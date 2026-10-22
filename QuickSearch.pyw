"""QuickSearch - fast, detailed file search for a large archive folder.

Double-click to run (pythonw). Standard library (tkinter + sqlite3); Pillow is optional
and only used for image thumbnails in the preview pane.

* First start indexes every file and folder under the root (default: the folder
  this script is in). The index lives in %LOCALAPPDATA%\\QuickSearch, so the
  archive itself is not touched. The index refreshes itself in the background
  (Auto-refresh setting, default Daily); "Rebuild index" refreshes it now.
* Matching ignores case and Turkish accents: "vinc" finds "Vinç", "dugun" finds "DÜĞÜN".
* Query syntax:  word1 word2 (all must match)   "exact phrase"   -exclude
                 wild*card / ?   ext:pdf,docx
* "README hints" shows lines from the README.md knowledge map that mention
  your terms; double-click one to search only inside that folder.
* Select results (Ctrl/Shift+click, Ctrl+A) and press Del to move them to the
  Recycle Bin after a confirmation.
* Preview pane (right of the results, "Preview" checkbox): image thumbnail with EXIF
  date, the start of text/code files, the first page of a PDF, folder contents.
* "Search all roots" combines several indexed folders (e.g. H:\\ and D:\\); "Roots…"
  adds / removes them. Merged results show absolute folders; Sort and Max results
  apply to the merged list. Auto-refresh also keeps the other roots' indexes fresh.
* "Find duplicates…" groups files with identical content (size, then BLAKE2b hash of
  the first 64 KB, then of the whole file) within the current filters, helps select
  the extra copies and sends them to the Recycle Bin - never the last copy.
"""

import calendar
import collections
import csv
import datetime
import hashlib
import json
import os
import queue
import re
import shutil
import sqlite3
import subprocess
import sys
import threading
import time
import unicodedata

import tkinter as tk
from tkinter import ttk, filedialog, messagebox

APP = "QuickSearch"
DATA_DIR = os.path.join(os.environ.get("LOCALAPPDATA") or os.path.expanduser("~"), APP)
SETTINGS_FILE = os.path.join(DATA_DIR, "settings.json")
SKIP_DIRS = {"$recycle.bin", "system volume information", "__pycache__", ".git"}
SKIP_FILES = {"thumbs.db", "desktop.ini"}
CREATE_NO_WINDOW = 0x08000000

TYPES = {
    "All files and folders": None,
    "Folders only": "<dir>",
    "Documents": "pdf doc docx odt rtf txt md djvu chm epub ps wri",
    "Spreadsheets": "xls xlsx xlsm csv ods",
    "Presentations": "ppt pptx pps ppsx odp",
    "Images": "jpg jpeg png gif bmp tif tiff cr2 nef psd svg ico webp heic",
    "Videos": "avi mp4 mov mkv wmv flv mpg mpeg 3gp m4v vob",
    "Audio": "mp3 wav wma ogg flac m4a aac mid midi",
    "Source code": "c h cpp hpp cc cs asm s inc a51 z80 mac bas bi vb vbp frm pas py java js php pl sh bat ino pjt mcp",
    "Web pages": "htm html mht mhtml php css js xml",
    "Archives": "zip rar 7z gz tgz tar bz2 iso cab arj lzh",
    "Programs": "exe msi com dll sys",
    "CAD / 3D": "sldprt sldasm slddrw stp step dxf dwg stl igs iges 3ds obj skp",
    "Emulator images": "dsk cdt cpr rom tap tzx sna",
}
TEXT_EXTS = set(("txt md c h cpp hpp cc cs asm s inc a51 z80 mac bas bi vb frm pas py java js php "
                 "pl sh bat ino pjt lst htm html xml csv ini cfg nfo diz json rtf tex log").split())
MAX_TEXT_BYTES = 8 * 1024 * 1024
MAX_CONTENT_CANDIDATES = 60000
# Auto-refresh: maximum index age in seconds (0 = rebuild at every start, None = never)
AUTO_OPTIONS = {"Off": None, "On every start": 0, "Every hour": 3600,
                "Every 6 hours": 6 * 3600, "Daily": 24 * 3600}
AUTO_TICK_MS = 5 * 60 * 1000  # how often a running window checks the index age

# ---------------------------------------------------------------- text folding
_TR = str.maketrans({"ı": "i", "ş": "s", "ğ": "g", "ç": "c", "ö": "o", "ü": "u",
                     "â": "a", "î": "i", "û": "u", "é": "e", "è": "e", "à": "a", "ñ": "n"})


def fold(s):
    """Lower-case and strip accents (Turkish aware) for matching."""
    s = s.replace("İ", "i").lower().translate(_TR)
    if s.isascii():
        return s
    s = unicodedata.normalize("NFKD", s)
    return "".join(c for c in s if not unicodedata.combining(c))


def fold_fast(s):
    """Length-preserving fold used for file contents (keeps snippet offsets aligned)."""
    return s.replace("İ", "i").lower().translate(_TR)


def like_escape(s):
    return s.replace("\\", "\\\\").replace("%", "\\%").replace("_", "\\_")


def like_pattern(term):
    """Substring LIKE pattern; * and ? act as wildcards."""
    return "%" + like_escape(term).replace("*", "%").replace("?", "_") + "%"


def parse_query(q):
    """Return (include_terms, exclude_terms, extensions) - terms already folded."""
    include, exclude, exts = [], [], []
    for neg, quoted, word in re.findall(r'(-?)(?:"([^"]*)"|(\S+))', q):
        raw = quoted if quoted else word
        if not quoted and raw.lower().startswith("ext:"):
            exts += [x.strip(". ").lower() for x in raw[4:].split(",") if x.strip(". ")]
            continue
        t = fold(raw).strip()
        if t:
            (exclude if neg else include).append(t)
    return include, exclude, exts


DATE_HELP = "use 2008, 06.2008 or 15.06.2008 (2008-06-15 also works)"


def parse_date(text, end=False):
    """Parse a year / month / day into a local timestamp.

    end=False -> start of that period; end=True -> start of the NEXT period (exclusive bound),
    so "to 2008-06" includes all of June. Accepts Y, Y-M, Y-M-D (any of - . / as separator)
    and the Turkish day-first forms M.Y and D.M.Y. Returns None for empty text."""
    t = (text or "").strip()
    if not t:
        return None
    parts = [p for p in re.split(r"[-./\s]+", t) if p]
    if not 1 <= len(parts) <= 3 or not all(p.isdigit() for p in parts):
        raise ValueError(f"unrecognised date '{t}' ({DATE_HELP})")
    n = [int(p) for p in parts]
    if len(parts[0]) == 4:
        y, m, d = (n + [None, None])[:3]
    elif len(parts) == 2:
        (m, y), d = n, None
    elif len(parts) == 3:
        d, m, y = n
    else:
        raise ValueError(f"unrecognised date '{t}' ({DATE_HELP})")
    try:
        if not 1900 <= y <= 2100:
            raise ValueError
        start = datetime.datetime(y, m or 1, d or 1)
    except (ValueError, TypeError):
        raise ValueError(f"invalid date '{t}' ({DATE_HELP})") from None
    if end:
        if d:
            start += datetime.timedelta(days=1)
        elif m:
            start = datetime.datetime(y + (m == 12), m % 12 + 1, 1)
        else:
            start = datetime.datetime(y + 1, 1, 1)
    return start.timestamp()


def date_preset(name, today=None):
    """Return (from_text, to_text) for a quick date preset."""
    today = today or datetime.date.today()
    day = lambda d: d.strftime("%d.%m.%Y")
    if name == "Today":
        return day(today), day(today)
    if name == "Last 7 days":
        return day(today - datetime.timedelta(days=6)), day(today)
    if name == "Last 30 days":
        return day(today - datetime.timedelta(days=29)), day(today)
    if name == "This month":
        s = today.strftime("%m.%Y")
        return s, s
    if name == "Last month":
        last = today.replace(day=1) - datetime.timedelta(days=1)
        s = last.strftime("%m.%Y")
        return s, s
    if name == "This year":
        return str(today.year), str(today.year)
    if name == "Last year":
        return str(today.year - 1), str(today.year - 1)
    return "", ""


DATE_FORMATS = {"31.12.2026 (EU)": "%d.%m.%Y %H:%M",
                "2026-12-31 (ISO)": "%Y-%m-%d %H:%M",
                "12/31/2026 (US)": "%m/%d/%Y %I:%M %p"}
DEFAULT_DATE_FORMAT = "31.12.2026 (EU)"


DATE_PRESETS = ["Any date", "Today", "Last 7 days", "Last 30 days", "This month", "Last month",
                "This year", "Last year", "Custom"]


def human_size(n):
    for unit in ("B", "KB", "MB", "GB"):
        if n < 1024 or unit == "GB":
            return f"{n:.0f} {unit}" if unit == "B" else f"{n:.1f} {unit}"
        n /= 1024.0


def find_pdftotext():
    p = shutil.which("pdftotext")
    if p:
        return p
    for c in (r"C:\Program Files\Git\mingw64\bin\pdftotext.exe",
              r"C:\Program Files (x86)\Git\mingw64\bin\pdftotext.exe",
              r"C:\Program Files\xpdf\pdftotext.exe"):
        if os.path.isfile(c):
            return c
    return None


# ---------------------------------------------------------------- deleting (Windows shell)
DRIVE_TYPES = {0: "unknown", 1: "invalid path", 2: "removable", 3: "fixed (local disk)",
               4: "network", 5: "CD/DVD", 6: "RAM disk"}
DRIVE_FIXED = 3
FO_DELETE = 0x0003
FOF_SILENT = 0x0004
FOF_NOCONFIRMATION = 0x0010
FOF_ALLOWUNDO = 0x0040
FOF_NOERRORUI = 0x0400
FOF_WANTNUKEWARNING = 0x4000  # Windows asks first if an item can't be recycled (e.g. too big)
_SH_ERRORS = {
    2: "not found", 3: "path not found", 5: "access denied (permission)",
    0x20: "file is in use by another program", 0x21: "file is locked by another program",
    0x71: "source and destination are the same", 0x74: "root folder cannot be deleted",
    0x75: "cancelled", 0x78: "access denied (permission)", 0x79: "path too long",
    0x7C: "invalid path / name", 0x402: "unknown error (maybe in use or path too long)",
    0x10000: "error on destination",
}

try:
    import ctypes
    from ctypes import wintypes

    class SHFILEOPSTRUCTW(ctypes.Structure):
        # shellapi.h packs this struct to 1 byte only on 32-bit Windows; 64-bit uses natural alignment.
        if ctypes.sizeof(ctypes.c_void_p) == 4:
            _pack_ = 1
        _fields_ = [("hwnd", wintypes.HWND),
                    ("wFunc", wintypes.UINT),
                    ("pFrom", ctypes.c_void_p),           # LPCWSTR, double-NUL terminated list
                    ("pTo", ctypes.c_void_p),             # LPCWSTR
                    ("fFlags", wintypes.WORD),            # FILEOP_FLAGS
                    ("fAnyOperationsAborted", wintypes.BOOL),
                    ("hNameMappings", wintypes.LPVOID),
                    ("lpszProgressTitle", ctypes.c_void_p)]  # LPCWSTR
except (ImportError, AttributeError):  # not Windows
    ctypes = None


def drive_type(path):
    """kernel32 GetDriveTypeW for the drive that holds path (0 = unknown)."""
    if ctypes is None:
        return 0
    drive = os.path.splitdrive(os.path.abspath(path))[0]
    if not drive:
        return 0
    try:
        return int(ctypes.windll.kernel32.GetDriveTypeW(ctypes.c_wchar_p(drive.rstrip("\\/") + "\\")))
    except (AttributeError, OSError):
        return 0


def shell_recycle(paths, hwnd=0, nuke_warning=True):
    """Send paths to the Recycle Bin with SHFileOperationW. Returns (return_code, aborted).

    On drives without a Recycle Bin (removable / network) Windows deletes permanently instead.
    """
    if ctypes is None:
        return -1, False
    paths = [os.path.abspath(p) for p in paths if p and "\0" not in p]
    if not paths:
        return 0, False
    buf = ctypes.create_unicode_buffer("\0".join(paths) + "\0\0")
    op = SHFILEOPSTRUCTW()
    op.hwnd = hwnd or None
    op.wFunc = FO_DELETE
    op.pFrom = ctypes.addressof(buf)
    op.pTo = None
    op.fFlags = (FOF_ALLOWUNDO | FOF_NOCONFIRMATION | FOF_SILENT | FOF_NOERRORUI
                 | (FOF_WANTNUKEWARNING if nuke_warning else 0))
    fn = ctypes.windll.shell32.SHFileOperationW
    fn.argtypes = [ctypes.POINTER(SHFILEOPSTRUCTW)]
    fn.restype = ctypes.c_int
    rc = fn(ctypes.byref(op))
    return rc, bool(op.fAnyOperationsAborted)


def sh_error_text(rc):
    return _SH_ERRORS.get(rc, "error code 0x%X" % rc)


# ---------------------------------------------------------------- indexing
def db_path_for(root):
    key = os.path.normcase(os.path.abspath(root)).encode("utf-8")
    return os.path.join(DATA_DIR, "index_%s.sqlite" % hashlib.md5(key).hexdigest()[:12])


def _walk(root, include_system=False):
    skip_dirs = set() if include_system else SKIP_DIRS
    skip_files = set() if include_system else SKIP_FILES
    stack = [root]
    while stack:
        d = stack.pop()
        try:
            it = os.scandir(d)
        except OSError:
            continue
        with it:
            for e in it:
                try:
                    if e.is_dir(follow_symlinks=False):
                        if e.name.lower() in skip_dirs:
                            continue
                        stack.append(e.path)
                        yield e.path, e.name, True, 0, e.stat(follow_symlinks=False).st_mtime
                    else:
                        if e.name.lower() in skip_files:
                            continue
                        st = e.stat(follow_symlinks=False)
                        yield e.path, e.name, False, st.st_size, st.st_mtime
                except OSError:
                    continue


def build_index(root, db_path, progress=None, cancel=None, include_system=False):
    """Walk root and write a fresh index. Returns item count, or None if cancelled.

    include_system=True also indexes $RECYCLE.BIN, System Volume Information, .git,
    __pycache__, Thumbs.db and desktop.ini (folders Windows denies access to are skipped)."""
    os.makedirs(os.path.dirname(db_path), exist_ok=True)
    root = os.path.abspath(root)
    cut = len(root) if root.endswith(os.sep) else len(root) + 1
    tmp = db_path + ".building"
    if os.path.exists(tmp):
        os.remove(tmp)
    con = sqlite3.connect(tmp)
    con.executescript("""PRAGMA journal_mode=OFF; PRAGMA synchronous=OFF;
        CREATE TABLE files(rel TEXT, name TEXT, ext TEXT, size INTEGER, mtime REAL,
                           isdir INTEGER, fname TEXT, fpath TEXT);
        CREATE TABLE meta(k TEXT PRIMARY KEY, v TEXT);""")
    n, batch, last = 0, [], 0.0
    ins = "INSERT INTO files VALUES (?,?,?,?,?,?,?,?)"
    for path, name, isdir, size, mtime in _walk(root, include_system):
        if cancel is not None and cancel.is_set():
            con.close()
            os.remove(tmp)
            return None
        rel = path[cut:]
        ext = "" if isdir else os.path.splitext(name)[1][1:].lower()
        batch.append((rel, name, ext, size, mtime, 1 if isdir else 0, fold(name), fold(rel)))
        n += 1
        if len(batch) >= 5000:
            con.executemany(ins, batch)
            batch.clear()
        if progress and time.time() - last > 0.3:
            last = time.time()
            progress(n, os.path.dirname(rel))
    con.executemany(ins, batch)
    con.executemany("INSERT INTO meta VALUES (?,?)",
                    [("root", root), ("built", str(time.time())), ("count", str(n)),
                     ("system", "1" if include_system else "0")])
    con.commit()
    con.close()
    for _ in range(20):  # the old index may be open by a running search for a moment
        try:
            os.replace(tmp, db_path)
            break
        except PermissionError:
            time.sleep(0.25)
    else:
        raise RuntimeError("Could not replace the old index file (in use).")
    return n


def index_info(db_path):
    if not os.path.isfile(db_path):
        return None
    try:
        con = sqlite3.connect(db_path)
        meta = dict(con.execute("SELECT k, v FROM meta"))
        con.close()
        return meta
    except sqlite3.Error:
        return None


# ---------------------------------------------------------------- searching
def _connect(db_path):
    con = sqlite3.connect(db_path)
    cache = {}

    def regexp(pattern, value):
        r = cache.get(pattern)
        if r is None:
            r = cache[pattern] = re.compile(pattern, re.I)
        return value is not None and r.search(value) is not None

    con.create_function("REGEXP", 2, regexp, deterministic=True)
    return con


def filter_clauses(o, exts_from_query, restrict_exts=None):
    """WHERE clauses for type / folder / size / date filters."""
    where, params = [], []
    tdef = TYPES.get(o.get("type"))
    exts = None
    if tdef == "<dir>":
        where.append("isdir = 1")
    elif tdef:
        exts = set(tdef.split())
    if exts_from_query:
        exts = set(exts_from_query) if exts is None else exts & set(exts_from_query)
    if restrict_exts is not None:
        exts = set(restrict_exts) if exts is None else exts & set(restrict_exts)
    if exts is not None:
        if not exts:
            where.append("0")
        else:
            where.append("isdir = 0 AND ext IN (%s)" % ",".join("?" * len(exts)))
            params += sorted(exts)
    scope = (o.get("scope") or "").strip().strip("\\/")
    if scope:
        fs = fold(scope.replace("/", "\\"))
        where.append("(fpath = ? OR fpath LIKE ? ESCAPE '\\')")
        params += [fs, like_escape(fs + "\\") + "%"]
    if o.get("min_mb") not in (None, ""):
        where.append("size >= ?")
        params.append(int(float(o["min_mb"]) * 1048576))
    if o.get("max_mb") not in (None, ""):
        where.append("size <= ?")
        params.append(int(float(o["max_mb"]) * 1048576))
    start = parse_date(o.get("date_from") or o.get("year_from"))
    if start is not None:
        where.append("mtime >= ?")
        params.append(start)
    stop = parse_date(o.get("date_to") or o.get("year_to"), end=True)
    if stop is not None:
        where.append("mtime < ?")
        params.append(stop)
    return where, params


def search_names(db_path, o, want_total=False):
    """Name / path search. Returns list of (rel, name, ext, size, mtime, isdir, snippet);
    with want_total=True returns (rows, total_matches)."""
    q = o.get("query", "")
    col = "fname" if o.get("field") == "name" else "fpath"
    where, params, select_params = [], [], []
    score = "0"
    if o.get("regex"):
        exts = []
        if q.strip():
            where.append(("name" if col == "fname" else "rel") + " REGEXP ?")
            params.append(q.strip())
    else:
        include, exclude, exts = parse_query(q)
        for t in include:
            where.append(f"{col} LIKE ? ESCAPE '\\'")
            params.append(like_pattern(t))
        for t in exclude:
            where.append(f"{col} NOT LIKE ? ESCAPE '\\'")
            params.append(like_pattern(t))
        if include:
            score = "+".join(["(fname LIKE ? ESCAPE '\\')"] * len(include))
            select_params = [like_pattern(t) for t in include]
    fw, fp = filter_clauses(o, exts)
    where += fw
    params += fp
    where_sql = " WHERE " + " AND ".join(where) if where else ""
    order = SORTS.get(o.get("sort") or "Best match")
    if order:
        order_sql = f" ORDER BY {order}, length(rel)"
    elif score != "0":
        order_sql = " ORDER BY score DESC, isdir DESC, length(rel)"
    else:
        order_sql = " ORDER BY mtime DESC"
    limit = int(o.get("limit") or 2000)
    sql = f"SELECT rel, name, ext, size, mtime, isdir, ({score}) AS score FROM files{where_sql}{order_sql} LIMIT ?"
    con = _connect(db_path)
    try:
        rows = con.execute(sql, select_params + params + [limit]).fetchall()
        total = len(rows)
        if want_total and total >= limit:
            total = con.execute(f"SELECT COUNT(*) FROM files{where_sql}", params).fetchone()[0]
    finally:
        con.close()
    rows = [(r[0], r[1], r[2], r[3], r[4], r[5], "") for r in rows]
    return (rows, total) if want_total else rows


def _read_text(full, ext, pdftotext):
    if ext == "pdf":
        try:
            r = subprocess.run([pdftotext, "-q", "-enc", "UTF-8", full, "-"], capture_output=True,
                               timeout=30, creationflags=CREATE_NO_WINDOW)
            return r.stdout.decode("utf-8", "replace")
        except (OSError, subprocess.SubprocessError):
            return ""
    try:
        with open(full, "rb") as f:
            data = f.read(MAX_TEXT_BYTES)
    except OSError:
        return ""
    if data.startswith((b"\xff\xfe", b"\xfe\xff")):
        return data.decode("utf-16", "replace")
    try:
        return data.decode("utf-8")
    except UnicodeDecodeError:
        return data.decode("cp1254", "replace")  # Turkish Windows code page


def search_contents(db_path, root, o, pdftotext, cancel, emit, progress):
    """Search inside text/code (and optionally PDF) files. Calls emit(rows) in batches."""
    include, exclude, exts = parse_query(o.get("query", ""))
    if o.get("regex"):
        rx = re.compile(o.get("query", ""), re.I)
        include, exclude = [], []
    elif not include:
        return 0, 0, "Type at least one word to look for inside files."
    allowed = set(TEXT_EXTS)
    if o.get("pdf") and pdftotext:
        allowed.add("pdf")
    where, params = filter_clauses(o, exts, restrict_exts=allowed)
    where.append("isdir = 0")
    where.append("size <= ?")
    params.append(MAX_TEXT_BYTES if not o.get("pdf") else 200 * 1048576)
    con = _connect(db_path)
    try:
        cands = con.execute("SELECT rel, name, ext, size, mtime FROM files WHERE " + " AND ".join(where)
                            + " ORDER BY mtime DESC LIMIT ?", params + [MAX_CONTENT_CANDIDATES]).fetchall()
    finally:
        con.close()
    limit = int(o.get("limit") or 2000)
    found, batch, last = 0, [], 0.0
    for i, (rel, name, ext, size, mtime) in enumerate(cands, 1):
        if cancel.is_set():
            break
        if time.time() - last > 0.3:
            last = time.time()
            progress(f"Searching inside files… {i:,}/{len(cands):,} checked, {found:,} found")
        text = _read_text(os.path.join(root, rel), ext, pdftotext)
        if not text:
            continue
        if o.get("regex"):
            m = rx.search(text)
            if not m:
                continue
            pos, ln = m.start(), max(1, m.end() - m.start())
        else:
            ft = fold_fast(text)
            if any(t not in ft for t in include) or any(t in ft for t in exclude):
                continue
            pos, ln = ft.find(include[0]), len(include[0])
        a = max(0, pos - 50)
        snippet = re.sub(r"\s+", " ", text[a:pos + ln + 70]).strip()
        batch.append((rel, name, ext, size, mtime, 0, snippet))
        found += 1
        if len(batch) >= 50:
            emit(batch)
            batch = []
        if found >= limit:
            break
    if batch:
        emit(batch)
    note = " (candidate list capped)" if len(cands) >= MAX_CONTENT_CANDIDATES else ""
    return found, len(cands), note


# ---------------------------------------------------------------- several roots
def indexed_roots():
    """Root folders that have an index in DATA_DIR (read from each index's meta table)."""
    out = []
    try:
        names = sorted(os.listdir(DATA_DIR))
    except OSError:
        return out
    for n in names:
        if re.fullmatch(r"index_[0-9a-f]{12}\.sqlite", n):
            info = index_info(os.path.join(DATA_DIR, n))
            if info and info.get("root"):
                out.append(info["root"])
    return out


def path_in(path, folder):
    """True if path is folder itself or lies inside it (case-insensitive, Windows style)."""
    p = os.path.normcase(os.path.abspath(path))
    f = os.path.normcase(os.path.abspath(folder))
    return p == f or p.startswith(f.rstrip("\\/") + os.sep)


def rel_to(path, folder):
    """path relative to folder ('' for the folder itself); path must be inside folder."""
    p, f = os.path.abspath(path), os.path.abspath(folder).rstrip("\\/")
    return "" if os.path.normcase(p) == os.path.normcase(os.path.abspath(folder)) else p[len(f) + 1:]


def merge_sort_key(o):
    """Python sort key (row, relative_rel_length) that reproduces search_names' SQL order,
    so per-root top-N lists can be merged into a correct overall top-N."""
    order = SORTS.get(o.get("sort") or "Best match")
    keys = {"mtime DESC": lambda r, n: (-(r[4] or 0), n), "mtime ASC": lambda r, n: (r[4] or 0, n),
            "fname ASC": lambda r, n: (fold(r[1]), n), "size DESC": lambda r, n: (-(r[3] or 0), n),
            "size ASC": lambda r, n: (r[3] or 0, n), "fpath ASC": lambda r, n: (fold(r[0]), n)}
    if order in keys:
        return keys[order]
    include = [] if o.get("regex") else parse_query(o.get("query", ""))[0]
    if include and o.get("field") != "content":
        rxs = [re.compile(re.escape(t).replace(r"\*", ".*").replace(r"\?", ".")) for t in include]
        return lambda r, n: (-sum(1 for x in rxs if x.search(fold(r[1]))), -r[5], n)
    return lambda r, n: (-(r[4] or 0), n)


def search_names_multi(targets, o):
    """search_names over several (root, db, scope) targets; rows get rel = ABSOLUTE path.
    Returns (rows, total_matches) with Sort and Max results applied to the merged list."""
    limit = int(o.get("limit") or 2000)
    merged, total = [], 0
    for root, db, scope in targets:
        rows, t = search_names(db, dict(o, scope=scope), want_total=True)
        total += t
        merged += [((os.path.join(root, r[0]),) + tuple(r[1:]), len(r[0])) for r in rows]
    key = merge_sort_key(o)
    merged.sort(key=lambda x: key(x[0], x[1]))
    return [r for r, _ in merged[:limit]], total


# ---------------------------------------------------------------- duplicates
HEAD_BYTES = 64 * 1024
CHUNK = 1024 * 1024


def _hash_file(path, size, mode, cancel, on_read):
    """BLAKE2b of a file: mode 'head' = first 64 KB, 'quick' = first + last 1 MB, 'full'.
    on_read(n) is called with the number of bytes read. Returns digest or None if cancelled."""
    h = hashlib.blake2b(digest_size=32)
    with open(path, "rb") as f:
        if mode == "head":
            data = f.read(HEAD_BYTES)
            on_read(len(data))
            h.update(data)
        elif mode == "quick":
            data = f.read(CHUNK)
            on_read(len(data))
            h.update(data)
            if size > CHUNK:
                f.seek(max(CHUNK, size - CHUNK))
                data = f.read(CHUNK)
                on_read(len(data))
                h.update(data)
        else:
            while True:
                if cancel.is_set():
                    return None
                data = f.read(CHUNK)
                if not data:
                    break
                on_read(len(data))
                h.update(data)
    return h.digest()


def find_duplicates(targets, o, min_bytes, quick, cancel, progress):
    """Find files with identical content.

    targets: [(root, db, relative_scope)], o: search options (Type / size / date filters are
    used, the query is not). progress(text, fraction) is called from this (worker) thread.
    Returns (groups, stats); groups = [(size, [(path, mtime), ...]), ...] sorted by wasted space."""
    stats = collections.Counter()
    min_bytes = max(1, int(min_bytes))
    progress("Reading the index…", 0)
    parts = []
    for root, db, scope in targets:
        where, params = filter_clauses(dict(o, scope=scope), None)
        parts.append((root, db, " AND ".join(["isdir = 0", "size >= ?"] + where), [min_bytes] + params))
    con = sqlite3.connect(":memory:")
    cands = []
    try:
        con.execute("CREATE TEMP TABLE allsizes(size INTEGER)")
        for i, (root, db, w, p) in enumerate(parts):  # sizes of every root, then GROUP BY across roots
            con.execute("ATTACH DATABASE ? AS src", (db,))
            try:
                con.execute(f"INSERT INTO allsizes SELECT size FROM src.files WHERE {w}", p)
            finally:
                con.commit()
                con.execute("DETACH DATABASE src")
        con.execute("CREATE TEMP TABLE cs AS SELECT size FROM allsizes GROUP BY size HAVING COUNT(*) > 1")
        con.execute("CREATE INDEX temp.cs_size ON cs(size)")
        for root, db, w, p in parts:
            con.execute("ATTACH DATABASE ? AS src", (db,))
            try:
                cands += [(os.path.join(root, rel), size) for rel, size in con.execute(
                    f"SELECT rel, size FROM src.files WHERE {w} AND size IN (SELECT size FROM cs)", p)]
            finally:
                con.commit()
                con.execute("DETACH DATABASE src")
    finally:
        con.close()
    stats["candidates"] = len(cands)

    # check the files still exist and have the indexed size (nested roots list a file twice)
    seen, by_size = set(), collections.defaultdict(list)
    last = 0.0
    for i, (path, size) in enumerate(cands, 1):
        if cancel.is_set():
            return None, stats
        if time.time() - last > 0.3:
            last = time.time()
            progress(f"Checking files on disk… {i:,}/{len(cands):,}", i / max(1, len(cands)) * 0.05)
        k = os.path.normcase(os.path.normpath(path))
        if k in seen:
            continue
        seen.add(k)
        try:
            st = os.stat(path)
        except OSError:
            stats["missing"] += 1
            continue
        if st.st_size != size:
            stats["changed"] += 1
            continue
        by_size[size].append((path, st.st_mtime))
    groups = [(s, fs) for s, fs in by_size.items() if len(fs) > 1]

    read = [0]

    def on_read(n):
        read[0] += n

    def split(groups, mode, step):
        n = sum(len(fs) for _, fs in groups)
        out, i, last = [], 0, 0.0
        for size, files in groups:
            by_hash = collections.defaultdict(list)
            for path, mtime in files:
                if cancel.is_set():
                    return None
                i += 1
                if time.time() - last > 0.25:
                    last = time.time()
                    progress(f"Hashing {i:,}/{n:,} files · {human_size(read[0])} read  ({step})",
                             0.05 + 0.95 * i / max(1, n))
                try:
                    d = _hash_file(path, size, mode, cancel, on_read)
                except OSError:
                    stats["errors"] += 1
                    continue
                if d is None:
                    return None
                by_hash[d].append((path, mtime))
            out += [(size, fs) for fs in by_hash.values() if len(fs) > 1]
        return out

    groups = split(groups, "head", "step 1 of 2: first 64 KB")
    if groups is None:
        return None, stats
    small = [g for g in groups if g[0] <= HEAD_BYTES]  # the first 64 KB were the whole file
    big = [g for g in groups if g[0] > HEAD_BYTES]
    big = split(big, "quick" if quick else "full",
                "step 2 of 2: " + ("first + last 1 MB" if quick else "whole files"))
    if big is None:
        return None, stats
    groups = [(s, sorted(fs, key=lambda x: x[0].lower())) for s, fs in small + big]
    groups.sort(key=lambda g: (-g[0] * (len(g[1]) - 1), g[1][0][0].lower()))
    stats["read"] = read[0]
    progress("Done.", 1.0)
    return groups, stats


# ---------------------------------------------------------------- preview
IMAGE_EXTS = set("jpg jpeg png gif bmp tif tiff webp ico heic heif".split())
PREVIEW_TEXT_EXTS = TEXT_EXTS | {"md", "csv", "json", "xml", "ini", "log"}
PREVIEW_TEXT_BYTES = 64 * 1024
PREVIEW_TEXT_LINES = 300
PREVIEW_IMAGE_MAX_BYTES = 256 * 1048576
PREVIEW_DIR_ENTRIES = 50
_PIL = None


def pil_modules():
    """(Image, ImageOps, ImageTk) from Pillow, or None when Pillow is not installed."""
    global _PIL
    if _PIL is None:
        try:
            from PIL import Image, ImageOps, ImageTk
            _PIL = (Image, ImageOps, ImageTk)
        except Exception:  # ImportError or a broken install
            _PIL = False
    return _PIL or None


def decode_text(data, truncated=False):
    """Decode like _read_text (UTF-16 BOM / UTF-8 / cp1254); tolerate a cut last character."""
    if data.startswith((b"\xff\xfe", b"\xfe\xff")):
        if truncated and len(data) % 2:
            data = data[:-1]
        return data.decode("utf-16", "replace")
    try:
        text = data.decode("utf-8")
    except UnicodeDecodeError as ex:
        text = None
        if truncated and ex.end >= len(data) - 1:  # the read limit cut a multi-byte character
            try:
                text = data[:ex.start].decode("utf-8")
            except UnicodeDecodeError:
                pass
        if text is None:
            text = data.decode("cp1254", "replace")  # Turkish Windows code page
    return text.lstrip("﻿")


def _exif_taken(im):
    """EXIF DateTimeOriginal (or DateTime) as a timestamp, or None."""
    try:
        ex = im.getexif()
    except Exception:
        return None
    v = None
    try:
        v = ex.get_ifd(0x8769).get(36867)
    except Exception:
        pass
    v = v or ex.get(36867) or ex.get(306)
    if not isinstance(v, str):
        return None
    try:
        return datetime.datetime.strptime(v.strip("\x00 ")[:19], "%Y:%m:%d %H:%M:%S").timestamp()
    except (ValueError, OverflowError, OSError):
        return None


def build_preview(path, isdir, ext, size, box, pdftotext):
    """Compute preview content (runs in a worker thread). Returns a dict:
    kind 'image' (image = PIL image fitted in box) / 'text' / 'info', text, extra (list of str),
    taken (EXIF timestamp or None)."""
    res = {"kind": "info", "text": "", "extra": [], "image": None, "taken": None}
    try:
        if isdir:
            if not os.path.isdir(path):
                res["text"] = "This folder no longer exists on disk."
                return res
            entries, n_dirs, n_files, more = [], 0, 0, False
            with os.scandir(path) as it:
                for e in it:
                    try:
                        d = e.is_dir(follow_symlinks=False)
                    except OSError:
                        d = False
                    n_dirs += d
                    n_files += not d
                    if len(entries) < 20000:
                        entries.append((not d, e.name.lower(), e))
                    if n_dirs + n_files >= 200000:
                        more = True
                        break
            entries.sort(key=lambda x: (x[0], x[1]))
            lines = []
            for isfile, _, e in entries[:PREVIEW_DIR_ENTRIES]:
                if not isfile:
                    lines.append("📁 " + e.name)
                else:
                    try:
                        sz = human_size(e.stat(follow_symlinks=False).st_size)
                    except OSError:
                        sz = "?"
                    lines.append(f"   {e.name}   ({sz})")
            plus = "+" if more else ""
            head = f"{n_dirs:,}{plus} folder(s), {n_files:,}{plus} file(s)"
            if n_dirs + n_files > PREVIEW_DIR_ENTRIES:
                head += f" - first {PREVIEW_DIR_ENTRIES} shown"
            res.update(kind="text", text=head + "\n\n" + ("\n".join(lines) or "(empty folder)"))
            return res
        if not os.path.isfile(path):
            res["text"] = "This file no longer exists on disk."
            return res
        if ext in IMAGE_EXTS:
            pil = pil_modules()
            if not pil:
                res["text"] = "Install Pillow (pip install pillow) to see image thumbnails."
                return res
            if size > PREVIEW_IMAGE_MAX_BYTES:
                res["text"] = f"Image is too large to preview ({human_size(size)})."
                return res
            Image, ImageOps, _ = pil
            try:
                with Image.open(path) as im:
                    res["extra"].append(f"{im.size[0]:,} × {im.size[1]:,} px · {im.format or ext.upper()}")
                    res["taken"] = _exif_taken(im)
                    try:
                        im.draft("RGB", box)  # fast JPEG downscaling while decoding
                    except Exception:
                        pass
                    im2 = ImageOps.exif_transpose(im)
                    im2.thumbnail(box)
                    im2 = im2.convert("RGBA" if im2.mode in ("RGBA", "LA", "P", "PA") else "RGB")
                    im2.load()
                res.update(kind="image", image=im2)
            except Exception as ex:
                res["text"] = f"Pillow cannot show this image ({type(ex).__name__}: {ex})."
            return res
        if ext in PREVIEW_TEXT_EXTS:
            with open(path, "rb") as f:
                data = f.read(PREVIEW_TEXT_BYTES + 1)
            cut = len(data) > PREVIEW_TEXT_BYTES
            text = decode_text(data[:PREVIEW_TEXT_BYTES], truncated=cut).replace("\x00", "")
            lines = text.splitlines()
            if len(lines) > PREVIEW_TEXT_LINES:
                lines, cut = lines[:PREVIEW_TEXT_LINES], True
            if cut:
                res["extra"].append(f"Beginning of the file shown (max {PREVIEW_TEXT_LINES} lines / 64 KB)")
            res.update(kind="text", text="\n".join(lines) if lines else "(empty file)")
            return res
        if ext == "pdf":
            if not pdftotext:
                res["text"] = "PDF text needs pdftotext (comes with Git for Windows)."
                return res
            try:
                r = subprocess.run([pdftotext, "-q", "-l", "1", "-enc", "UTF-8", path, "-"],
                                   capture_output=True, timeout=15, creationflags=CREATE_NO_WINDOW)
                text = decode_text(r.stdout[:PREVIEW_TEXT_BYTES], truncated=len(r.stdout) > PREVIEW_TEXT_BYTES)
            except subprocess.TimeoutExpired:
                res["text"] = "pdftotext took too long (over 15 s)."
                return res
            text = text.replace("\x00", "").replace("\f", "").strip()
            if not text:
                res["text"] = "This PDF has no text layer on page 1 (scanned PDF?)."
            else:
                res["extra"].append("Text of page 1")
                res.update(kind="text", text=text)
            return res
        res["text"] = f"No preview for .{ext} files." if ext else "No preview for this file type."
    except Exception as ex:  # unreadable / locked / anything else - never crash the UI
        res.update(kind="info", image=None, text=f"Cannot preview: {ex}")
    return res


# ---------------------------------------------------------------- GUI
class CalendarPopup(tk.Toplevel):
    """Small month calendar under a date entry. Click a day (or 'Whole month') to fill the entry."""

    def __init__(self, master, anchor, var, on_pick):
        super().__init__(master)
        self.var, self.on_pick = var, on_pick
        self.title("Pick a date")
        self.resizable(False, False)
        self.transient(master)
        try:
            self.attributes("-toolwindow", True)
        except tk.TclError:
            pass
        self.today = datetime.date.today()
        self.selected = None
        try:
            ts = parse_date(var.get())
            if ts is not None:
                self.selected = datetime.date.fromtimestamp(ts)
        except ValueError:
            pass
        base = self.selected or self.today
        self.year, self.month = base.year, base.month
        st = ttk.Style(self)
        st.configure("CalToday.TButton", foreground="#1a5fb4")
        st.configure("CalSel.TButton", font=("Segoe UI", 9, "bold"), foreground="#c01c28")

        head = ttk.Frame(self, padding=(6, 6, 6, 2))
        head.pack(fill="x")
        for txt, dy, dm in (("«", -1, 0), ("‹", 0, -1)):
            ttk.Button(head, text=txt, width=3, command=lambda dy=dy, dm=dm: self._shift(dy, dm)).pack(side="left")
        for txt, dy, dm in (("»", 1, 0), ("›", 0, 1)):
            ttk.Button(head, text=txt, width=3, command=lambda dy=dy, dm=dm: self._shift(dy, dm)).pack(side="right")
        self.v_title = tk.StringVar()
        ttk.Label(head, textvariable=self.v_title, anchor="center", font=("Segoe UI", 10, "bold")
                  ).pack(side="left", fill="x", expand=True)
        self.grid_frame = ttk.Frame(self, padding=(6, 2))
        self.grid_frame.pack()
        foot = ttk.Frame(self, padding=(6, 4, 6, 6))
        foot.pack(fill="x")
        ttk.Button(foot, text="Today", command=lambda: self._pick(self.today)).pack(side="left")
        ttk.Button(foot, text="Whole month", command=self._pick_month).pack(side="left", padx=4)
        ttk.Button(foot, text="Clear", command=lambda: self._finish("")).pack(side="left")
        ttk.Button(foot, text="Close", command=self.destroy).pack(side="right")
        self.bind("<Escape>", lambda e: self.destroy())
        self._draw()
        self.update_idletasks()
        x = anchor.winfo_rootx()
        y = anchor.winfo_rooty() + anchor.winfo_height() + 2
        self.geometry(f"+{x}+{y}")
        self.grab_set()
        self.focus_set()

    def _shift(self, dy, dm):
        m = self.month + dm
        y = self.year + dy + (m - 1) // 12
        self.year, self.month = y, (m - 1) % 12 + 1
        self._draw()

    def _draw(self):
        for w in self.grid_frame.winfo_children():
            w.destroy()
        self.v_title.set(f"{calendar.month_name[self.month]} {self.year}")
        for c, name in enumerate(("Mo", "Tu", "We", "Th", "Fr", "Sa", "Su")):
            ttk.Label(self.grid_frame, text=name, anchor="center", width=4,
                      foreground="#c01c28" if c >= 5 else "#444").grid(row=0, column=c, pady=(0, 2))
        weeks = calendar.Calendar(firstweekday=0).monthdayscalendar(self.year, self.month)
        for r, week in enumerate(weeks, 1):
            for c, day in enumerate(week):
                if not day:
                    continue
                d = datetime.date(self.year, self.month, day)
                style = ("CalSel.TButton" if d == self.selected else
                         "CalToday.TButton" if d == self.today else "TButton")
                ttk.Button(self.grid_frame, text=str(day), width=4, style=style,
                           command=lambda d=d: self._pick(d)).grid(row=r, column=c, padx=1, pady=1)

    def _pick(self, d):
        self._finish(d.strftime("%d.%m.%Y"))

    def _pick_month(self):
        self._finish(f"{self.month:02d}.{self.year}")

    def _finish(self, text):
        self.var.set(text)
        self.destroy()
        self.on_pick()


SORTS = {"Best match": None, "Newest first": "mtime DESC", "Oldest first": "mtime ASC",
         "Name A–Z": "fname ASC", "Largest first": "size DESC", "Smallest first": "size ASC",
         "Folder path": "fpath ASC"}


class RootsDialog(tk.Toplevel):
    """Add / remove the folders that 'Search all roots' combines."""

    def __init__(self, app):
        super().__init__(app)
        self.app = app
        self.title(APP + " - roots")
        self.geometry("760x330")
        self.minsize(520, 240)
        self.transient(app)
        ttk.Label(self, padding=(8, 8, 8, 4), wraplength=740, text=(
            "Folders searched together when 'Search all roots' is ticked (the current root is always "
            "included). Adding a folder builds its index in the background; removing one keeps its index file.")
                  ).pack(fill="x")
        mid = ttk.Frame(self, padding=(8, 0))
        mid.pack(fill="both", expand=True)
        self.lb = tk.Listbox(mid, selectmode="extended", font=("Segoe UI", 9), activestyle="none")
        sb = ttk.Scrollbar(mid, orient="vertical", command=self.lb.yview)
        self.lb.configure(yscrollcommand=sb.set)
        self.lb.pack(side="left", fill="both", expand=True)
        sb.pack(side="right", fill="y")
        bar = ttk.Frame(self, padding=8)
        bar.pack(fill="x")
        ttk.Button(bar, text="Add…", command=self.add).pack(side="left")
        ttk.Button(bar, text="Remove", command=self.remove).pack(side="left", padx=4)
        ttk.Button(bar, text="Rebuild index of selected", command=self.rebuild).pack(side="left")
        ttk.Button(bar, text="Close", command=self.destroy).pack(side="right")
        self.bind("<Escape>", lambda e: self.destroy())
        self.items = []
        self.refresh()

    def refresh(self):
        self.items = self.app._all_roots()
        self.lb.delete(0, "end")
        busy = self.app.indexing and os.path.normcase(self.app.index_root)
        for i, r in enumerate(self.items):
            info = index_info(db_path_for(r))
            if busy == os.path.normcase(r):
                desc = "indexing…"
            elif info is None:
                desc = "not indexed" + (" (queued)" if any(os.path.normcase(q) == os.path.normcase(r)
                                                           for q in self.app.index_queue) else "")
            else:
                desc = (f"{int(info.get('count', 0)):,} items · indexed "
                        f"{self.app.fmt_time(float(info.get('built', 0)))}")
            if not os.path.isdir(r):
                desc += " · OFFLINE"
            self.lb.insert("end", f"{r}    —    {desc}" + ("    (current root)" if i == 0 else ""))

    def add(self):
        d = filedialog.askdirectory(parent=self, title="Add a root folder")
        if not d:
            return
        d = os.path.abspath(d)
        if any(os.path.normcase(d) == os.path.normcase(r) for r in self.items):
            messagebox.showinfo(APP, "That folder is already in the list.", parent=self)
            return
        self.app.roots.append(d)
        self.app._roots_changed()
        if index_info(db_path_for(d)) is None:
            self.app.rebuild_index(root=d)  # queued if another index is being built
        self.refresh()

    def remove(self):
        sel = [self.items[i] for i in self.lb.curselection()]
        if not sel:
            return
        cur = os.path.normcase(self.app.root_dir)
        if any(os.path.normcase(r) == cur for r in sel):
            messagebox.showinfo(APP, "The current root cannot be removed (use 'Change root…' first).", parent=self)
        drop = {os.path.normcase(r) for r in sel} - {cur}
        self.app.roots = [r for r in self.app.roots if os.path.normcase(os.path.abspath(r)) not in drop]
        self.app._roots_changed()
        self.refresh()

    def rebuild(self):
        for i in self.lb.curselection():
            r = self.items[i]
            if os.path.isdir(r):
                self.app.rebuild_index(root=r)
        self.refresh()


class DupWindow(tk.Toplevel):
    """Duplicate finder: groups of identical files, selection helpers, safe delete."""

    def __init__(self, app):
        super().__init__(app)
        self.app = app
        self.title(APP + " - find duplicates")
        self.geometry("1100x650")
        self.minsize(860, 420)
        self.q = queue.Queue()
        self.cancel = threading.Event()
        self.gen = 0
        self.running = False
        self.groups = {}   # group iid -> {"size": bytes, "files": [child iids]}
        self.child = {}    # child iid -> (path, size, mtime, group iid)
        s = app.settings

        top = ttk.Frame(self, padding=(8, 8, 8, 2))
        top.pack(fill="x")
        ttk.Label(top, text="Minimum size").pack(side="left")
        self.v_min = tk.StringVar(value=str(s.get("dup_min_kb", 1)))
        e = ttk.Entry(top, textvariable=self.v_min, width=8)
        e.pack(side="left", padx=(4, 2))
        e.bind("<Return>", lambda ev: self.start())
        ttk.Label(top, text="KB").pack(side="left", padx=(0, 14))
        self.v_quick = tk.BooleanVar(value=bool(s.get("dup_quick", False)))
        ttk.Checkbutton(top, text="Quick mode (size + first/last 1 MB only)", variable=self.v_quick
                        ).pack(side="left")
        self.b_start = ttk.Button(top, text="Find duplicates", command=self.start)
        self.b_start.pack(side="left", padx=(14, 4))
        self.b_cancel = ttk.Button(top, text="Cancel", command=lambda: self.cancel.set(), state="disabled")
        self.b_cancel.pack(side="left")
        self.v_scope = tk.StringVar()
        ttk.Label(self, textvariable=self.v_scope, foreground="#666", padding=(8, 2), wraplength=1060
                  ).pack(fill="x")
        prog = ttk.Frame(self, padding=(8, 2))
        prog.pack(fill="x")
        self.pb = ttk.Progressbar(prog, mode="determinate", maximum=1000, length=260)
        self.pb.pack(side="left")
        self.v_prog = tk.StringVar(value="Press 'Find duplicates' to start.")
        ttk.Label(prog, textvariable=self.v_prog).pack(side="left", padx=8)

        mid = ttk.Frame(self, padding=(8, 4))
        mid.pack(fill="both", expand=True)
        self.tree = ttk.Treeview(mid, columns=("folder", "size", "modified"), show="tree headings",
                                 selectmode="extended")
        self.tree.heading("#0", text="Group / file name")
        self.tree.heading("folder", text="Folder")
        self.tree.heading("size", text="Size")
        self.tree.heading("modified", text="Modified")
        self.tree.column("#0", width=330, stretch=False)
        self.tree.column("folder", width=480, stretch=True)
        self.tree.column("size", width=90, anchor="e", stretch=False)
        self.tree.column("modified", width=130, stretch=False)
        self.tree.tag_configure("group", foreground="#1a5fb4", font=("Segoe UI", 9, "bold"))
        ys = ttk.Scrollbar(mid, orient="vertical", command=self.tree.yview)
        xs = ttk.Scrollbar(mid, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=ys.set, xscrollcommand=xs.set)
        self.tree.grid(row=0, column=0, sticky="nsew")
        ys.grid(row=0, column=1, sticky="ns")
        xs.grid(row=1, column=0, sticky="ew")
        mid.rowconfigure(0, weight=1)
        mid.columnconfigure(0, weight=1)
        self.tree.bind("<<TreeviewSelect>>", self._on_select)
        self.tree.bind("<Double-1>", self._on_double)
        self.tree.bind("<Button-3>", self._context_menu)
        self.tree.bind("<Delete>", lambda e: self.delete_selected())

        sel = ttk.Frame(self, padding=(8, 2))
        sel.pack(fill="x")
        ttk.Label(sel, text="Select:").pack(side="left")
        for txt, cmd in (("All but oldest", lambda: self.select_keep("oldest")),
                         ("All but newest", lambda: self.select_keep("newest")),
                         ("All but shortest path", lambda: self.select_keep("shortest")),
                         ("All except in folder…", self.select_except_folder),
                         ("Clear selection", self.clear_selection)):
            ttk.Button(sel, text=txt, command=cmd).pack(side="left", padx=(4, 0))

        bot = ttk.Frame(self, padding=(8, 4, 8, 8))
        bot.pack(fill="x")
        self.v_summary = tk.StringVar(value="")
        ttk.Label(bot, textvariable=self.v_summary, font=("Segoe UI", 9, "bold")).pack(side="left")
        ttk.Button(bot, text="Close", command=self.close).pack(side="right")
        self.b_delete = ttk.Button(bot, text="Delete selected (to Recycle Bin)…", command=self.delete_selected)
        self.b_delete.pack(side="right", padx=6)
        self.v_selinfo = tk.StringVar(value="")
        ttk.Label(bot, textvariable=self.v_selinfo, foreground="#666").pack(side="right", padx=10)

        self.menu = tk.Menu(self, tearoff=0)
        self.menu.add_command(label="Open", command=self.open_selected)
        self.menu.add_command(label="Show in Explorer", command=self.reveal_selected)
        self.protocol("WM_DELETE_WINDOW", self.close)
        self.bind("<Escape>", lambda e: self.close())
        self._describe_scope()
        self.after(60, self._poll)

    # ---- scanning
    def _describe_scope(self, o=None, targets=None):
        app = self.app
        o = o or app._search_options()
        if targets is None:
            targets = app._search_targets(o["scope"])[0]
        where = (f"{len(targets)} roots ({', '.join(t[0] for t in targets)})" if app.v_allroots.get()
                 else app.root_dir)
        parts = [f"Scope: {where}", f"Type: {o['type']}"]
        if o["scope"].strip():
            parts.append(f"Look in: {o['scope'].strip()}")
        if o["min_mb"] or o["max_mb"]:
            parts.append(f"Size MB: {o['min_mb'] or '0'} … {o['max_mb'] or '∞'}")
        if o["date_from"] or o["date_to"]:
            parts.append(f"Modified: {o['date_from'] or '…'} to {o['date_to'] or '…'}")
        self.v_scope.set("  ·  ".join(parts) + "   (filters come from the main window)")

    def start(self):
        if self.running:
            return
        try:
            kb = float(self.v_min.get().strip().replace(",", ".") or "0")
            if kb < 0:
                raise ValueError
        except ValueError:
            messagebox.showerror(APP, "Minimum size must be a number of KB (e.g. 1 or 1024).", parent=self)
            return
        o = self.app._search_options()
        try:
            for k in ("min_mb", "max_mb"):
                if o[k]:
                    float(o[k])
            parse_date(o["date_from"])
            parse_date(o["date_to"], end=True)
        except ValueError as ex:
            messagebox.showerror(APP, f"Check the filters in the main window: {ex}", parent=self)
            return
        targets, notes = self.app._search_targets(o["scope"])
        self._describe_scope(o, targets)
        if not targets:
            messagebox.showinfo(APP, f"Nothing to scan: {notes or 'no index yet'}.", parent=self)
            return
        self.app.settings["dup_min_kb"] = self.v_min.get().strip()
        self.app.settings["dup_quick"] = self.v_quick.get()
        self.app._save_settings()
        self.tree.delete(*self.tree.get_children())
        self.groups.clear()
        self.child.clear()
        self.v_summary.set("")
        self.v_selinfo.set("")
        self.cancel = threading.Event()
        self.gen += 1
        gen, cancel, quick = self.gen, self.cancel, self.v_quick.get()
        self.running = True
        self.b_start.configure(state="disabled")
        self.b_cancel.configure(state="normal")
        self.pb.configure(value=0)
        self.v_prog.set("Starting…")
        self._t0 = time.time()

        def work():
            try:
                groups, stats = find_duplicates(targets, o, int(kb * 1024), quick, cancel,
                                                lambda t, f: self.q.put(("prog", gen, t, f)))
                self.q.put(("done", gen, groups, stats, None))
            except Exception as ex:  # report in the window
                self.q.put(("done", gen, None, collections.Counter(), str(ex)))

        threading.Thread(target=work, daemon=True).start()

    def _poll(self):
        if not self.winfo_exists():
            return
        try:
            for _ in range(100):
                msg = self.q.get_nowait()
                if msg[1] != self.gen:
                    continue
                if msg[0] == "prog":
                    self.v_prog.set(msg[2])
                    self.pb.configure(value=int(msg[3] * 1000))
                elif msg[0] == "done":
                    self._finished(*msg[2:])
        except queue.Empty:
            pass
        self.after(80, self._poll)

    def _finished(self, groups, stats, err):
        self.running = False
        self.b_start.configure(state="normal")
        self.b_cancel.configure(state="disabled")
        if err:
            self.v_prog.set(f"Failed: {err}")
            return
        if groups is None:
            self.v_prog.set("Cancelled.")
            self.pb.configure(value=0)
            return
        for size, files in groups:
            n = len(files)
            g = self.tree.insert("", "end", open=True, tags=("group",),
                                 text=self._group_text(n, size))
            kids = []
            for path, mtime in files:
                c = self.tree.insert(g, "end", text=os.path.basename(path), values=(
                    os.path.dirname(path), human_size(size), self.app.fmt_time(mtime)))
                self.child[c] = (path, size, mtime, g)
                kids.append(c)
            self.groups[g] = {"size": size, "files": kids}
        notes = []
        if stats.get("missing"):
            notes.append(f"{stats['missing']:,} no longer exist")
        if stats.get("changed"):
            notes.append(f"{stats['changed']:,} changed since indexing")
        if stats.get("errors"):
            notes.append(f"{stats['errors']:,} could not be read")
        self.v_prog.set(f"Done in {time.time() - self._t0:.1f} s · {stats.get('candidates', 0):,} files with a "
                        f"same-size partner checked · {human_size(stats.get('read', 0))} read"
                        + (" · skipped: " + ", ".join(notes) + " (Rebuild index)" if notes else ""))
        self._update_summary()

    @staticmethod
    def _group_text(n, size):
        return f"{n} copies · {human_size(size)} each · {human_size(size * (n - 1))} wasted"

    def _update_summary(self):
        extra = sum(len(g["files"]) - 1 for g in self.groups.values())
        files = sum(len(g["files"]) for g in self.groups.values())
        waste = sum(g["size"] * (len(g["files"]) - 1) for g in self.groups.values())
        self.v_summary.set(f"{len(self.groups):,} groups · {files:,} files ({extra:,} duplicate copies) · "
                           f"{human_size(waste)} reclaimable" if self.groups else "No duplicates found.")
        self._on_select()

    # ---- selection
    def _on_select(self, event=None):
        sel = self.tree.selection()
        parents = [i for i in sel if i in self.groups]
        if parents:  # only files can be selected
            self.tree.selection_remove(*parents)
            sel = self.tree.selection()
        files = [self.child[i] for i in sel if i in self.child]
        self.v_selinfo.set(f"Selected: {len(files):,} files · {human_size(sum(f[1] for f in files))}"
                           if files else "")

    def select_keep(self, which):
        """In every group select all copies except the one to keep."""
        sel = []
        for info in self.groups.values():
            kids = info["files"]
            if which == "oldest":
                keep = min(kids, key=lambda c: (self.child[c][2], len(self.child[c][0])))
            elif which == "newest":
                keep = max(kids, key=lambda c: (self.child[c][2], -len(self.child[c][0])))
            else:
                keep = min(kids, key=lambda c: (len(self.child[c][0]), self.child[c][0].lower()))
            sel += [c for c in kids if c != keep]
        self.tree.selection_set(sel)
        self._on_select()

    def select_except_folder(self, folder=None):
        """Keep the copies inside a folder, select the other copies of those groups."""
        if folder is None:
            folder = filedialog.askdirectory(parent=self, title="Keep the copies inside this folder")
            if not folder:
                return
        sel, untouched = [], 0
        for info in self.groups.values():
            kids = info["files"]
            inside = [c for c in kids if path_in(self.child[c][0], folder)]
            if not inside:
                untouched += 1
                continue
            sel += [c for c in kids if c not in inside]
        self.tree.selection_set(sel)
        self._on_select()
        if untouched:
            self.v_prog.set(f"{untouched:,} group(s) have no copy in {os.path.abspath(folder)} - left unselected.")

    def clear_selection(self):
        self.tree.selection_set([])
        self._on_select()

    # ---- open / reveal
    def _paths(self):
        return [self.child[i][0] for i in self.tree.selection() if i in self.child]

    def _on_double(self, event):
        item = self.tree.identify_row(event.y)
        if item in self.child:
            self._open(self.child[item][0])
            return "break"

    def _open(self, path):
        try:
            os.startfile(path)
        except OSError as ex:
            messagebox.showerror(APP, f"Could not open:\n{path}\n\n{ex}", parent=self)

    def open_selected(self):
        for p in self._paths()[:10]:
            self._open(p)

    def reveal_selected(self):
        for p in self._paths()[:5]:
            subprocess.Popen(f'explorer /select,"{p}"')

    def _context_menu(self, event):
        item = self.tree.identify_row(event.y)
        if item in self.child:
            if item not in self.tree.selection():
                self.tree.selection_set(item)
            self.menu.tk_popup(event.x_root, event.y_root)

    # ---- deleting
    def delete_selected(self):
        try:
            self._delete_selected()
        except Exception as ex:  # never let a delete problem crash the app
            self.app._busy(False)
            messagebox.showerror(APP, f"Delete failed:\n{ex}", parent=self)

    def _delete_selected(self):
        if self.running:
            return
        sel = [i for i in self.tree.selection() if i in self.child]
        if not sel:
            self.v_prog.set("Select the copies to delete (buttons above, or Ctrl/Shift+click).")
            return
        selset = set(sel)
        lost = []
        for g, info in self.groups.items():
            kids = info["files"]
            if not any(c in selset for c in kids):
                continue
            keep = [c for c in kids if c not in selset]
            if not keep or not any(os.path.isfile(self.child[c][0]) for c in keep):
                lost.append(g)
        if lost:
            lines = [f"• {self.tree.item(g, 'text')}:  {self.child[self.groups[g]['files'][0]][0]}"
                     for g in lost[:15]]
            if len(lost) > 15:
                lines.append(f"… and {len(lost) - 15:,} more")
            messagebox.showerror(APP + " - delete", (
                f"Nothing was deleted.\n\nThe selection would remove ALL copies of {len(lost):,} group(s) "
                "(or the copies you keep no longer exist on disk). Leave at least one copy of every "
                "group unselected:\n\n" + "\n".join(lines)), parent=self)
            return
        paths = [self.child[c][0] for c in sel]
        size = sum(self.child[c][1] for c in sel)
        ngroups = len({self.child[c][3] for c in sel})
        msg = (f"Delete {len(paths):,} duplicate file(s) ({human_size(size)}) from {ngroups:,} group(s)?\n"
               "At least one copy of every group is kept.\n\n" + "\n".join(paths[:10]))
        if len(paths) > 10:
            msg += f"\n… and {len(paths) - 10:,} more"
        if not self.app._confirm_delete(msg, len(paths), False, paths, parent=self):
            self.v_prog.set("Delete cancelled.")
            return
        recycle = self.app._drive_check(paths)[0]
        todo, failures = self.app._recycle(paths, recycle, self)
        gone = [c for c in sel if not os.path.lexists(self.child[c][0])]
        rows = []
        for c in gone:
            path, sz, mtime, _ = self.child[c]
            rows.append((path, os.path.basename(path), os.path.splitext(path)[1][1:].lower(), sz, mtime, 0, ""))
        removed = self.app._remove_from_index(rows)
        self.app._remove_from_results(rows)
        self.app.readme_cache = None
        self.app._show_index_status()
        self._remove_children(gone)
        done = len([p for p in todo if not os.path.lexists(p)])
        status = (f"Moved {done:,} file(s) to the Recycle Bin" if recycle
                  else f"Deleted {done:,} file(s) permanently")
        if len(gone) > done:
            status += f" · {len(gone) - done:,} were already missing"
        if failures:
            status += f" · {len(failures):,} failed"
        if removed is None:
            status += " · index not updated - use Rebuild index"
        self.v_prog.set(status + ".")
        self.app.v_status.set(status + " (duplicate finder).")
        if failures:
            self.app._show_failures(failures, self)

    def _remove_children(self, iids):
        for c in iids:
            path, size, mtime, g = self.child.pop(c)
            if self.tree.exists(c):
                self.tree.delete(c)
            info = self.groups.get(g)
            if info and c in info["files"]:
                info["files"].remove(c)
        for g in list(self.groups):
            info = self.groups[g]
            if len(info["files"]) < 2:  # no longer a duplicate
                for c in info["files"]:
                    self.child.pop(c, None)
                if self.tree.exists(g):
                    self.tree.delete(g)
                del self.groups[g]
            else:
                self.tree.item(g, text=self._group_text(len(info["files"]), info["size"]))
        self._update_summary()

    def close(self):
        self.cancel.set()
        self.app.dup_window = None
        self.destroy()


class App(tk.Tk):
    COLS = ("name", "folder", "size", "modified", "type", "snippet")

    def __init__(self):
        super().__init__()
        self.title(APP)
        self.geometry("1250x780")
        self.minsize(960, 560)
        try:
            ttk.Style(self).theme_use("vista")
        except tk.TclError:
            pass
        self.settings = self._load_settings()
        self.root_dir = self.settings.get("root") or os.path.dirname(os.path.abspath(sys.argv[0]))
        self.db = db_path_for(self.root_dir)
        self.pdftotext = find_pdftotext()
        self.q = queue.Queue()
        self.gen = 0
        self.cancel = threading.Event()
        self.index_cancel = threading.Event()
        self.indexing = False
        self.rows = []
        self.row_by_iid = {}
        self.pending = []
        self.sort_state = {}
        self.readme_cache = None
        self._debounce = None
        self._reindex_after = False
        self._auto_run = False
        # several roots
        roots = self.settings.get("roots")
        if not isinstance(roots, list):
            roots = indexed_roots()  # default: every root that already has an index
        self.roots = [os.path.abspath(r) for r in roots if isinstance(r, str) and r.strip()]
        self.index_root = self.root_dir   # root the running indexer works on
        self.index_queue = []             # roots waiting to be (re)indexed, one at a time
        self._auto_failed = set()         # roots whose automatic refresh failed this session
        self._auto_started = set()        # roots rebuilt by "On every start" this session
        self._auto_startup = False
        self.roots_dialog = None
        self.dup_window = None
        # preview pane
        self.preview_gen = 0
        self._pv_after = None
        self._pv_resize_after = None
        self._pv_path = None
        self._pv_kind = None
        self._pv_box = None
        self._pv_photo = None
        self._build_ui()
        self._refresh_scopes()
        self._show_index_status()
        self.after(60, self._poll)
        self.protocol("WM_DELETE_WINDOW", self._on_close)
        if index_info(self.db) is None:
            self.after(300, self.rebuild_index)
        else:
            self.after(1500, lambda: self._auto_check(startup=True))
        self.after(AUTO_TICK_MS, self._auto_tick)
        self.entry.focus_set()

    # ---- settings
    def _load_settings(self):
        try:
            with open(SETTINGS_FILE, encoding="utf-8") as f:
                return json.load(f)
        except (OSError, ValueError):
            return {}

    def _save_settings(self):
        s = dict(self.settings)  # keeps keys owned by other windows (duplicate finder…)
        s.update({"root": self.root_dir, "field": self.v_field.get(), "type": self.v_type.get(),
                  "limit": self.v_limit.get(), "pdf": self.v_pdf.get(), "system": self.v_system.get(),
                  "auto": self.v_auto.get(), "sort": self.v_sort.get(), "date_format": self.v_datefmt.get(),
                  "geometry": self.geometry(), "roots": list(self.roots),
                  "all_roots": self.v_allroots.get(), "preview": self.v_preview.get()})
        w = self._preview_width()
        if w:
            s["preview_width"] = w
        self.settings = s
        try:
            os.makedirs(DATA_DIR, exist_ok=True)
            with open(SETTINGS_FILE, "w", encoding="utf-8") as f:
                json.dump(s, f, indent=1)
        except OSError:
            pass

    # ---- layout
    def _build_ui(self):
        s = self.settings
        if s.get("geometry"):
            try:
                self.geometry(s["geometry"])
            except tk.TclError:
                pass
        big = ("Segoe UI", 12)
        top = ttk.Frame(self, padding=(8, 8, 8, 2))
        top.pack(fill="x")
        ttk.Label(top, text="Search:", font=big).pack(side="left")
        self.v_query = tk.StringVar()
        self.entry = ttk.Entry(top, textvariable=self.v_query, font=big)
        self.entry.pack(side="left", fill="x", expand=True, padx=6)
        self.entry.bind("<Return>", lambda e: self.search())
        self.entry.bind("<KeyRelease>", self._on_key)
        self.entry.bind("<Escape>", lambda e: self.v_query.set(""))
        ttk.Button(top, text="Search", command=self.search).pack(side="left")
        self.b_stop = ttk.Button(top, text="Stop", command=self.stop, state="disabled")
        self.b_stop.pack(side="left", padx=(4, 0))
        ttk.Button(top, text="?", width=3, command=self.show_help).pack(side="left", padx=(4, 0))
        ttk.Button(top, text="Find duplicates…", command=self.open_duplicates).pack(side="left", padx=(12, 0))
        self.v_preview = tk.BooleanVar(value=bool(s.get("preview", True)))
        ttk.Checkbutton(top, text="Preview", variable=self.v_preview,
                        command=self._preview_toggled).pack(side="left", padx=(10, 0))

        row2 = ttk.Frame(self, padding=(8, 2))
        row2.pack(fill="x")
        ttk.Label(row2, text="Match in:").pack(side="left")
        self.v_field = tk.StringVar(value=s.get("field", "path"))
        for val, txt in (("name", "File name"), ("path", "Name + folder path"), ("content", "File contents")):
            ttk.Radiobutton(row2, text=txt, value=val, variable=self.v_field,
                            command=self._field_changed).pack(side="left", padx=4)
        self.v_regex = tk.BooleanVar(value=False)
        ttk.Checkbutton(row2, text="Regex", variable=self.v_regex).pack(side="left", padx=(12, 4))
        self.v_pdf = tk.BooleanVar(value=bool(s.get("pdf", False)))
        self.c_pdf = ttk.Checkbutton(row2, text="Include PDF text (slow)", variable=self.v_pdf)
        self.c_pdf.pack(side="left", padx=4)
        if not self.pdftotext:
            self.c_pdf.configure(text="PDF text (needs pdftotext)", state="disabled")
        self.v_system = tk.BooleanVar(value=bool(s.get("system", False)))
        ttk.Checkbutton(row2, text="Include system folders ($RECYCLE.BIN, .git, Thumbs.db…)",
                        variable=self.v_system, command=self._system_changed).pack(side="left", padx=(12, 4))

        row3 = ttk.Frame(self, padding=(8, 2, 8, 6))
        row3.pack(fill="x")
        ttk.Label(row3, text="Type:").pack(side="left")
        self.v_type = tk.StringVar(value=s.get("type", "All files and folders"))
        if self.v_type.get() not in TYPES:
            self.v_type.set("All files and folders")
        cb = ttk.Combobox(row3, textvariable=self.v_type, values=list(TYPES), state="readonly", width=20)
        cb.pack(side="left", padx=(2, 10))
        cb.bind("<<ComboboxSelected>>", lambda e: self.search())
        ttk.Label(row3, text="Look in:").pack(side="left")
        self.v_scope = tk.StringVar(value="")
        self.cb_scope = ttk.Combobox(row3, textvariable=self.v_scope, width=38)
        self.cb_scope.pack(side="left", padx=2)
        self.cb_scope.bind("<<ComboboxSelected>>", lambda e: self.search())
        self.cb_scope.bind("<Return>", lambda e: self.search())
        ttk.Button(row3, text="…", width=3, command=self.browse_scope).pack(side="left")
        ttk.Button(row3, text="✕", width=3, command=lambda: (self.v_scope.set(""), self.search())
                   ).pack(side="left", padx=(2, 10))
        self.v_min, self.v_max, self.v_y1, self.v_y2 = (tk.StringVar() for _ in range(4))
        for label, var, w in (("Size MB ≥", self.v_min, 6), ("≤", self.v_max, 6)):
            ttk.Label(row3, text=label).pack(side="left", padx=(4, 1))
            e = ttk.Entry(row3, textvariable=var, width=w)
            e.pack(side="left")
            e.bind("<Return>", lambda ev: self.search())
        ttk.Label(row3, text="Max results").pack(side="left", padx=(10, 1))
        self.v_limit = tk.StringVar(value=str(s.get("limit", "2000")))
        ttk.Spinbox(row3, from_=100, to=100000, increment=500, textvariable=self.v_limit, width=7
                    ).pack(side="left")

        row4 = ttk.Frame(self, padding=(8, 0, 8, 6))
        row4.pack(fill="x")
        ttk.Label(row4, text="Modified date:").pack(side="left")
        self.v_preset = tk.StringVar(value="Any date")
        cb_date = ttk.Combobox(row4, textvariable=self.v_preset, values=DATE_PRESETS, state="readonly", width=13)
        cb_date.pack(side="left", padx=(2, 10))
        cb_date.bind("<<ComboboxSelected>>", lambda e: self._preset_selected())
        self.date_entries = {}
        for label, var in (("From", self.v_y1), ("To", self.v_y2)):
            ttk.Label(row4, text=label).pack(side="left", padx=(4, 1))
            e = ttk.Entry(row4, textvariable=var, width=11)
            e.pack(side="left")
            e.bind("<Return>", lambda ev: self.search())
            e.bind("<KeyRelease>", self._date_typed)
            ttk.Button(row4, text="📅", width=3,
                       command=lambda e=e, var=var: self.open_calendar(e, var)).pack(side="left", padx=(1, 2))
            self.date_entries[label] = e
        ttk.Button(row4, text="✕", width=3, command=lambda: (self.v_preset.set("Any date"),
                                                             self._preset_selected())).pack(side="left", padx=(2, 8))
        self.v_sort = tk.StringVar(value=s.get("sort", "Best match"))
        if self.v_sort.get() not in SORTS:
            self.v_sort.set("Best match")
        cb_sort = ttk.Combobox(row4, textvariable=self.v_sort, values=list(SORTS), state="readonly", width=13)
        cb_sort.pack(side="right")
        cb_sort.bind("<<ComboboxSelected>>", lambda e: self.search())
        ttk.Label(row4, text="Sort:").pack(side="right", padx=(8, 2))
        self.v_datefmt = tk.StringVar(value=s.get("date_format", DEFAULT_DATE_FORMAT))
        if self.v_datefmt.get() not in DATE_FORMATS:
            self.v_datefmt.set(DEFAULT_DATE_FORMAT)
        cb_fmt = ttk.Combobox(row4, textvariable=self.v_datefmt, values=list(DATE_FORMATS),
                              state="readonly", width=15)
        cb_fmt.pack(side="right")
        cb_fmt.bind("<<ComboboxSelected>>", lambda e: self._date_format_changed())
        ttk.Label(row4, text="Show dates:").pack(side="right", padx=(8, 2))
        ttk.Label(row4, text="To is inclusive",
                  foreground="#666").pack(side="left")

        pane = ttk.PanedWindow(self, orient="vertical")
        pane.pack(fill="both", expand=True, padx=8)
        self.hpane = ttk.PanedWindow(pane, orient="horizontal")
        res = ttk.Frame(self.hpane)
        self.tree = ttk.Treeview(res, columns=self.COLS, show="headings", selectmode="extended")
        widths = {"name": 300, "folder": 420, "size": 80, "modified": 120, "type": 60, "snippet": 380}
        heads = {"name": "Name", "folder": "Folder", "size": "Size", "modified": "Modified",
                 "type": "Type", "snippet": "Match in file"}
        for c in self.COLS:
            self.tree.heading(c, text=heads[c], command=lambda c=c: self.sort_by(c))
            self.tree.column(c, width=widths[c], anchor="e" if c == "size" else "w",
                             stretch=c in ("folder", "snippet"))
        ys = ttk.Scrollbar(res, orient="vertical", command=self.tree.yview)
        xs = ttk.Scrollbar(res, orient="horizontal", command=self.tree.xview)
        self.tree.configure(yscrollcommand=ys.set, xscrollcommand=xs.set)
        self.tree.grid(row=0, column=0, sticky="nsew")
        ys.grid(row=0, column=1, sticky="ns")
        xs.grid(row=1, column=0, sticky="ew")
        res.rowconfigure(0, weight=1)
        res.columnconfigure(0, weight=1)
        self.tree.tag_configure("dir", foreground="#1a5fb4")
        self.tree.bind("<Double-1>", lambda e: self.open_selected())
        self.tree.bind("<Return>", lambda e: self.open_selected())
        self.tree.bind("<Button-3>", self._context_menu)
        self.tree.bind("<Control-c>", lambda e: self.copy_paths())
        self.tree.bind("<Control-a>", self._select_all)
        self.tree.bind("<Control-A>", self._select_all)
        self.tree.bind("<Delete>", lambda e: self.delete_selected())
        self.tree.bind("<<TreeviewSelect>>", self._on_tree_select)
        self.hpane.add(res, weight=1)
        self._build_preview()
        if self.v_preview.get():
            self.hpane.add(self.pv, weight=0)
            self.after(250, self._place_preview_sash)
        pane.add(self.hpane, weight=4)

        hints = ttk.LabelFrame(pane, text="README hints  (double-click: search only in that folder · right-click: open README)")
        self.hints = ttk.Treeview(hints, columns=("where", "line"), show="headings", height=5)
        self.hints.heading("where", text="Index file")
        self.hints.heading("line", text="Mentions your terms")
        self.hints.column("where", width=300, stretch=False)
        self.hints.column("line", width=900)
        hs = ttk.Scrollbar(hints, orient="vertical", command=self.hints.yview)
        self.hints.configure(yscrollcommand=hs.set)
        self.hints.pack(side="left", fill="both", expand=True)
        hs.pack(side="right", fill="y")
        self.hints.bind("<Double-1>", self._hint_scope)
        self.hints.bind("<Button-3>", self._hint_open)
        pane.add(hints, weight=1)

        self.menu = tk.Menu(self, tearoff=0)
        self.menu.add_command(label="Open", command=self.open_selected)
        self.menu.add_command(label="Show in Explorer", command=self.reveal_selected)
        self.menu.add_command(label="Search inside this folder", command=self.scope_to_selected)
        self.menu.add_separator()
        self.menu.add_command(label="Copy full path", command=self.copy_paths)
        self.menu.add_command(label="Copy name", command=lambda: self.copy_paths(names=True))
        self.menu.add_command(label="Select all", accelerator="Ctrl+A", command=self._select_all)
        self.menu.add_separator()
        self.menu.add_command(label="Delete… (to Recycle Bin)", accelerator="Del",
                              command=self.delete_selected)

        bar = ttk.Frame(self, padding=(8, 4))
        bar.pack(fill="x")
        self.v_status = tk.StringVar(value="Ready.")
        ttk.Label(bar, textvariable=self.v_status).pack(side="left")
        ttk.Button(bar, text="Change root…", command=self.change_root).pack(side="right")
        ttk.Button(bar, text="Roots…", command=self.open_roots).pack(side="right", padx=(4, 0))
        self.v_allroots = tk.BooleanVar(value=bool(s.get("all_roots", False)))
        ttk.Checkbutton(bar, text="Search all roots", variable=self.v_allroots,
                        command=self._allroots_changed).pack(side="right", padx=(8, 0))
        self.b_index = ttk.Button(bar, text="Rebuild index", command=self._rebuild_clicked)
        self.b_index.pack(side="right", padx=4)
        self.v_auto = tk.StringVar(value=s.get("auto", "Daily"))
        if self.v_auto.get() not in AUTO_OPTIONS:
            self.v_auto.set("Daily")
        cb_auto = ttk.Combobox(bar, textvariable=self.v_auto, values=list(AUTO_OPTIONS),
                               state="readonly", width=14)
        cb_auto.pack(side="right")
        cb_auto.bind("<<ComboboxSelected>>", lambda e: self._auto_changed())
        ttk.Label(bar, text="Auto-refresh:").pack(side="right", padx=(8, 2))
        ttk.Button(bar, text="Export CSV…", command=self.export_csv).pack(side="right")
        self.v_index = tk.StringVar()
        ttk.Label(bar, textvariable=self.v_index, foreground="#666").pack(side="right", padx=10)
        self._field_changed()

    # ---- index management
    def _show_index_status(self):
        if self.v_allroots.get():
            roots = self._all_roots()
            items, missing, offline = 0, 0, 0
            for r in roots:
                info = index_info(db_path_for(r))
                if info is None:
                    missing += 1
                else:
                    items += int(info.get("count", 0))
                    offline += not os.path.isdir(r)
            extra = (f"  ·  {missing} not indexed" if missing else "") + (f"  ·  {offline} offline" if offline else "")
            self.v_index.set(f"{len(roots)} roots  ·  {items:,} items{extra}")
            return
        info = index_info(self.db)
        if info:
            built = self.fmt_time(float(info.get("built", 0)))
            extra = "  ·  incl. system folders" if info.get("system") == "1" else ""
            self.v_index.set(f"{self.root_dir}  ·  {int(info.get('count', 0)):,} items  ·  indexed {built}{extra}")
        else:
            self.v_index.set(f"{self.root_dir}  ·  not indexed yet")

    def _refresh_scopes(self):
        vals = []
        if self.v_allroots.get():  # absolute top-level folders of every root
            for r in self._all_roots():
                try:
                    vals += sorted((e.path for e in os.scandir(r)
                                    if e.is_dir() and e.name.lower() not in SKIP_DIRS), key=str.lower)
                except OSError:
                    pass
        else:
            try:
                vals = sorted((e.name for e in os.scandir(self.root_dir)
                               if e.is_dir() and e.name.lower() not in SKIP_DIRS), key=str.lower)
            except OSError:
                vals = []
        self.cb_scope.configure(values=[""] + vals)
        self.readme_cache = None

    # ---- several roots
    def _all_roots(self):
        """Current root first, then the 'roots' list; duplicates removed."""
        seen, out = set(), []
        for r in [self.root_dir] + list(self.roots):
            a = os.path.abspath(r)
            k = os.path.normcase(a)
            if k not in seen:
                seen.add(k)
                out.append(a)
        return out

    def _known_roots(self):
        """Every root whose index might list a path (for index clean-up after deleting)."""
        return [r for r in self._all_roots() if os.path.isfile(db_path_for(r))]

    def _scope_for_root(self, scope, root):
        """Translate the Look in text into a scope relative to root, or None if the folder is
        not inside root. Absolute folders work in both modes; a relative folder means
        'relative to the current root'."""
        s = (scope or "").strip()
        if not s:
            return ""
        if os.path.splitdrive(s)[0]:
            if not path_in(s, root):
                return None
            return rel_to(s, root)
        if self.v_allroots.get() and os.path.normcase(os.path.abspath(root)) != os.path.normcase(
                os.path.abspath(self.root_dir)):
            return None
        return s

    def _search_targets(self, scope):
        """([(root, db, relative_scope)], problems_text) for the roots to search."""
        multi = self.v_allroots.get()
        targets, missing, offline, outside = [], 0, 0, 0
        for r in (self._all_roots() if multi else [self.root_dir]):
            db = db_path_for(r)
            if index_info(db) is None:
                missing += 1
                continue
            if multi and not os.path.isdir(r):
                offline += 1
                continue
            rel = self._scope_for_root(scope, r)
            if rel is None:
                outside += 1
                continue
            targets.append((r, db, rel))
        notes = []
        if multi and missing:
            notes.append(f"{missing} root(s) not indexed yet")
        if offline:
            notes.append(f"{offline} root(s) offline")
        if not targets and outside:
            notes.append("the Look in folder is not inside " + ("any root" if multi else "the root"))
        return targets, ", ".join(notes)

    def _allroots_changed(self):
        sc = self.v_scope.get().strip()
        if self.v_allroots.get():
            if sc and not os.path.splitdrive(sc)[0]:
                self.v_scope.set(os.path.join(self.root_dir, sc))
        elif sc and os.path.splitdrive(sc)[0]:
            self.v_scope.set(rel_to(sc, self.root_dir) if path_in(sc, self.root_dir) else "")
        self._save_settings()
        self._refresh_scopes()
        self._show_index_status()
        if self.v_allroots.get():
            self.after(500, self._auto_check)
        self.search()

    def open_roots(self):
        if self.roots_dialog is not None and self.roots_dialog.winfo_exists():
            self.roots_dialog.lift()
            return
        self.roots_dialog = RootsDialog(self)

    def _roots_changed(self):
        self._save_settings()
        if self.v_allroots.get():
            self._refresh_scopes()
        self.readme_cache = None
        self._show_index_status()

    def _auto_check(self, startup=False):
        """Rebuild in the background when an index is older than the auto-refresh setting.
        With 'Search all roots' on, the other roots are refreshed too, one at a time."""
        limit = AUTO_OPTIONS.get(self.v_auto.get())
        if limit is None or self.indexing:
            return
        if startup:
            self._auto_startup = True
        roots = self._all_roots() if self.v_allroots.get() else [self.root_dir]
        for i, r in enumerate(roots):
            k = os.path.normcase(r)
            if k in self._auto_failed:
                continue
            info = index_info(db_path_for(r))
            if info is None:
                if i == 0 or not os.path.isdir(r):  # current root: built at start / by change_root
                    continue
                stale = True
            elif limit == 0:
                stale = self._auto_startup and k not in self._auto_started
            else:
                stale = time.time() - float(info.get("built", 0)) >= limit
            if stale:
                self._auto_started.add(k)
                self.rebuild_index(auto=True, root=r)
                return
        self._auto_startup = False

    def _auto_tick(self):
        try:
            self._auto_failed.clear()  # retry failed roots every tick, like before
            self._auto_check()
        finally:
            self.after(AUTO_TICK_MS, self._auto_tick)

    def _auto_changed(self):
        self._save_settings()
        self._auto_check()

    def _rebuild_clicked(self):
        if self.indexing:  # the button reads "Cancel indexing"
            self.index_queue.clear()
            self.index_cancel.set()
            return
        if self.v_allroots.get():  # rebuild every root, one after the other
            self.index_queue = [r for r in self._all_roots()[1:] if os.path.isdir(r)]
        self.rebuild_index()

    def rebuild_index(self, auto=False, root=None):
        """(Re)build the index of root (default: the current root) in a worker thread.
        While indexing runs, an explicit request for another root is queued."""
        if self.indexing:
            if root is not None and not auto:
                if not any(os.path.normcase(q) == os.path.normcase(root) for q in self.index_queue):
                    self.index_queue.append(root)
            elif not auto:
                self.index_cancel.set()
            return
        self._auto_run = auto
        self.indexing = True
        self.index_cancel.clear()
        self.b_index.configure(text="Cancel indexing")
        root = os.path.abspath(root or self.root_dir)
        self.index_root = root
        db, system = db_path_for(root), self.v_system.get()

        def work():
            try:
                n = build_index(root, db, lambda c, d: self.q.put(("iprog", c, d)), self.index_cancel,
                                include_system=system)
                self.q.put(("idone", n, None))
            except Exception as ex:  # report any failure in the UI
                self.q.put(("idone", None, str(ex)))

        threading.Thread(target=work, daemon=True).start()

    def _system_changed(self):
        self._save_settings()
        info = index_info(self.db) or {}
        if (info.get("system") == "1") == self.v_system.get():
            return
        if self.indexing:
            self._reindex_after = True
            self.index_cancel.set()
        elif messagebox.askyesno(APP, "Rebuild the index now so this setting takes effect?\n"
                                      "(About 15 seconds for H:\\all files.)"):
            self.rebuild_index()

    def change_root(self):
        d = filedialog.askdirectory(initialdir=self.root_dir, title="Folder to search")
        if not d:
            return
        self.root_dir = os.path.abspath(d)
        self.db = db_path_for(self.root_dir)
        if not any(os.path.normcase(r) == os.path.normcase(self.root_dir) for r in self.roots):
            self.roots.append(self.root_dir)  # remember it for "Search all roots"
        self.v_scope.set("")
        self._refresh_scopes()
        self._show_index_status()
        self.tree.delete(*self.tree.get_children())
        self._save_settings()
        if index_info(self.db) is None:
            if self.indexing:  # stop indexing the old root, then index the new one
                self._reindex_after = True
                self.index_cancel.set()
            else:
                self.rebuild_index()

    # ---- searching
    def _search_options(self):
        return {"query": self.v_query.get(), "field": self.v_field.get(), "regex": self.v_regex.get(),
                "type": self.v_type.get(), "scope": self.v_scope.get(), "min_mb": self.v_min.get().strip(),
                "max_mb": self.v_max.get().strip(), "date_from": self.v_y1.get().strip(),
                "date_to": self.v_y2.get().strip(), "limit": self.v_limit.get().strip() or "2000",
                "sort": self.v_sort.get(),
                "pdf": self.v_pdf.get()}

    def open_calendar(self, entry, var):
        def picked():
            self.v_preset.set("Custom" if (self.v_y1.get().strip() or self.v_y2.get().strip()) else "Any date")
            self.search()
        CalendarPopup(self, entry, var, picked)

    def _preset_selected(self):
        name = self.v_preset.get()
        if name == "Custom":
            return
        a, b = date_preset(name)
        self.v_y1.set(a)
        self.v_y2.set(b)
        self.search()

    def _date_typed(self, event):
        if event.keysym not in ("Return", "Tab", "Shift_L", "Shift_R"):
            self.v_preset.set("Custom" if (self.v_y1.get().strip() or self.v_y2.get().strip()) else "Any date")

    def _field_changed(self):
        content = self.v_field.get() == "content"
        if self.pdftotext:
            self.c_pdf.configure(state="normal" if content else "disabled")
        self.tree.column("snippet", width=380 if content else 120)

    def _on_key(self, event):
        if event.keysym in ("Return", "Escape") or self.v_field.get() == "content":
            return
        if self._debounce:
            self.after_cancel(self._debounce)
        self._debounce = self.after(350, self.search)

    def search(self):
        if self._debounce:
            self.after_cancel(self._debounce)
            self._debounce = None
        multi = self.v_allroots.get()
        if not multi and index_info(self.db) is None:
            self.v_status.set("The index is still being built - please wait.")
            return
        o = self._search_options()
        try:
            for k in ("min_mb", "max_mb"):
                if o[k]:
                    float(o[k])
            start, stop = parse_date(o["date_from"]), parse_date(o["date_to"], end=True)
            if start is not None and stop is not None and start >= stop:
                raise ValueError("the From date is after the To date")
            int(o["limit"])
            if o["regex"] and o["query"].strip():
                re.compile(o["query"])
        except (ValueError, re.error) as ex:
            self.v_status.set(f"Check the filters: {ex}")
            return
        targets, notes = self._search_targets(o["scope"])
        self.cancel.set()
        self.cancel = threading.Event()
        self.gen += 1
        gen, cancel = self.gen, self.cancel
        self.rows, self.pending = [], []
        self.row_by_iid.clear()
        self.tree.delete(*self.tree.get_children())
        self._update_hints(o)
        self.b_stop.configure(state="normal")
        self.v_status.set("Searching…")
        t0 = time.time()
        if not targets:
            self.b_stop.configure(state="disabled")
            self.v_status.set(f"Nothing to search: {notes or 'no index yet'}.")
            return
        db, root = self.db, self.root_dir
        if not multi:
            o["scope"] = targets[0][2]  # absolute Look in folder -> relative to the root
        note_txt = f"  ·  {notes}" if notes else ""

        def work_multi():
            limit = int(o["limit"])
            if o["field"] == "content":
                found, checked = [], 0
                for i, (r, d, sc) in enumerate(targets, 1):
                    if cancel.is_set():
                        break
                    n, c, note = search_contents(
                        d, r, dict(o, scope=sc), self.pdftotext, cancel,
                        lambda rows, r=r: found.extend(((os.path.join(r, x[0]),) + tuple(x[1:]), len(x[0]))
                                                       for x in rows),
                        lambda msg, i=i: self.q.put(("status", gen, f"Root {i}/{len(targets)}: {msg}")))
                    if c == 0 and note and not o["regex"] and not parse_query(o["query"])[0]:
                        return note
                    checked += c
                key = merge_sort_key(o)
                found.sort(key=lambda x: key(x[0], x[1]))
                rows = [x[0] for x in found[:limit]]
                self.q.put(("rows", gen, rows))
                shown = (f"{len(rows):,} of {len(found):,}+" if len(found) > limit else f"{len(rows):,}")
                return (f"{shown} files contain your terms ({checked:,} text files checked in "
                        f"{len(targets)} roots)" + (" - stopped" if cancel.is_set() else ""))
            rows, total = search_names_multi(targets, o)
            self.q.put(("rows", gen, rows))
            if total > len(rows):
                order = o.get("sort") or "Best match"
                return (f"{len(rows):,} of {total:,} matches in {len(targets)} roots shown ({order.lower()}) - "
                        f"narrow the search, change Sort, or raise Max results")
            return f"{len(rows):,} results in {len(targets)} roots"

        def work():
            try:
                if multi:
                    msg = work_multi()
                elif o["field"] == "content":
                    n, checked, note = search_contents(
                        db, root, o, self.pdftotext, cancel,
                        lambda rows: self.q.put(("rows", gen, rows)),
                        lambda msg: self.q.put(("status", gen, msg)))
                    if checked == 0 and note:
                        msg = note
                    else:
                        msg = (f"{n:,} files contain your terms ({checked:,} text files checked{note})"
                               + (" - stopped" if cancel.is_set() else ""))
                else:
                    rows, total = search_names(db, o, want_total=True)
                    self.q.put(("rows", gen, rows))
                    if total > len(rows):
                        order = o.get("sort") or "Best match"
                        msg = (f"{len(rows):,} of {total:,} matches shown ({order.lower()}) - narrow the search, "
                               f"change Sort, or raise Max results")
                    else:
                        msg = f"{len(rows):,} results"
                self.q.put(("done", gen, f"{msg}  ·  {time.time() - t0:.2f} s{note_txt}"))
            except Exception as ex:
                self.q.put(("done", gen, f"Search failed: {ex}"))

        threading.Thread(target=work, daemon=True).start()

    def stop(self):
        self.cancel.set()

    def _poll(self):
        try:
            for _ in range(200):
                msg = self.q.get_nowait()
                kind = msg[0]
                if kind == "rows" and msg[1] == self.gen:
                    self.pending.extend(msg[2])
                elif kind == "status" and msg[1] == self.gen:
                    self.v_status.set(msg[2])
                elif kind == "done" and msg[1] == self.gen:
                    self.pending.append(("__done__", msg[2]))
                elif kind == "preview" and msg[1] == self.preview_gen:
                    self._preview_show(msg[2])
                elif kind == "iprog":
                    self.v_index.set(f"Indexing {self.index_root} … {msg[1]:,} items  ({msg[2][-60:]})")
                elif kind == "idone":
                    self._index_done(msg[1], msg[2])
        except queue.Empty:
            pass
        self._flush_pending()
        self.after(60, self._poll)

    def _index_done(self, n, err):
        self.indexing = False
        self.b_index.configure(text="Rebuild index")
        root = self.index_root
        other = os.path.normcase(root) != os.path.normcase(self.root_dir)
        where = f" of {root}" if other else ""
        self._refresh_scopes()
        self._show_index_status()
        if self.roots_dialog is not None and self.roots_dialog.winfo_exists():
            self.roots_dialog.refresh()
        was_auto, self._auto_run = self._auto_run, False
        if err and was_auto:
            self._auto_failed.add(os.path.normcase(root))
        if self._reindex_after:
            self._reindex_after = False
            self.rebuild_index()
            return
        if err:
            if was_auto:  # don't interrupt the user with a dialog for a background refresh
                self.v_status.set(f"Automatic index refresh{where} failed: {err}")
            else:
                messagebox.showerror(APP, f"Indexing{where} failed:\n{err}")
        elif n is not None:
            if was_auto:  # keep the results the user is looking at
                self.v_status.set(f"Index{where} refreshed automatically: {n:,} items "
                                  f"({time.strftime('%H:%M')}). Search again to see changes.")
            else:
                self.v_status.set(f"Index{where} ready: {n:,} items. Type to search.")
                if self.v_query.get().strip() and not self.index_queue and (
                        not other or self.v_allroots.get()):
                    self.search()
        else:
            self.index_queue.clear()  # cancelled
        if self.index_queue:
            self.rebuild_index(root=self.index_queue.pop(0))
        elif was_auto and (n is not None or err):
            self.after(1000, self._auto_check)  # next stale root, one at a time

    def _flush_pending(self):
        n = 0
        while self.pending and n < 600:
            r = self.pending.pop(0)
            if r[0] == "__done__":
                self.v_status.set(r[1])
                self.b_stop.configure(state="disabled")
                continue
            self._insert_row(r)
            n += 1

    def _insert_row(self, r):
        rel, name, ext, size, mtime, isdir, snippet = r
        self.rows.append(r)
        folder = os.path.dirname(rel)
        iid = self.tree.insert("", "end", tags=("dir",) if isdir else (), values=(
            ("📁 " if isdir else "") + name, folder or ".", "" if isdir else human_size(size),
            self.fmt_time(mtime),
            "folder" if isdir else ext, snippet))
        self.row_by_iid[iid] = r

    def fmt_time(self, ts):
        if not ts:
            return ""
        fmt = DATE_FORMATS.get(self.v_datefmt.get(), DATE_FORMATS[DEFAULT_DATE_FORMAT])
        return time.strftime(fmt, time.localtime(ts))

    def _date_format_changed(self):
        self._save_settings()
        self._show_index_status()
        rows = list(self.rows)
        self.rows = []
        self.row_by_iid.clear()
        self.tree.delete(*self.tree.get_children())
        for r in rows:
            self._insert_row(r)

    def sort_by(self, col):
        idx = {"name": 1, "folder": 0, "size": 3, "modified": 4, "type": 2, "snippet": 6}[col]
        rev = not self.sort_state.get(col, False)
        self.sort_state = {col: rev}
        key = (lambda r: (r[idx] or "").lower()) if idx in (0, 1, 2, 6) else (lambda r: r[idx] or 0)
        rows = sorted(self.rows, key=key, reverse=rev)
        self.rows = []
        self.row_by_iid.clear()
        self.tree.delete(*self.tree.get_children())
        for r in rows:
            self._insert_row(r)

    # ---- README hints
    def _load_readmes(self):
        """README.md / CLAUDE.md lines of the current root (relative paths), or of every root
        when 'Search all roots' is on (absolute paths)."""
        texts = []
        multi = self.v_allroots.get()
        rels = []
        for root in (self._all_roots() if multi else [self.root_dir]):
            db = db_path_for(root)
            if not os.path.isfile(db) or (multi and not os.path.isdir(root)):
                continue
            try:
                con = sqlite3.connect(db)
                try:
                    found = [r[0] for r in con.execute(
                        "SELECT rel FROM files WHERE isdir = 0 AND fname IN ('readme.md', 'claude.md')")]
                finally:
                    con.close()
            except sqlite3.Error:
                found = []
            rels += [os.path.join(root, r) for r in found] if multi else found
        for rel in rels:
            try:
                with open(os.path.join(self.root_dir, rel), encoding="utf-8", errors="replace") as f:
                    for line in f:
                        line = line.strip()
                        if len(line) > 3:
                            texts.append((rel, line, fold(line)))
            except OSError:
                pass
        self.readme_cache = texts

    def _update_hints(self, o):
        self.hints.delete(*self.hints.get_children())
        if o["regex"]:
            return
        include, _, _ = parse_query(o["query"])
        if not include:
            return
        if self.readme_cache is None:
            self._load_readmes()
        scored = []
        for rel, line, fl in self.readme_cache:
            s = sum(1 for t in include if t.replace("*", "") in fl)
            if s:
                scored.append((-s, len(line), rel, line))
        scored.sort()
        for _, _, rel, line in scored[:40]:
            clean = re.sub(r"\]\(<[^>]*>\)|\]\([^)]*\)", "]", line).replace("**", "")
            self.hints.insert("", "end", values=(rel, clean))

    def _hint_scope(self, event):
        item = self.hints.identify_row(event.y)
        if not item:
            return
        rel = self.hints.item(item, "values")[0]
        self.v_scope.set(os.path.dirname(rel))
        self.search()

    def _hint_open(self, event):
        item = self.hints.identify_row(event.y)
        if item:
            path = os.path.join(self.root_dir, self.hints.item(item, "values")[0])
            subprocess.Popen(["notepad.exe", path])

    # ---- actions on results
    def _selected(self):
        return [self.row_by_iid[i] for i in self.tree.selection() if i in self.row_by_iid]

    def _full(self, r):
        return os.path.join(self.root_dir, r[0])

    def open_selected(self):
        for r in self._selected()[:10]:
            try:
                os.startfile(self._full(r))
            except OSError as ex:
                messagebox.showerror(APP, f"Could not open:\n{self._full(r)}\n\n{ex}")

    def reveal_selected(self):
        for r in self._selected()[:5]:
            subprocess.Popen(f'explorer /select,"{self._full(r)}"')

    def scope_to_selected(self):
        sel = self._selected()
        if sel:
            r = sel[0]
            self.v_scope.set(r[0] if r[5] else os.path.dirname(r[0]))
            self.search()

    def copy_paths(self, names=False):
        sel = self._selected()
        if sel:
            self.clipboard_clear()
            self.clipboard_append("\n".join(r[1] if names else self._full(r) for r in sel))
            self.v_status.set(f"Copied {len(sel)} {'name' if names else 'path'}(s).")

    def _context_menu(self, event):
        item = self.tree.identify_row(event.y)
        if item:
            if item not in self.tree.selection():
                self.tree.selection_set(item)
            self.menu.tk_popup(event.x_root, event.y_root)

    def _select_all(self, event=None):
        items = self.tree.get_children()
        if items:
            self.tree.selection_set(items)
            self.v_status.set(f"Selected {len(items):,} item(s).")
        return "break"

    # ---- preview pane
    def _build_preview(self):
        pv = self.pv = ttk.Frame(self.hpane, padding=(8, 0, 0, 0))
        self.v_pv_name, self.v_pv_path, self.v_pv_info, self.v_pv_extra = (tk.StringVar() for _ in range(4))
        self.pv_name = ttk.Label(pv, textvariable=self.v_pv_name, font=("Segoe UI", 10, "bold"), wraplength=330)
        self.pv_name.pack(fill="x")
        self.pv_path = ttk.Label(pv, textvariable=self.v_pv_path, foreground="#666", wraplength=330)
        self.pv_path.pack(fill="x")
        ttk.Label(pv, textvariable=self.v_pv_info).pack(fill="x", pady=(2, 0))
        self.pv_extra = ttk.Label(pv, textvariable=self.v_pv_extra, foreground="#666", wraplength=330)
        self.pv_extra.pack(fill="x")
        btns = ttk.Frame(pv)
        btns.pack(fill="x", pady=(4, 4))
        self.pv_b_open = ttk.Button(btns, text="Open", command=self._pv_open, state="disabled")
        self.pv_b_open.pack(side="left")
        self.pv_b_reveal = ttk.Button(btns, text="Show in Explorer", command=self._pv_reveal, state="disabled")
        self.pv_b_reveal.pack(side="left", padx=4)
        self.pv_body = ttk.Frame(pv)
        self.pv_body.pack(fill="both", expand=True)
        self.pv_img = ttk.Label(self.pv_body, anchor="center")
        self.pv_textf = ttk.Frame(self.pv_body)
        self.pv_text = tk.Text(self.pv_textf, font=("Consolas", 9), wrap="none", width=40, height=10,
                               relief="flat", background="#fbfbfb", state="disabled")
        ys = ttk.Scrollbar(self.pv_textf, orient="vertical", command=self.pv_text.yview)
        xs = ttk.Scrollbar(self.pv_textf, orient="horizontal", command=self.pv_text.xview)
        self.pv_text.configure(yscrollcommand=ys.set, xscrollcommand=xs.set)
        self.pv_text.grid(row=0, column=0, sticky="nsew")
        ys.grid(row=0, column=1, sticky="ns")
        xs.grid(row=1, column=0, sticky="ew")
        self.pv_textf.rowconfigure(0, weight=1)
        self.pv_textf.columnconfigure(0, weight=1)
        pv.bind("<Configure>", self._pv_configure)
        self._pv_clear("Select a result to preview it.")

    def _preview_width(self):
        try:
            if self.v_preview.get() and self._pv_shown():
                w = self.hpane.winfo_width() - self.hpane.sashpos(0)
                return w if 120 <= w <= 2000 else None
        except (tk.TclError, AttributeError):
            pass
        return None

    def _place_preview_sash(self):
        try:
            if not self._pv_shown():
                return
            total = self.hpane.winfo_width()
            if total < 50:  # not laid out yet
                self.after(200, self._place_preview_sash)
                return
            w = int(self.settings.get("preview_width") or 350)
            self.hpane.sashpos(0, max(250, total - min(w, total - 250)))
        except (tk.TclError, ValueError):
            pass

    def _pv_shown(self):
        try:
            return str(self.pv) in [str(p) for p in self.hpane.panes()]
        except tk.TclError:
            return False

    def _preview_toggled(self):
        if self.v_preview.get():
            if not self._pv_shown():
                self.hpane.add(self.pv, weight=0)
                self.after(50, self._place_preview_sash)
                self._preview_request()
        else:
            if self._pv_shown():
                w = self.hpane.winfo_width() - self.hpane.sashpos(0)
                if 120 <= w <= 2000:
                    self.settings["preview_width"] = w
                self.hpane.forget(self.pv)
            self.preview_gen += 1  # drop any preview still being computed
        self._save_settings()

    def _pv_configure(self, event):
        wrap = max(150, event.width - 16)
        for lab in (self.pv_name, self.pv_path, self.pv_extra):
            lab.configure(wraplength=wrap)
        if self._pv_kind == "image":  # refit the thumbnail after the pane was resized
            if self._pv_resize_after:
                self.after_cancel(self._pv_resize_after)
            self._pv_resize_after = self.after(400, self._pv_refit)

    def _pv_refit(self):
        self._pv_resize_after = None
        box = self._pv_box_size()
        if self._pv_kind == "image" and self._pv_box and (
                abs(box[0] - self._pv_box[0]) > 30 or abs(box[1] - self._pv_box[1]) > 30):
            self._preview_request()

    def _pv_box_size(self):
        self.update_idletasks()
        return (max(120, self.pv_body.winfo_width() - 8), max(120, self.pv_body.winfo_height() - 8))

    def _pv_set_text(self, text):
        self.pv_img.pack_forget()
        self.pv_img.configure(image="")
        self._pv_photo = None
        self.pv_textf.pack(fill="both", expand=True)
        self.pv_text.configure(state="normal")
        self.pv_text.delete("1.0", "end")
        self.pv_text.insert("1.0", text)
        self.pv_text.configure(state="disabled")

    def _pv_clear(self, text):
        self._pv_path = None
        self._pv_kind = None
        for v in (self.v_pv_name, self.v_pv_path, self.v_pv_info, self.v_pv_extra):
            v.set("")
        self.pv_b_open.configure(state="disabled")
        self.pv_b_reveal.configure(state="disabled")
        self._pv_set_text(text)

    def _on_tree_select(self, event=None):
        if not self.v_preview.get():
            return
        if self._pv_after:
            self.after_cancel(self._pv_after)
        self._pv_after = self.after(150, self._preview_request)

    def _preview_request(self):
        """Show the header now; compute the body in a worker thread (stale results are dropped)."""
        self._pv_after = None
        if not self.v_preview.get():
            return
        self.preview_gen += 1
        gen = self.preview_gen
        sel = self._selected()
        if len(sel) != 1:
            if sel:
                size = sum(r[3] or 0 for r in sel if not r[5])
                self._pv_clear(f"{len(sel):,} items selected ({human_size(size)} in files).\n\n"
                               "Select a single item to preview it.")
            else:
                self._pv_clear("Select a result to preview it.")
            return
        r = sel[0]
        path = self._full(r)
        self._pv_path = path
        self.v_pv_name.set(("📁 " if r[5] else "") + r[1])
        self.v_pv_path.set(path)
        self.v_pv_info.set("Folder" + (f"  ·  modified {self.fmt_time(r[4])}" if r[4] else "") if r[5]
                           else f"{human_size(r[3] or 0)}  ·  modified {self.fmt_time(r[4])}")
        self.v_pv_extra.set("")
        self.pv_b_open.configure(state="normal")
        self.pv_b_reveal.configure(state="normal")
        box = self._pv_box_size()
        self._pv_box = box
        self._pv_kind = "loading"
        self._pv_set_text("Loading preview…")
        args = (path, bool(r[5]), (r[2] or "").lower(), r[3] or 0, box, self.pdftotext)

        def work():
            p = build_preview(*args)
            self.q.put(("preview", gen, p))

        threading.Thread(target=work, daemon=True).start()

    def _preview_show(self, p):
        extra = list(p.get("extra") or [])
        if p.get("taken"):
            extra.insert(0, "Taken " + self.fmt_time(p["taken"]))
        self.v_pv_extra.set("  ·  ".join(extra))
        self._pv_kind = p["kind"]
        if p["kind"] == "image" and p.get("image") is not None:
            try:
                photo = pil_modules()[2].PhotoImage(p["image"])
            except Exception as ex:
                self._pv_kind = "info"
                self._pv_set_text(f"Cannot show this image: {ex}")
                return
            self.pv_textf.pack_forget()
            self._pv_photo = photo  # keep a reference or Tk shows nothing
            self.pv_img.configure(image=photo)
            self.pv_img.pack(fill="both", expand=True)
        else:
            self._pv_set_text(p.get("text") or "")

    def _pv_open(self):
        if self._pv_path:
            try:
                os.startfile(self._pv_path)
            except OSError as ex:
                messagebox.showerror(APP, f"Could not open:\n{self._pv_path}\n\n{ex}")

    def _pv_reveal(self):
        if self._pv_path:
            subprocess.Popen(f'explorer /select,"{self._pv_path}"')

    # ---- duplicates
    def open_duplicates(self):
        if self.dup_window is not None and self.dup_window.winfo_exists():
            self.dup_window.lift()
            self.dup_window.focus_set()
            return
        self.dup_window = DupWindow(self)

    # ---- deleting
    def _index_locations(self, full):
        """[(db, rel)] for every known index whose root contains the absolute path full."""
        out = []
        for root in self._known_roots():
            if path_in(full, root):
                rel = rel_to(full, root)
                if rel:
                    out.append((db_path_for(root), rel))
        return out

    def _folder_content_info(self, full):
        """(item count, total bytes) inside a folder according to the index, or (None, None)."""
        locs = self._index_locations(full)
        if not locs:
            return None, None
        db, rel = locs[0]
        f = fold(rel)
        try:
            con = sqlite3.connect(db, timeout=5)
            try:
                return con.execute("SELECT COUNT(*), COALESCE(SUM(size), 0) FROM files "
                                   "WHERE fpath LIKE ? ESCAPE '\\'", (like_escape(f + "\\") + "%",)).fetchone()
            finally:
                con.close()
        except sqlite3.Error:
            return None, None

    def _busy(self, on):
        # (set the cursor through Tcl directly)
        try:
            self.tk.call(self._w, "configure", "-cursor", "watch" if on else "")
            self.update_idletasks()
        except tk.TclError:
            pass

    def delete_selected(self):
        try:
            self._delete_selected()
        except Exception as ex:  # never let a delete problem crash the app
            self._busy(False)
            messagebox.showerror(APP, f"Delete failed:\n{ex}")

    def _delete_selected(self):
        sel = self._selected()
        if not sel:
            self.v_status.set("Select one or more results to delete (Ctrl/Shift+click, Ctrl+A).")
            return
        # unique items; children of selected folders are handled by their folder
        by_key = {}
        for r in sel:
            by_key.setdefault(os.path.normcase(os.path.normpath(self._full(r))), r)
        dir_prefixes = tuple(k + os.sep for k, r in by_key.items() if r[5])
        items = [(k, r) for k, r in sorted(by_key.items()) if not (dir_prefixes and k.startswith(dir_prefixes))]
        inside = len(by_key) - len(items)
        rows = [r for _, r in items]
        paths = [self._full(r) for r in rows]
        files = [r for r in rows if not r[5]]
        dirs = [r for r in rows if r[5]]
        fsize = sum(r[3] or 0 for r in files)

        parts = []
        if files:
            parts.append(f"{len(files):,} file(s) ({human_size(fsize)})")
        if dirs:
            parts.append(f"{len(dirs):,} folder(s)")
        msg = "Delete " + " and ".join(parts) + "?\n\n" + "\n".join(paths[:10])
        if len(paths) > 10:
            msg += f"\n… and {len(paths) - 10:,} more"
        if inside:
            msg += f"\n\n({inside:,} selected item(s) are inside selected folders and go with them.)"
        if dirs:
            n_in = s_in = 0
            known = True
            for d in dirs:
                n, s = self._folder_content_info(self._full(d))
                if n is None:
                    known = False
                    break
                n_in, s_in = n_in + n, s_in + s
            msg += ("\n\nWARNING: the selected folder(s) and EVERYTHING inside them will be deleted"
                    + (f" (about {n_in:,} items, {human_size(s_in)}, according to the index)." if known else "."))
        if not self._confirm_delete(msg, len(rows), bool(dirs), paths):
            self.v_status.set("Delete cancelled.")
            return
        recycle = self._drive_check(paths)[0]
        todo, failures = self._recycle(paths, recycle, self)

        gone = [r for r, p in zip(rows, paths) if not os.path.lexists(p)]
        removed = self._remove_from_index(gone)
        self._remove_from_results(gone)
        self.readme_cache = None
        self._show_index_status()
        done = len([p for p in todo if not os.path.lexists(p)])
        status = (f"Moved {done:,} item(s) to the Recycle Bin" if recycle
                  else f"Deleted {done:,} item(s) permanently")
        if len(gone) > done:
            status += f" · {len(gone) - done:,} were already missing"
        if failures:
            status += f" · {len(failures):,} failed"
        if removed is None:
            status += " · index not updated - use Rebuild index"
        elif self.indexing:
            status += " · indexing is running - rebuild again afterwards"
        self.v_status.set(status + ".")
        if failures:
            self._show_failures(failures, self)

    def _show_failures(self, failures, parent):
        lines = [f"{p}\n    → {why}" for p, why in list(failures.items())[:20]]
        if len(failures) > 20:
            lines.append(f"… and {len(failures) - 20:,} more")
        messagebox.showwarning(APP + " - delete", f"{len(failures):,} item(s) could not be deleted "
                               "(in use, no permission, path too long…):\n\n" + "\n".join(lines)
                               + "\n\nIf a folder was partly deleted, use Rebuild index.", parent=parent)

    def _drive_check(self, paths):
        """(recycle_ok, text) - recycle_ok is False when any path is on a drive that is not a
        fixed local disk (removable / network…), where Windows may delete permanently."""
        bad = {}
        for p in paths:
            drive = os.path.splitdrive(os.path.abspath(p))[0] or p
            k = drive.upper()
            if k not in bad:
                bad[k] = (drive, drive_type(p))
        bad = [(d, t) for d, t in bad.values() if t != DRIVE_FIXED]
        return not bad, ", ".join(f"{d} is a {DRIVE_TYPES.get(t, 'unknown')} drive" for d, t in bad)

    def _confirm_delete(self, msg, count, has_dirs, paths, parent=None):
        """The delete confirmations (default No): main question, 'really sure' above 50 items,
        and an extra PERMANENT-deletion question for drives without a Recycle Bin."""
        parent = parent or self
        recycle, drives = self._drive_check(paths)
        if recycle:
            msg += "\n\nThe items go to the Recycle Bin and can be restored from there."
        else:
            msg += f"\n\nNOTE: {drives} - the Recycle Bin may not apply, deletion may be PERMANENT."
        if not messagebox.askyesno(APP + " - delete", msg, icon="warning", default="no", parent=parent):
            return False
        if count > 50 and not messagebox.askyesno(
                APP + " - delete", f"You are about to delete {count:,} items"
                + (" (including folders with all their contents)" if has_dirs else "")
                + ".\n\nAre you really sure?", icon="warning", default="no", parent=parent):
            return False
        if not recycle and not messagebox.askyesno(
                APP + " - PERMANENT delete",
                f"PERMANENT DELETION\n\n{drives}. Windows "
                "usually has no Recycle Bin there, so these items will be deleted PERMANENTLY and "
                "cannot be restored.\n\nDelete them permanently anyway?", icon="warning", default="no",
                parent=parent):
            return False
        return True

    def _recycle(self, paths, recycle, window):
        """Send existing paths to the Recycle Bin. Returns (attempted_paths, {path: reason})."""
        todo = [p for p in paths if os.path.lexists(p)]  # already-missing items just leave the index
        failures = {}
        if todo:
            self.v_status.set(f"Deleting {len(todo):,} item(s)…")
            self._busy(True)
            self.update_idletasks()
            try:
                hwnd = int(window.wm_frame(), 16)
            except (tk.TclError, ValueError):
                hwnd = 0
            try:
                rc, aborted = shell_recycle(todo, hwnd, nuke_warning=recycle)
                left = [p for p in todo if os.path.lexists(p)]
                if left and len(todo) > 1 and not aborted:
                    for p in left:  # retry one by one to learn why each item failed
                        rc, ab = shell_recycle([p], hwnd, nuke_warning=recycle)
                        if os.path.lexists(p):
                            failures[p] = "cancelled" if ab and not rc else (sh_error_text(rc) if rc else "still exists")
                else:
                    for p in left:
                        failures[p] = "cancelled" if aborted and not rc else (sh_error_text(rc) if rc else "still exists")
            finally:
                self._busy(False)
        return todo, failures

    def _remove_from_index(self, rows):
        """Drop deleted rows (and descendants of deleted folders) from every index that lists
        them (rows may come from any root). Returns count or None if an index could not be updated."""
        if not rows:
            return 0
        by_db = collections.defaultdict(list)
        for r in rows:
            for db, rel in self._index_locations(self._full(r)):
                by_db[db].append((rel, r[5]))
        total, failed = 0, False
        for db, items in by_db.items():
            try:
                con = sqlite3.connect(db, timeout=5)
                try:
                    n = 0
                    for rel, isdir in items:
                        f = fold(rel)
                        n += con.execute("DELETE FROM files WHERE rel = ?", (rel,)).rowcount
                        if isdir:
                            n += con.execute("DELETE FROM files WHERE (fpath = ? OR fpath LIKE ? ESCAPE '\\') "
                                             "AND substr(rel, 1, ?) = ?",
                                             (f, like_escape(f + "\\") + "%", len(rel) + 1, rel + "\\")).rowcount
                    if n:
                        con.execute("UPDATE meta SET v = CAST(MAX(0, CAST(v AS INTEGER) - ?) AS TEXT) "
                                    "WHERE k = 'count'", (n,))
                    con.commit()
                    total += n
                finally:
                    con.close()
            except sqlite3.Error:
                failed = True
        return None if failed else total

    def _remove_from_results(self, rows):
        """Remove rows (matched by full path; folders take their contents) from the result list."""
        if not rows:
            return
        keys = [os.path.normcase(os.path.normpath(self._full(r))) for r in rows]
        gone = set(keys)
        prefixes = tuple(k + os.sep for k, r in zip(keys, rows) if r[5])

        def is_gone(r):
            k = os.path.normcase(os.path.normpath(self._full(r)))
            return k in gone or (bool(prefixes) and k.startswith(prefixes))

        for iid, r in list(self.row_by_iid.items()):
            if is_gone(r):
                if self.tree.exists(iid):
                    self.tree.delete(iid)
                del self.row_by_iid[iid]
        self.rows = [r for r in self.rows if not is_gone(r)]
        self.pending = [r for r in self.pending if r[0] == "__done__" or not is_gone(r)]

    def browse_scope(self):
        d = filedialog.askdirectory(initialdir=os.path.join(self.root_dir, self.v_scope.get()),
                                    title="Search only inside…")
        if not d:
            return
        d = os.path.abspath(d)
        root = os.path.abspath(self.root_dir)
        if self.v_allroots.get():  # absolute folder inside any of the roots
            if any(path_in(d, r) for r in self._all_roots()):
                self.v_scope.set(d)  # a root itself = search only that root
                self.search()
            else:
                messagebox.showinfo(APP, "That folder is not inside any of the roots. Add it with 'Roots…'.")
            return
        if os.path.normcase(d) == os.path.normcase(root):
            self.v_scope.set("")
        elif os.path.normcase(d).startswith(os.path.normcase(root) + os.sep):
            self.v_scope.set(d[len(root) + 1:])
        else:
            messagebox.showinfo(APP, "That folder is outside the indexed root. Use 'Change root…' instead.")
            return
        self.search()

    def export_csv(self):
        if not self.rows:
            messagebox.showinfo(APP, "There are no results to export.")
            return
        p = filedialog.asksaveasfilename(defaultextension=".csv", filetypes=[("CSV", "*.csv")],
                                         initialfile="search results.csv")
        if not p:
            return
        with open(p, "w", newline="", encoding="utf-8-sig") as f:
            w = csv.writer(f)
            w.writerow(["full path", "name", "type", "size bytes", "modified", "match in file"])
            for rel, name, ext, size, mtime, isdir, snip in self.rows:
                w.writerow([os.path.join(self.root_dir, rel), name, "folder" if isdir else ext, size,
                            self.fmt_time(mtime), snip])
        self.v_status.set(f"Exported {len(self.rows):,} rows to {p}")

    def show_help(self):
        """Help text in a small scrollable window (it no longer fits in a message box)."""
        win = tk.Toplevel(self)
        win.title(APP + " - help")
        win.geometry("640x620")
        win.transient(self)
        txt = tk.Text(win, wrap="word", font=("Consolas", 9), padx=10, pady=8, relief="flat")
        sb = ttk.Scrollbar(win, orient="vertical", command=txt.yview)
        txt.configure(yscrollcommand=sb.set)
        ttk.Button(win, text="Close", command=win.destroy).pack(side="bottom", pady=6)
        sb.pack(side="right", fill="y")
        txt.pack(side="left", fill="both", expand=True)
        txt.insert("1.0", self._help_text())
        txt.configure(state="disabled")
        win.bind("<Escape>", lambda e: win.destroy())
        win.focus_set()

    def _help_text(self):
        return ((
            "QUERY\n"
            "  crane remote        both words must appear\n"
            "  \"uzaktan kumanda\"   exact phrase\n"
            "  pic -pdf            exclude a word\n"
            "  *.asm  or  ext:asm,s   by extension\n"
            "  2008*dugun           * and ? are wildcards\n"
            "  Case and Turkish accents are ignored (vinc = Vinç).\n\n"
            "MATCH IN\n"
            "  File name - only the file/folder name.\n"
            "  Name + folder path - words may be in any parent folder too\n"
            "    (e.g. 'project box dxf').\n"
            "  File contents - looks inside text/code files (asm, c, bas,\n"
            "    txt, html…) and optionally PDFs. Press Enter to start.\n\n"
            "FILTERS  Type, Look in (folder), size in MB, and Modified date:\n"
            "  pick a preset (Today, Last 7 days, This month, Last year…), click 📅\n"
            "  to choose a day (or 'Whole month') on a calendar, or type From / To as\n"
            "  2008, 2008-06, 2008-06-15, 06.2008 or 15.06.2008.\n"
            "  To is inclusive: From 03.2008 To 06.2008 = March through June 2008.\n\n"
            "SORT  Best match / Newest / Oldest / Name / Size / Folder - applied to\n"
            "  ALL matches before Max results cuts the list. The status line shows\n"
            "  'N of M matches' when more exist than are shown.\n\n"
            "RESULTS  Double-click opens · right-click for Explorer / copy path /\n"
            "  search inside folder · click a column header to sort.\n"
            "  Ctrl/Shift+click selects several · Ctrl+A selects all ·\n"
            "  Ctrl+C copies paths · Enter opens.\n\n"
            "DELETE  Del key or right-click > Delete… removes the selected files\n"
            "  and folders after a confirmation. They go to the Recycle Bin\n"
            "  (restore them from there). On removable / network drives there\n"
            "  is no Recycle Bin - you get an extra PERMANENT-delete warning.\n\n"
            "PREVIEW  (checkbox at the top) shows the selected item on the right:\n"
            "  image thumbnail + EXIF date (needs Pillow), the start of text/code\n"
            "  files, page 1 of a PDF, the contents of a folder. Drag the divider\n"
            "  to resize it.\n\n"
            "README HINTS  lines of the README knowledge map that mention your\n"
            "  words. Double-click one to search only inside that folder.\n\n"
            "SEVERAL ROOTS  'Roots…' lists the indexed folders (add / remove;\n"
            "  adding one indexes it). Tick 'Search all roots' to search all of\n"
            "  them at once: Folder shows the full path, Sort and Max results apply\n"
            "  to the merged list, Look in takes a full folder path (a short name\n"
            "  means a folder of the current root). 'Rebuild index' then rebuilds\n"
            "  every root, one after the other.\n\n"
            "DUPLICATES  'Find duplicates…' compares files of the current root (or\n"
            "  of all roots) within the Type, Look in, Size and Modified filters:\n"
            "  same size, then same first 64 KB, then same full content (BLAKE2b).\n"
            "  Quick mode compares only the first + last 1 MB. Use the 'Select all\n"
            "  but …' buttons or Ctrl/Shift+click, then 'Delete selected' - the last\n"
            "  copy of a group is never deleted.\n\n"
            "INDEX  Auto-refresh (bottom right) rebuilds the index in the background\n"
            "  when it is older than the chosen interval (default: Daily); searching\n"
            "  keeps working meanwhile. With 'Search all roots' on, the other roots'\n"
            "  indexes are refreshed too, one at a time. 'Rebuild index' refreshes\n"
            "  immediately."))

    def _on_close(self):
        self.cancel.set()
        self.index_cancel.set()
        if self.dup_window is not None:
            self.dup_window.cancel.set()
        self._save_settings()
        self.destroy()


if __name__ == "__main__":
    App().mainloop()
