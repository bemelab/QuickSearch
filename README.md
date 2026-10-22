# QuickSearch

Fast, detailed file search for large Windows drives and archive folders — a single Python/tkinter program.

QuickSearch indexes every file and folder name once (SQLite, stored in `%LOCALAPPDATA%\QuickSearch`), then searches hundreds of thousands of files in well under a second. The searched folders themselves are never modified unless you explicitly delete, rename, move or copy files.

## Features

- **Instant name / path search** — all words must match, `"exact phrase"`, `-exclude`, `*` / `?` wildcards, `ext:pdf,docx`, optional regex. Case- and Turkish-accent-insensitive (`vinc` finds `Vinç`, `dugun` finds `DÜĞÜN`).
- **File-contents search** — inside text and source files (asm, c, bas, py, html, …), Word / Excel / PowerPoint, OpenDocument, RTF and optionally PDFs (via `pdftotext`), with the matching text shown.
- **Content index (full text)** — a per-root SQLite FTS5 index (`index_<hash>_content.sqlite` next to the name index) of text/code files, PDFs (all pages), `docx` / `xlsx` / `pptx`, `odt` / `ods` / `odp` and RTF, built in the background after indexing: incremental (only new / changed documents, deleted ones removed), low priority, cancelable, progress in the status line. *File contents* searches become instant and support whole words, `"phrases"`, `-exclude` and `prefix*` (Turkish-accent-insensitive), combined with all filters, sort, result limit and all-roots; documents not indexed yet are scanned live ("indexed + live"). Regex searches keep using the live scan. On/off in `Settings…` (default on); without FTS5 in Python's SQLite the live scan is used.
- **Live updates** — while the program runs, the searched roots are watched (`ReadDirectoryChangesW`): created / changed / renamed / moved / deleted files and folders reach the index within seconds, photo dates and the content index follow. `● live` in the status bar; "index changed – search again" when results on screen may be outdated. Drives that cannot be watched fall back to Auto-refresh; after a flood of changes the root is re-indexed in the background. On/off in `Settings…` (default on).
- **Explorer right-click menu (optional)** — `Settings…` → *Add 'QuickSearch here' to Explorer right-click menu* (asks first; per-user keys under `HKEY_CURRENT_USER\Software\Classes\Directory`, `Directory\Background` and `Drive`; *Remove it* deletes them). It starts QuickSearch with `--scope "<folder>"`: Look in is set to that folder, or — for a folder outside every root — you choose to add its whole drive or only that folder as a new root.
- **Filters** — file type, folder ("Look in"), size, and date range with presets and a calendar picker (European `dd.mm.yyyy` by default; ISO / US optional).
- **Photo "date taken"** — switch *Date* to *Taken (photos)* to filter and sort by the EXIF date of jpg / tif / png / heic photos; the dates are read in the background after indexing (incremental, cancelable; needs Pillow).
- **Sort** — best match, newest, oldest, name, size or folder; applied to all matches before the result limit, with an "N of M matches" status.
- **Search history and saved searches** — the search box drops down the last 30 searches; `☆ Save` stores the complete search (query, filters, sort, all-roots) under a name, `Saved` restores and runs it, `Manage…` renames / reorders / deletes.
- **Preview pane** — image thumbnails with EXIF "date taken", the start of text/code files, the first page of PDFs, folder contents.
- **Several roots at once** — index and search multiple drives/folders together (`Roots…`, `Search all roots`).
- **Disk space view** (`Space…`) — biggest files, biggest folders as an expandable tree (sizes include all subfolders, % of parent) and totals per type category / extension, within the current filters.
- **Duplicate finder** — groups identical files (size → BLAKE2b hash of the first 64 KB → full-file hash), helps select the extra copies, never deletes the last copy.
- **Rename / Move / Copy** — right-click (or F2) on results, files and folders; confirmation, Skip / Keep both / Overwrite for existing names, copy-then-delete between drives, failures reported without data loss, index updated.
- **Safe delete** — selected files go to the Recycle Bin after a confirmation; permanent deletion on removable/network drives is announced and confirmed separately.
- **Auto-refresh** — rebuilds stale indexes in the background (Off / every start / hourly / every 6 h / daily).
- **README hints** — if the searched folders contain `README.md` knowledge-map files, lines mentioning your search terms are shown; double-click one to search only in that folder.
- **Export** results to CSV.

## Requirements

- Windows 10/11
- Python 3.10+ (tested with 3.13) with tkinter (included in the python.org installer)
- Optional: [Pillow](https://pypi.org/project/pillow/) for image thumbnails in the preview and photo "date taken" (EXIF)
- Optional: `pdftotext` (e.g. from Git for Windows / Poppler) for PDF text search and preview

## Usage

Double-click `QuickSearch.pyw`, or create a shortcut to:

```
pythonw.exe "path\to\QuickSearch.pyw"
```

On first start the chosen root is indexed (about 15 s for ~400,000 files on a local disk). Use **Change root…** or **Roots…** to add drives, and **?** in the program for the full help.

To open QuickSearch on a folder from the command line (this is what the Explorer menu entry does):

```
pythonw.exe "path\to\QuickSearch.pyw" --scope "F:\Projects"
```

## Data and privacy

The index, the content index and settings are stored locally in `%LOCALAPPDATA%\QuickSearch`. Nothing is uploaded; the program makes no network connections. The registry is only written when you click the Explorer-menu button in `Settings…`.
