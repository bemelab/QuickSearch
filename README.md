# QuickSearch

Fast, detailed file search for large Windows drives and archive folders — a single Python/tkinter program.

QuickSearch indexes every file and folder name once (SQLite, stored in `%LOCALAPPDATA%\QuickSearch`), then searches hundreds of thousands of files in well under a second. The searched folders themselves are never modified unless you explicitly delete files.

## Features

- **Instant name / path search** — all words must match, `"exact phrase"`, `-exclude`, `*` / `?` wildcards, `ext:pdf,docx`, optional regex. Case- and Turkish-accent-insensitive (`vinc` finds `Vinç`, `dugun` finds `DÜĞÜN`).
- **File-contents search** — inside text and source files (asm, c, bas, py, html, …) and optionally PDFs (via `pdftotext`), with the matching line shown.
- **Filters** — file type, folder ("Look in"), size, and modified-date range with presets and a calendar picker (European `dd.mm.yyyy` by default; ISO / US optional).
- **Sort** — best match, newest, oldest, name, size or folder; applied to all matches before the result limit, with an "N of M matches" status.
- **Preview pane** — image thumbnails with EXIF "date taken", the start of text/code files, the first page of PDFs, folder contents.
- **Several roots at once** — index and search multiple drives/folders together (`Roots…`, `Search all roots`).
- **Duplicate finder** — groups identical files (size → BLAKE2b hash of the first 64 KB → full-file hash), helps select the extra copies, never deletes the last copy.
- **Safe delete** — selected files go to the Recycle Bin after a confirmation; permanent deletion on removable/network drives is announced and confirmed separately.
- **Auto-refresh** — rebuilds stale indexes in the background (Off / every start / hourly / every 6 h / daily).
- **README hints** — if the searched folders contain `README.md` knowledge-map files, lines mentioning your search terms are shown; double-click one to search only in that folder.
- **Export** results to CSV.

## Requirements

- Windows 10/11
- Python 3.10+ (tested with 3.13) with tkinter (included in the python.org installer)
- Optional: [Pillow](https://pypi.org/project/pillow/) for image thumbnails in the preview
- Optional: `pdftotext` (e.g. from Git for Windows / Poppler) for PDF text search and preview

## Usage

Double-click `QuickSearch.pyw`, or create a shortcut to:

```
pythonw.exe "path\to\QuickSearch.pyw"
```

On first start the chosen root is indexed (about 15 s for ~400,000 files on a local disk). Use **Change root…** or **Roots…** to add drives, and **?** in the program for the full help.

## Data and privacy

The index and settings are stored locally in `%LOCALAPPDATA%\QuickSearch`. Nothing is uploaded; the program makes no network connections.
