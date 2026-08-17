#!/usr/bin/env python3
"""Refresh SHA256SUMS for the D12 package, excluding the checksum file."""

from __future__ import annotations

import hashlib
from pathlib import Path

HERE = Path(__file__).resolve().parent


def main() -> None:
    rows = []
    for path in sorted(HERE.rglob("*")):
        if path.is_file() and path.name != "SHA256SUMS":
            rel = path.relative_to(HERE).as_posix()
            value = hashlib.sha256(path.read_bytes()).hexdigest()
            rows.append(f"{value}  {rel}\n")
    (HERE / "SHA256SUMS").write_text(
        "".join(rows), encoding="ascii", newline="\n"
    )
    print(f"files={len(rows)}")


if __name__ == "__main__":
    main()
