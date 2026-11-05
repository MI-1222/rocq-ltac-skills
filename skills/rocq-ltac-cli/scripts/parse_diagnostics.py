#!/usr/bin/env python3
"""Compiler and build diagnostics parser for Rocq and Dune outputs.

Strips ANSI sequences and converts single-line and multi-line errors, warnings,
locations, and warning tags into structured JSON.
"""

import argparse
import json
import re
import sys
from typing import Any

ANSI_ESCAPE_PATTERN = re.compile(r"\x1B(?:[@-Z\\-_]|\[[0-?]*[ -/]*[@-~])")

LOCATION_PATTERN = re.compile(
    r'^File\s+"(?P<file>[^"]+)",\s+'
    r"(?:line\s+(?P<line>\d+)|lines\s+(?P<line_start>\d+)-(?P<line_end>\d+)),\s+"
    r"characters\s+(?P<char_start>\d+)-(?P<char_end>\d+):"
)

WARNING_TAG_PATTERN = re.compile(r"\[(?P<tag>[a-zA-Z0-9_\-]+)\]$")


def strip_ansi(text: str) -> str:
    """Remove ANSI escape sequences from text.

    Args:
        text: String containing potential ANSI codes.

    Returns:
        Cleaned plain text string.
    """
    return ANSI_ESCAPE_PATTERN.sub("", text)


def parse_diagnostics(raw_text: str) -> dict[str, Any]:
    """Parse raw compiler/Dune log text into structured diagnostics.

    Args:
        raw_text: Raw compiler stdout or stderr stream.

    Returns:
        Dictionary containing list of parsed diagnostics, total errors, and total warnings.
    """
    clean_text = strip_ansi(raw_text)
    lines = clean_text.splitlines()

    diagnostics: list[dict[str, Any]] = []
    current_entry: dict[str, Any] | None = None
    message_lines: list[str] = []

    def commit_current_entry() -> None:
        nonlocal current_entry, message_lines
        if current_entry is not None:
            full_message = "\n".join(message_lines).strip()
            current_entry["message"] = full_message

            tags = []
            for tag_match in WARNING_TAG_PATTERN.finditer(full_message):
                tags.append(tag_match.group("tag"))
            current_entry["warning_tags"] = tags

            diagnostics.append(current_entry)
            current_entry = None
            message_lines = []

    for line in lines:
        loc_match = LOCATION_PATTERN.match(line.strip())
        if loc_match:
            commit_current_entry()

            file_path = loc_match.group("file")
            if loc_match.group("line"):
                line_start = int(loc_match.group("line"))
                line_end = line_start
            else:
                line_start = int(loc_match.group("line_start"))
                line_end = int(loc_match.group("line_end"))

            char_start = int(loc_match.group("char_start"))
            char_end = int(loc_match.group("char_end"))

            current_entry = {
                "file": file_path,
                "line_start": line_start,
                "line_end": line_end,
                "char_start": char_start,
                "char_end": char_end,
                "severity": "Error",
                "message": "",
                "warning_tags": [],
            }
            continue

        if current_entry is not None:
            stripped_line = line.strip()
            if stripped_line.startswith("Warning:"):
                current_entry["severity"] = "Warning"
            elif stripped_line.startswith("Error:"):
                current_entry["severity"] = "Error"
            elif stripped_line.startswith("Anomaly:"):
                current_entry["severity"] = "Anomaly"
            message_lines.append(line)
        else:
            stripped_line = line.strip()
            if stripped_line.startswith(("Error:", "Anomaly:")):
                diagnostics.append(
                    {
                        "file": "",
                        "line_start": 0,
                        "line_end": 0,
                        "char_start": 0,
                        "char_end": 0,
                        "severity": "Error"
                        if stripped_line.startswith("Error:")
                        else "Anomaly",
                        "message": stripped_line,
                        "warning_tags": [],
                    }
                )

    commit_current_entry()

    total_errors = sum(
        1 for diag in diagnostics if diag["severity"] in ("Error", "Anomaly")
    )
    total_warnings = sum(1 for diag in diagnostics if diag["severity"] == "Warning")

    return {
        "diagnostics": diagnostics,
        "total_errors": total_errors,
        "total_warnings": total_warnings,
    }


def parse_arguments() -> argparse.Namespace:
    """Parse command line arguments.

    Returns:
        Parsed arguments namespace.
    """
    parser = argparse.ArgumentParser(
        description="Rocq and Dune compiler diagnostic log parser.",
    )
    parser.add_argument(
        "file",
        nargs="?",
        default=None,
        help="Path to log file to parse (reads from stdin if omitted).",
    )
    return parser.parse_args()


def main() -> None:
    """Main CLI entrypoint."""
    args = parse_arguments()

    if args.file:
        try:
            with open(
                args.file, "r", encoding="utf-8", errors="replace"
            ) as file_handle:
                raw_input = file_handle.read()
        except OSError as err:
            sys.stderr.write(f"Error reading file: {err}\n")
            sys.exit(1)
    else:
        raw_input = sys.stdin.read()

    result = parse_diagnostics(raw_input)
    print(json.dumps(result, indent=2, ensure_ascii=False))

    if result["total_errors"] > 0:
        sys.exit(1)
    sys.exit(0)


if __name__ == "__main__":
    main()
