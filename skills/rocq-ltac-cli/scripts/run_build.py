#!/usr/bin/env python3
"""Safe build runner with process group isolation and deadline timeout control.

Prevents process hangs and zombie processes caused by heavily backtracking
automated proof tactics (e.g., lia, auto 10, eauto) by executing build
commands within an isolated process group and terminating the entire process
tree via SIGKILL upon timeout expiration.
"""

import argparse
import json
import os
import signal
import subprocess
import sys
from typing import Any


def kill_process_group(proc: subprocess.Popen) -> None:
    """Send SIGKILL to the entire process group of the given process.

    Args:
        proc: Target subprocess object to terminate.
    """
    try:
        if os.name == "nt":
            proc.terminate()
        else:
            pgid = os.getpgid(proc.pid)
            os.killpg(pgid, signal.SIGKILL)
    except (ProcessLookupError, PermissionError):
        pass


def execute_build(
    command: list[str],
    timeout_seconds: float,
    working_directory: str | None = None,
) -> dict[str, Any]:
    """Execute command in an isolated process group and collect outputs.

    Args:
        command: Command argument list to execute.
        timeout_seconds: Timeout threshold in seconds.
        working_directory: Working directory for command execution.

    Returns:
        Dictionary containing command, returncode, timed_out flag, stdout, and stderr.
    """
    timed_out = False
    stdout_text = ""
    stderr_text = ""
    return_code = 0

    popen_kwargs: dict[str, Any] = {
        "stdout": subprocess.PIPE,
        "stderr": subprocess.PIPE,
        "text": True,
        "cwd": working_directory,
    }

    if os.name == "nt":
        popen_kwargs["creationflags"] = subprocess.CREATE_NEW_PROCESS_GROUP
    else:
        popen_kwargs["start_new_session"] = True

    try:
        process = subprocess.Popen(command, **popen_kwargs)
        try:
            stdout_text, stderr_text = process.communicate(timeout=timeout_seconds)
            return_code = process.returncode
        except subprocess.TimeoutExpired:
            timed_out = True
            kill_process_group(process)
            stdout_text, stderr_text = process.communicate()
            return_code = 124
    except FileNotFoundError as err:
        return {
            "command": command,
            "returncode": 127,
            "timed_out": False,
            "stdout": "",
            "stderr": f"Command not found: {err}.",
        }
    except OSError as err:
        return {
            "command": command,
            "returncode": 1,
            "timed_out": False,
            "stdout": "",
            "stderr": f"Execution error: {err}.",
        }

    return {
        "command": command,
        "returncode": return_code,
        "timed_out": timed_out,
        "stdout": stdout_text,
        "stderr": stderr_text,
    }


def parse_arguments() -> argparse.Namespace:
    """Parse command-line arguments.

    Returns:
        Parsed arguments namespace.
    """
    parser = argparse.ArgumentParser(
        description="Safe build runner with process group isolation and timeout control.",
    )
    parser.add_argument(
        "--timeout",
        type=float,
        default=60.0,
        help="Command execution timeout in seconds (default: 60.0).",
    )
    parser.add_argument(
        "--cwd",
        type=str,
        default=None,
        help="Working directory for command execution.",
    )
    parser.add_argument(
        "--raw",
        action="store_true",
        help="Directly stream stdout and stderr instead of JSON output.",
    )
    parser.add_argument(
        "command",
        nargs=argparse.REMAINDER,
        help="Command and arguments to execute (specify after '--').",
    )
    return parser.parse_args()


def main() -> None:
    """Main CLI entrypoint."""
    args = parse_arguments()
    cmd = args.command
    if cmd and cmd[0] == "--":
        cmd = cmd[1:]

    if not cmd:
        sys.stderr.write("Error: No command specified to execute.\n")
        sys.exit(1)

    result = execute_build(
        command=cmd,
        timeout_seconds=args.timeout,
        working_directory=args.cwd,
    )

    if args.raw:
        if result["stdout"]:
            sys.stdout.write(result["stdout"])
        if result["stderr"]:
            sys.stderr.write(result["stderr"])
        sys.exit(result["returncode"])
    else:
        print(json.dumps(result, indent=2, ensure_ascii=False))
        sys.exit(result["returncode"])


if __name__ == "__main__":
    main()
