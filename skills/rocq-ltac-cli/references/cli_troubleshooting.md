# Rocq CLI & Build Troubleshooting Guide

This document provides error diagnostics, root-cause analyses, and concrete recovery steps for common failure modes encountered during Rocq (formerly Coq) CLI compilation and build execution.

---

## 1. Exit Code Conventions

| Exit Code | Source                               | Meaning & Root Cause                                                         |
| :-------: | :----------------------------------- | :--------------------------------------------------------------------------- |
|  **`0`**  | Rocq / Dune                          | Successful execution.                                                        |
|  **`1`**  | `rocq compile` / `CErrors.exit_code` | User error, syntax error, type unification failure, or multiple input files. |
| **`124`** | `scripts/run_build.py`               | Command execution timed out. Process group terminated with `SIGKILL`.        |
| **`127`** | OS / Shell                           | Command binary (`rocq`, `dune`) not found on system PATH.                    |
| **`129`** | Rocq Kernel (`cErrors.ml`)           | **Anomaly**. Internal compiler bug, unhandled exception, or stack overflow.  |

---

## 2. Common Build Failures & Remedies

### 2.1. `More than one file to compile: ... and ...`

- **Source**: `toplevel/coqcargs.ml` (`add_compile`)
- **Cause**: Multiple `.v` source files were passed to a single `rocq compile` or `coqc` invocation.
- **Remedy**:
  - `rocq compile` accepts **strictly one** target file per execution.
  - Compile files individually, or execute project builds via `dune build` or `make -f Makefile.coq`.

### 2.2. `Cannot find a physical path bound to logical path ... with prefix Stdlib`

- **Cause**: Dune project targeting Rocq 9.0+ lacks `Stdlib` in its theory dependencies.
- **Remedy**:
  - Add `(theories Stdlib Corelib)` to the `(coq.theory ...)` stanza in the relevant `dune` file:
  ```lisp
  (coq.theory
   (name MyProject)
   (theories Stdlib Corelib))
  ```

### 2.3. `Cannot find a physical path bound to logical path ...`

- **Cause**: Mismatch between `_CoqProject` bindings (`-Q` / `-R`) and import statements (`From Prefix Require Import ...`), or build executed outside the project root.
- **Remedy**:
  - Ensure working directory is the project root containing `_CoqProject`.
  - If `theories/` is mapped via `-Q theories MyProject`, import modules with `From MyProject Require Import Core.`.

### 2.4. Tactic Timeout or Process Hang (Exit Code 124)

- **Cause**: Backtracking search in `lia`, `nia`, `auto 10`, `eauto with *`, or heavy unification in `dependent destruction` exceeded execution deadlines.
- **Remedy**:
  - `scripts/run_build.py` terminates the entire process group with `SIGKILL`.
  - Isolate the stalling tactic by stepping through proofs interactively via `rocq-ltac-interactive-proof` (`rocq_goal.py`).
  - Constrain search depth (e.g., `auto 3` instead of `auto 10`) or supply explicit intermediate lemmas with `assert` and `apply`.

### 2.5. Compiler Anomaly (Exit Code 129: `Anomaly: ... Please report`)

- **Cause**: Kernel stack overflow, cyclic type definitions, or internal compiler defects.
- **Remedy**:
  - Expand recursion stack limit: `ulimit -s unlimited`.
  - Simplify deeply nested recursive functions or compute tactics (`vm_compute`, `native_compute`).
  - Revert recent changes and isolate the offending vernac command.

### 2.6. `_CoqProject` Tokenization Errors

- **Error**: `Parsing_error ("Invalid value for -arg, unpaired single quote...")`
- **Cause**: Mismatched or unclosed single quote in an `-arg` line.
- **Remedy**:
  - Verify that quotes in `_CoqProject` are properly balanced:
  ```text
  # Valid format
  -arg "-w -deprecated-from-Coq -color no"
  ```
