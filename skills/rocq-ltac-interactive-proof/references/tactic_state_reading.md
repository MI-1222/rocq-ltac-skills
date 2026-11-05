# Tactic Proof State Reading & Diagnostics Guide

This reference provides detailed technical specifications for parsing, interpreting, and troubleshooting proof engine outputs returned by Rocq (formerly Coq) during interactive proof sessions.

---

## 1. Anatomy of the Rocq Proof State

When running `rocq_goal.py` or inspecting standard REPL outputs, the proof state is organized into structured blocks:

```text
2 goals

  n : nat
  m : nat
  H : n <= m
  ============================
  n + 0 <= m + 0

goal 2 is:
  m <= n -> False
```

### Key Components

1. **Subgoal Counter**:
   - `1 goal` or `N goals` (or legacy `N subgoals`).
   - Indicates how many unsolved leaf branches exist in the current proof tree.
2. **Local Context (Hypotheses Block)**:
   - Lines above the horizontal line `============================`.
   - Contains introduced variables, hypotheses, and local definitions (e.g., `n : nat`, `H : n <= m`, `k := 2 : nat`).
3. **Separator Line**:
   - A sequence of at least 10 consecutive equals signs (`============================`).
   - Separates in-scope hypotheses from the target formula.
4. **Focused Goal (Target Conclusion)**:
   - The expression immediately below the separator line (`n + 0 <= m + 0`).
   - Tactics applied next operate directly on this focused goal and its context.
5. **Pending Background Subgoals (`goal 2 is:`)**:
   - Lists targets of subsequent open branches.
   - Note: In modern Rocq 9.0+, background goals are prefixed with `goal N is:` (in older Coq versions: `subgoal N is:`).

---

## 2. Multi-Goal Ordering & Scope Tracking

When tactics like `destruct`, `split`, or `induction` generate multiple subgoals, Rocq pushes them onto the proof stack:

- **First Subgoal**: Automatically becomes the active focused goal. Its full hypotheses context and target are displayed above and below the separator line.
- **Subsequent Subgoals**: Listed concisely at the bottom as `goal 2 is: ...`, `goal 3 is: ...`. Their hypotheses are hidden until they become focused.
- **Focusing Disciplines**:
  - Use bullets (`-`, `+`, `*`) or curly braces (`{ ... }`) to focus subgoals one at a time.
  - When the first branch is solved (`reflexivity.`), Rocq automatically pops and focuses the next subgoal on the stack.

---

## 3. Existential Variables (Evars) Pitfalls & Prevention

An Existential Variable (Evar, rendered as `?X`, `?Goal`, or `?a`) represents a hole in a Gallina term that Rocq's typechecker has deferred for later instantiation.

### The Evar Hazard

Uncontrolled application of tactics like `eapply`, `econstructor`, or `eexists` introduces Evars:

```text
1 goal
  A : Type
  x : A
  ============================
  ?y = x
```

If an Evar remains uninstantiated when closing a proof with `Qed.`, Rocq rejects the proof with a fatal error:

```text
Error: Attempt to save an incomplete proof (uninstantiated existential variables).
```

### Prevention & Remediation

1. **Prefer Explicit Tactics**: Whenever possible, avoid `eapply` and supply explicit terms using `apply ... with ...` or explicit arguments:
   - ❌ **Risky**: `eapply le_trans.`
   - ✅ **Safe**: `apply Nat.le_trans with (m := k).`
2. **Explicit Instantiation (`instantiate`)**: If an Evar exists in the goal, instantiate it directly:
   ```coq
   instantiate (1 := my_term).
   ```
3. **Unification Discharge**: If another hypothesis or goal constraint forces the value of the Evar, apply that hypothesis to unify and resolve it:
   ```coq
   exact H.  (* Unifies ?y with x *)
   ```

---

## 4. Shelved Goals Resolution

When an existential variable cannot be instantiated automatically by subsequent tactics, Rocq moves the uninstantiated subterms to a background shelf rather than keeping them active.

### Detecting Shelved Goals

If `rocq_goal.py` reports `has_evar_warning: true` or the REPL displays:

```text
This subproof is complete, but there are some shelved goals.
```

the proof cannot be finalized with `Qed.`.

### Resolving Shelved Goals

- **Unshelve Background Goals**: Execute `Unshelve.` to bring all shelved goals back to the active proof stack as visible subgoals.
- **Grab Existential Variables**: Alternatively, run:
  ```coq
  Grab Existential Variables.
  ```
  This turns all uninstantiated Evars into explicit subgoals that can be closed individually.

---

## 5. REPL Error Signatures and Diagnostic Interpretation

| Error Message Pattern                                                    | Root Cause                                                                                            | Immediate Action                                                                                             |
| :----------------------------------------------------------------------- | :---------------------------------------------------------------------------------------------------- | :----------------------------------------------------------------------------------------------------------- |
| `Error: Unable to unify "?A" with "?B".`                                 | Type mismatch or incompatible constructor in `apply`, `exact`, or `reflexivity`.                      | Check lemma types using `About` or `Check`. Verify explicit arguments or try `unfold` on definitions.        |
| `Error: The reference <ident> was not found in the current environment.` | Missing module import or typo in identifier name.                                                     | Run `Locate <ident>` or check missing `From ... Require Import ...`.                                         |
| `Error: No such hypothesis: <ident>`                                     | Tactic referenced a hypothesis name that does not exist in the focused local context.                 | Inspect hypotheses in `rocq_goal.py` JSON output. Correct the variable name in `inversion`, `apply in`, etc. |
| `Error: Cannot solve a goal with existentials.`                          | `reflexivity` or automated decision procedure failed because uninstantiated Evars remain in the goal. | Instantiate the Evar with `instantiate` or supply the witness explicitly.                                    |
| `Syntax error: '.' expected after [vernac:command]`                      | Missing whitespace after a period or missing period at the end of a command.                          | Ensure the period terminator is followed by a space or newline.                                              |
| `Wrong bullet [b1]: Current bullet [b2] is not finished.`                | Previous branch was not fully solved before starting the next branch.                                 | Complete the current branch with `reflexivity.`, `lia.`, or `{ ... }`.                                       |
