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

1. **Subgoal Counter Header**:
   - `1 goal` (singular, no period).
   - `N goals` (plural, no period).
   - `No more goals.` (when proof is complete, with period).
   - _Note_: Legacy Coq 8.x versions used `subgoal`/`subgoals`, but modern Rocq 9.0+ standardizes strictly on `goal`/`goals`.
2. **Local Context (Hypotheses Block)**:
   - Lines above the horizontal line.
   - Contains introduced variables, hypotheses, and local definitions (e.g., `n : nat`, `H : n <= m`, `k := 2 : nat`).
   - Long propositions wrapped across lines by indentation are normalized by `rocq_goal.py`.
3. **Goal Separator Line**:
   - Exactly **28 consecutive equals signs** (`============================`).
   - Has no leading indentation and is delimited by single newlines.
4. **Focused Goal (Target Conclusion)**:
   - The expression immediately below the separator line (`n + 0 <= m + 0`).
   - Tactics applied next operate directly on this focused goal and its context.
5. **Pending Background Subgoals (`goal N is:`)**:
   - Formatted strictly as `goal %d is:` (e.g., `goal 2 is:`).
   - In older Coq 8.16-, formatted as `subgoal %d is:`. `scripts/rocq_goal.py` parses both transparently.

---

## 2. Multi-Goal Ordering, Scope Tracking & Prompts

### Prompts in Proof Mode

- **Toplevel prompt**: `Rocq < ` (or legacy `Coq < `).
- **In-Proof prompt**: `lemma_name < ` (includes prime symbols, e.g., `lemma' < `).
- **Subgoal Focus prompt**: When focused via `{ ... }` or explicit focus, may display `lemma_name (focused) < `.
- The prompt indicates proof mode, while the goal count and hypotheses are emitted through standard output.

### Background Subgoals Navigation

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

Uncontrolled application of tactics like `eapply`, `econstructor`, or `eexists` introduces Evars. In Rocq 9.0+, active open Evars are announced as:

```text
(dependent evars: ?X : nat)
```

If an Evar remains uninstantiated when closing a proof with `Qed.`, Rocq rejects the proof with a fatal kernel error:

```text
Error: Attempt to save an incomplete proof (uninstantiated existential variables).
```

### Prevention & Remediation

1. **Prefer Explicit Tactics**: Avoid speculative `eapply`. Supply explicit witness terms using `apply ... with ...`:
   - ❌ **Risky**: `eapply le_trans.`
   - ✅ **Safe**: `apply Nat.le_trans with (m := k).`
2. **Explicit Instantiation (`instantiate`)**: If an Evar exists in the goal, instantiate it directly:
   ```coq
   instantiate (1 := my_term).
   ```
3. **Unification Discharge**: Apply a hypothesis that instantiates all unbound holes:
   ```coq
   exact H.  (* Unifies ?X *)
   ```

---

## 4. Shelved Goals & Given-up Goals Resolution

### Shelved Goals (`(shelved: N)`)

When an existential variable cannot be instantiated automatically by subsequent tactics, Rocq moves the uninstantiated subterms to a background shelf rather than keeping them active:

```text
(shelved: 1)
```

or warning:

```text
This subproof is complete, but there are some shelved goals.
```

- **Unshelve Background Goals**: Execute `Unshelve.` to bring all shelved goals back to the active proof stack as visible subgoals.
- **Grab Existential Variables**: Alternatively, run:
  ```coq
  Grab Existential Variables.
  ```
  This turns all uninstantiated Evars into explicit subgoals that can be closed individually.

### Given-Up Goals (`admit` / `give_up`)

If `admit.` or `give_up.` is executed, Rocq prints:

```text
No more goals, but there are some goals you gave up:
```

This is detected by `scripts/rocq_goal.py` as an unsound cheat state (`has_given_up_warning: true` and `soundness_violation`), preventing false positive completion.

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

---

## 6. Subterm Focusing in Massive Monadic Bind Expressions (`set`, `remember`, `pattern`)

Programs extracted from systems languages (e.g., via Charon/Aeneas from Rust) frequently yield massive monadic expressions featuring multi-stage `bind` operators (`o <- ...; ...`) and deeply nested `match` branches.

### The Attention Saturation Problem

Unfolding an extracted deserializer (such as `tlv_deserialize_record`) can produce goal expressions spanning hundreds of lines. Trying to perform global rewrites or direct `destruct` on such ASTs overwhelms the model's attention and causes unifications to misfire.

### Idiomatic Surgical Focusing Strategies

1. **Local Abstraction with `set`**:
   To temporarily collapse a noisy, irrelevant sub-chain of the monadic expression while maintaining definitional convertibility:

   ```coq
   set (rem_parser := (o <- step2; step3)).
   (* The goal now concisely displays: o <- step1; rem_parser *)
   ```

   When the outer proof obligations are discharged, restore the original term with `subst rem_parser` or `unfold rem_parser`.

2. **Branch Isolation with `remember ... as x eqn:Heqx`**:
   If an intermediate monadic operation produces an option or result that must be case-split, use `remember`:

   ```coq
   remember (slice_take_prefix u8 s len) as slice_res eqn:Hslice.
   destruct slice_res as [head_slice |].
   - (* Success branch: Hslice tracks the equality *)
   - (* None branch: contradiction or error handling *)
   ```

3. **Targeted Redex Isolation with `pattern`**:
   When multiple occurrences of an identical term appear across a massive monadic term, but you only want to rewrite or instantiate a specific occurrence:
   ```coq
   pattern (target_subterm) at 1. (* Exposes only the 1st occurrence as a lambda application *)
   ```
   This eliminates ambiguous subterm errors in `rewrite` or `apply`.
