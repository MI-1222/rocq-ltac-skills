# Falsification, Disproof & Tactic Thrashing

This reference provides a systematic 3-phase Falsification Protocol to break out of tactic thrashing loops when an intermediate conjecture or helper lemma is suspected of being false in Rocq 9.0+ and Coq 8.20.

---

## 1. Error Signatures

### Signature A: Tactic Thrashing Loop

```text
(* Attempt 1: induction n; simpl; auto. -> Goal unchanged *)
(* Attempt 2: destruct n; try reflexivity. -> Goal unchanged *)
(* Tactic budget exhausted: Proof state did not evolve over 2 edits *)
```

The agent repeatedly alternates tactics (`simpl`, `auto`, `intuition`, `eauto`) without reducing open subgoals.

### Signature B: Counterexample Encountered

```text
Goal: False
(* or 1 = 2, or false = true *)
```

An intermediate step reduced the goal to a provably false proposition, indicating that the premise does not imply the conclusion.

---

## 2. Root Cause & Theoretical Background

1. **The Pathology of False Conjectures**:
   During autonomous proof search, agents frequently assert intermediate helper lemmas (`assert (H : P)`). If the helper proposition $P$ is false (or under-constrained), no sequence of sound tactics can complete the proof. Continuing to guess tactics wastes compute and tokens indefinitely.
2. **Goal Drift Boundary**:
   While top-level theorem statements are immutable (**Header Fence Rule**), intermediate helper lemmas asserted by the agent _can_ and _must_ be corrected or discarded.
3. **The 3-Phase Falsification Protocol**:
   - **Phase 1 (Compute Gate)**: Test the proposition on minimal boundary instances ($0, 1, 2$, `[]`, `[x]`, `true`, `false`).
   - **Phase 2 (Refutation Lemma)**: Attempt to formally prove $\neg P$ on a specific concrete counterexample.
   - **Phase 3 (Precondition Strengthening)**: If a counterexample exists, reformulate the lemma by adding the missing prerequisite constraint.

---

## 3. Anti-Patterns to Avoid

- ❌ **Altering the top-level theorem statement**: Never weaken the main theorem statement (e.g., adding `False ->` or changing conclusion). Only helper lemmas may be modified.
- ❌ **Ignoring stationary goal states**: Continuing to edit tactics after two attempts produced the exact same AST representation.
- ❌ **Blindly assuming helper lemmas are sound**: Always sanity-check self-invented lemmas on edge cases before investing in multi-step inductive proofs.

---

## 4. Concrete Prescriptions (Before & After)

### Phase 1: Boundary Value Testing via `Compute`

Suppose the agent formulates this flawed conjecture:

```Coq
(* Conjecture: List reversal preserves the head element *)
Definition flawed_prop (l : list nat) : Prop :=
  match l with
  | [] => True
  | x :: _ => hd 0 (rev l) = x
  end.
```

Before proving `forall l, flawed_prop l`, test on boundary inputs:

```Coq
From Stdlib Require Import List.
Import ListNotations.

(* Test on empty list: *)
Compute (flawed_prop []).
(* = True : Prop *)

(* Test on two-element list [1; 2]: *)
Compute (hd 0 (rev [1; 2])).
(* = 2 : nat *)
(* Clearly 2 <> 1, so flawed_prop [1; 2] is false! *)
```

Conclusion: The conjecture is false for lists with length $\ge 2$.

---

### Phase 2: Formulating a Refutation Lemma

If an intermediate asserted lemma `H : forall a b, a - b = b - a` is suspected of being false:

**Failing Code (Thrashing on False Proposition):**

```Coq
Lemma test_sub_comm : forall a b : nat, a - b = b - a.
Proof.
  intros a b.
  induction a; simpl.
  (* Endless thrashing trying to prove 0 = b - 0 for all b *)
Abort.
```

**Refutation Action (Formal Counterexample):**

```Coq
Lemma sub_not_comm : ~ (forall a b : nat, a - b = b - a).
Proof.
  intro H.
  (* Specialize on concrete counterexample values: a = 1, b = 0 *)
  specialize (H 1 0).
  simpl in H.
  (* H reduces to: 1 = 0 *)
  discriminate H.
Qed.
```

Once refutation succeeds, the flawed helper lemma is discarded entirely.

---

### Phase 3: Precondition Strengthening

When a conjecture fails only at specific boundary cases, identify the missing constraint and strengthen the premise:

**Failing Code (Under-Constrained Lemma):**

```Coq
(* Fails when n = 0, because 0 / 2 = 0 which is not strictly less than 0 *)
Lemma div2_strictly_less : forall n, Nat.div2 n < n.
Abort.
```

**Repaired Code (Strengthened Precondition):**

```Coq
From Stdlib Require Import Arith.
From Stdlib Require Import Lia.

Lemma div2_strictly_less : forall n, n > 0 -> Nat.div2 n < n.
Proof.
  intros n Hpos.
  destruct n as [| n'].
  - lia. (* Contradiction with n > 0 *)
  - apply Nat.lt_div2; lia.
Qed.
```

---

## 5. Fallback Procedures

1. **Discarding the Intermediate Assertion**:
   If a helper lemma cannot be proved and cannot be easily repaired by preconditions, abandon that proof branch:
   ```Coq
   (* Replace flawed assertion with a direct proof or a different lemma *)
   ```
2. **Testing with QuickChick (When Available)**:
   If QuickChick is installed in the project environment, run property-based tests via `rocq_goal.py`:
   ```bash
   python3 skills/rocq-ltac-interactive-proof/scripts/rocq_goal.py --file <file.v> --line <N> --search "QuickCheck prop_to_test"
   ```
3. **Decomposing into Case-Specific Sub-Lemmas**:
   Instead of asserting an overly general proposition `forall x, P x`, split into separate lemmas for distinct constructors:
   - `Lemma P_zero : P 0.`
   - `Lemma P_succ : forall n, P (S n).`
