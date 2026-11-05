# Tactic Automation Failures (`lia`, `congruence`, `match goal`)

This reference provides techniques to diagnose and repair automated decision procedure breakdowns (`lia`, `nia`, `congruence`, `tauto`) and Ltac pattern-matching failures in Rocq 9.0+ and Coq 8.20.

---

## 1. Error Signatures

### Signature A: Presburger / Linear Arithmetic Failure

```text
Error: Cannot solve goal with lia.
```

The goal involves natural number subtraction underflow ($a - b = 0$ for $a \le b$), non-linear multiplication, or untranslated data types.

### Signature B: Congruence / Tauto Failure

```text
Error: congruence failed.
```

or

```text
Error: tauto failed.
```

The goal cannot be solved by pure ground equality, constructor distinctness, or intuitionistic propositional logic without term unfolding or case analysis.

### Signature C: Ltac Pattern Match Failure

```text
Error: No matching clauses for match goal.
```

A custom Ltac macro executed a `match goal with ... end` block where no pattern clause matched the current proof state, or an unhandled failure propagated out of a matching clause.

---

## 2. Root Cause & Theoretical Background

1. **`lia` and Truncated Natural Subtraction**:
   `lia` internally translates terms into linear integer arithmetic ($\mathbb{Z}$). On natural numbers (`nat`), subtraction is truncated: $a - b = 0$ whenever $a \le b$.
   - Because $a - b$ is piecewise linear, `lia` must introduce case distinctions for every occurrence of $-$, causing combinatorial blowup or failing when hypotheses bounding the operands are absent.
   - Non-linear terms (like $a \times b$ where neither $a$ nor $b$ is a constant) are treated by `lia` as uninterpreted variables.
2. **`zify` Preprocessing**:
   Rocq's `lia` tactic runs a preprocessing hook called `zify` that converts `nat`, `N`, and `positive` into $\mathbb{Z}$. Custom types, boolean comparisons, or user functions will not be recognized unless registered with `zify` or explicitly rewritten.
3. **Ltac Failure Levels (`fail 0` vs. `fail 1`)**:
   In Ltac's `match goal with ... end`:
   - If a tactic in a branch fails with level 0 (`fail 0` or standard failure like `discriminate`), Ltac backtracks to the next matching clause or permutation of hypotheses.
   - If a branch fails with level 1 or higher (`fail 1`), or if no pattern matches, the entire `match goal` aborts with `No matching clauses`.

---

## 3. Anti-Patterns to Avoid

- ❌ **Calling removed legacy tactics (`omega`, `romega`, `sos`)**: These tactics were removed in Coq 8.14+ and are fatal syntax errors in Rocq 9.0+. Always import `Lia` and use `lia`.
- ❌ **Calling `lia` on unbounded `nat` subtraction**: Expecting `lia` to deduce $a \le b$ from $a - b = 0$ without a case split.
- ❌ **Brittle Ltac `match goal` without fallback**: Omitting a default clause `| _ => idtac`, causing automated proof loops to abort unrecoverably.

---

## 4. Concrete Prescriptions (Before & After)

### Case 1: Natural Subtraction Underflow in `lia`

**Failing Code (Before):**

```Coq
From Stdlib Require Import Lia.

Lemma nat_sub_zero_le : forall a b : nat, a - b = 0 -> a <= b.
Proof.
  intros a b H.
  (* Fails: Cannot solve goal with lia *)
  lia.
Qed.
```

**Repaired Code (After):**

```Coq
From Stdlib Require Import Lia.
From Stdlib Require Import Arith.

Lemma nat_sub_zero_le : forall a b : nat, a - b = 0 -> a <= b.
Proof.
  intros a b H.
  destruct (Nat.le_gt_cases a b) as [Hle | Hgt].
  - exact Hle.
  - exfalso.
    (* When a > b, a - b is strictly positive in nat *)
    assert (Hpos : a - b > 0) by lia.
    lia.
Qed.
```

---

### Case 2: Non-Linear Arithmetic with `nia`

**Failing Code (Before):**

```Coq
From Stdlib Require Import Lia.

Lemma sq_pos : forall x : nat, 0 <= x * x.
Proof.
  intros x.
  (* Fails: Cannot solve goal with lia because x * x is non-linear *)
  lia.
Qed.
```

**Repaired Code (After):**

```Coq
From Stdlib Require Import Lia.

Lemma sq_pos : forall x : nat, 0 <= x * x.
Proof.
  intros x.
  nia. (* Non-linear integer arithmetic tactic *)
Qed.
```

---

### Case 3: Robust Ltac Pattern Matching with Fallbacks

**Failing Code (Before):**

```Coq
Ltac solve_equalities :=
  match goal with
  | [ H : ?x = ?y |- ?y = ?x ] => symmetry; exact H
  end.
(* Fails with "No matching clauses for match goal" if target is not a simple symmetry *)
```

**Repaired Code (After):**

```Coq
Ltac solve_equalities :=
  repeat match goal with
  | [ H : ?x = ?y |- ?y = ?x ] => symmetry; exact H
  | [ H : ?x = ?y |- _ ] => subst x || subst y
  | _ => idtac (* Graceful fallback: terminates without raising fatal error *)
  end.
```

Use `lazymatch goal` when backtracking over alternative hypothesis bindings is not desired, and use `try lia` when chaining tactics.

---

### Case 4: Preprocessing with `zify` for Custom Arithmetic Predicates

When reasoning about boolean comparisons or relations that `lia` does not recognize natively:

```Coq
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.

Lemma leb_trans : forall x y z : nat,
  (x <=? y) = true -> (y <=? z) = true -> (x <=? z) = true.
Proof.
  intros x y z H1 H2.
  (* Convert boolean comparisons to Prop inequalities using zify *)
  zify.
  lia.
Qed.
```

---

## 5. Fallback Procedures

1. **Isolating Non-Linear Factors with `remember`**:
   If `nia` fails on complex polynomial terms, abstract the non-linear subterm into a variable:
   ```Coq
   remember (f x * g y) as k eqn:Heqk.
   (* Now k is treated as a linear variable by lia *)
   ```
2. **Injectivity & Disjointness with `congruence`**:
   If `congruence` fails because constructor arguments are hidden behind definitions:
   ```Coq
   unfold my_constructor_alias in *.
   congruence.
   ```
3. **Manual Arithmetic Lemmas**:
   When automation cannot close the goal, apply standard lemmas from `Nat` or `Z`:
   - `apply Nat.mul_le_mono_pos_l; lia.`
   - `rewrite Nat.add_comm, Nat.add_assoc.`
