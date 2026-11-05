# Tactic Automation Failures (`lia`, `congruence`, `match goal`)

This reference provides techniques to diagnose and repair automated decision procedure breakdowns (`lia`, `nia`, `congruence`, `tauto`) and Ltac pattern-matching failures in Rocq 9.0+ and Coq 8.20.

---

## 1. Error Signatures

### Signature A: Presburger / Linear Arithmetic Failure

```text
Error: Cannot solve goal with lia.
```

The goal involves natural number subtraction underflow ($a - b = 0$ for $a \le b$), a combinatorial explosion of case splits from `Z.max`, or uninterpreted non-linear terms.

### Signature B: Congruence / Tauto Failure

```text
Error: congruence failed.
```

or

```text
Error: tauto failed.
```

The goal cannot be solved by pure ground equational reasoning, constructor distinctness, or intuitionistic propositional logic without term unfolding or case analysis.

### Signature C: Ltac Pattern Match Failure

```text
Error: No matching clauses for match goal.
```

A custom Ltac macro executed a `match goal with ... end` block where no pattern clause matched the current proof state, or an unhandled failure propagated out of a matching clause.

---

## 2. Root Cause & Theoretical Background

1. **`zify` Preprocessing and Truncated Subtraction**:
   `lia` internally operates on linear integer arithmetic ($\mathbb{Z}$) via the `micromega` solver (`plugins/micromega/`).
   - The `zify` preprocessor lifts terms into $\mathbb{Z}$ using registered type injections (`ZifyClasses`):
     - `nat -> Z.of_nat`, `N -> Z.of_N`, `positive -> Z.pos`.
     - Operations `+`, `*`, `S`, `O` map to `Z.add`, `Z.mul`, `Z.succ`, `0%Z`.
     - Comparisons `<=`, `<`, `=`, `<>` map to their $\mathbb{Z}$ equivalents.
   - **Truncated Subtraction Blowup**: Natural number subtraction `n - m` is translated into `Z.max 0 (Z.of_nat n - Z.of_nat m)`. Each distinct occurrence of `Z.max a b` induces a case split:
     $$\text{Branch 1: } a \ge b \quad \Big\vert{} \quad \text{Branch 2: } a < b$$
     If an expression or hypothesis context contains $k$ natural subtractions or `Nat.pred` terms, `micromega` generates up to $2^k$ constraint branches. When $2^k$ exceeds solver bounds, `Cannot solve goal with lia` is raised.
2. **`nia` (Non-linear Integer Arithmetic) Boundaries**:
   `nia` uses polynomial cone heuristics ($x^2 \ge 0$ and $a \ge 0 \land b \ge 0 \implies a \cdot b \ge 0$) to extend `lia`.
   - **Unsupported Constructs**: Non-integer exponentiation ($x^y$), non-linear modular equations, and integer division/modulo (`Z.div`, `Z.modulo`, `/`, `mod`) cannot be solved by `nia`.
   - Division must be eliminated manually via `Z.div_mod_eq` or `Nat.div_mod` before invoking `nia`.
3. **Ltac Failure Levels (`fail 0` vs. `fail 1`)**:
   In Ltac's `match goal with ... end`:
   - If a tactic in a branch fails with level 0 (`fail 0` or standard failure like `discriminate`), Ltac backtracks to the next matching clause or permutation of hypotheses.
   - If a branch fails with level 1 or higher (`fail 1`), or if no pattern matches, the entire `match goal` aborts with `No matching clauses`.

---

## 3. Anti-Patterns to Avoid

- ❌ **Calling removed legacy tactics (`omega`, `romega`, `sos`)**: These tactics were removed in Coq 8.14+ and are fatal syntax errors in Rocq 9.0+. Always import `Lia` and use `lia`.
- ❌ **Calling `lia` on unbounded `nat` subtraction**: Expecting `lia` to deduce $a \le b$ from $a - b = 0$ without a case split.
- ❌ **Passing expressions with `div` or `mod` to `nia`**: Expecting non-linear solvers to discharge integer division without manual quotient-remainder lemmas.
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

### Case 2: Taming Subtraction Combinatorial Explosion with `zify`

When multiple subtractions cause `lia` to fail:

**Repaired Code:**

```Coq
From Stdlib Require Import Lia.
From Stdlib Require Import ZArith.

Lemma multi_sub_example : forall a b c : nat,
  a <= b -> b <= c -> (c - b) + (b - a) = c - a.
Proof.
  intros a b c Hab Hbc.
  (* Preprocess with zify to expose Z.max *)
  zify.
  (* Use known bounds Hab and Hbc so the solver avoids unnecessary case branches *)
  lia.
Qed.
```

---

### Case 3: Non-Linear Arithmetic with `nia` & Division Elimination

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

When integer division is involved:

```Coq
From Stdlib Require Import ZArith.
From Stdlib Require Import Lia.
Open Scope Z_scope.

Lemma div_mul_bound : forall a b : Z,
  b > 0 -> a >= 0 -> (a / b) * b <= a.
Proof.
  intros a b Hb Ha.
  (* Eliminate division by asserting the Euclidean division equation *)
  pose proof (Z.div_mod_eq a b Hb) as Hdiv.
  pose proof (Z.mod_pos_bound a b Hb).
  nia.
Qed.
```

---

### Case 4: Robust Ltac Pattern Matching with Fallbacks

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
3. **Manual Arithmetic Decomposition**:
   When automation cannot close the goal, rewrite using standard arithmetic lemmas:
   - `rewrite Nat.mul_comm, Nat.add_assoc.`
   - `apply Nat.mul_le_mono_l; lia.`
