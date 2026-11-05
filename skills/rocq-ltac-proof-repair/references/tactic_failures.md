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

### Case 5: Taming Simplification Blowup (`simpl` vs `cbn [fn]` & Unfold Lemmas)

Running unconditional `simpl` on functions that use accumulator arguments, fuel counters, or complex pattern matching can aggressively unroll definitions into massive, unreadable nested `match` expressions that freeze the compiler.

**Failing Code (Before - Simplification Blowup):**

```Coq
Fixpoint eval_step (fuel : nat) (st : state) (c : cmd) : option state :=
  match fuel with
  | O => None
  | S fuel' =>
      match c with
      | CSkip => Some st
      | CSeq c1 c2 =>
          match eval_step fuel' st c1 with
          | Some st' => eval_step fuel' st' c2
          | None => None
          end
      (* More branches ... *)
      end
  end.

Lemma eval_step_extend : forall fuel st c st',
  eval_step fuel st c = Some st' ->
  eval_step (S fuel) st c = Some st'.
Proof.
  intros fuel st c st' H.
  simpl.
  (* Disastrous: unrolls every recursive call into hundreds of nested match clauses *)
Abort.
```

**Repaired Code (After - Controlled Reduction via `cbn` or Unfold Lemmas):**

1. **Targeted Reduction with `cbn`**:
   ```Coq
   (* Restrict reduction strictly to the outer fuel constructor: *)
   cbn [eval_step].
   ```
2. **Step Unfolding Lemma**:
   Prove an explicit one-step unrolling equation and rewrite with it instead of reducing:

   ```Coq
   Lemma eval_step_S : forall fuel st c,
     eval_step (S fuel) st c =
       match c with
       | CSkip => Some st
       | CSeq c1 c2 =>
           match eval_step fuel st c1 with
           | Some st' => eval_step fuel st' c2
           | None => None
           end
       end.
   Proof. reflexivity. Qed.

   (* In proof: *)
   rewrite eval_step_S.
   destruct c; [reflexivity | ...].
   ```

---

### Case 6: Preventing Unresolved Existential Variables in `eauto` (The Evar Trap)

When applying lemmas with intermediate existential parameters (such as transitive relations or typing rules with unconstrained intermediate types `?T`), `eauto` or `eapply` may bind an incorrect term to the existential variable or leave it uninstantiated, causing `Cannot solve goal with existential variables` at `Qed`.

**Failing Code (Before):**

```Coq
(* Rule: has_type Gamma (t_app t1 t2) T2
         requires has_type Gamma t1 (t_arrow T1 T2) and has_type Gamma t2 T1 *)
Lemma app_typing_example : forall Gamma t1 t2 T2,
  has_type Gamma (t_app t1 t2) T2.
Proof.
  intros.
  eapply T_App.
  (* Created existential variable ?T1 for the domain type *)
  eauto.
  (* eauto binds ?T1 erroneously or leaves it unresolved, failing later *)
Abort.
```

**Repaired Code (After - Supplying Witnesses or Explicit Instantiation):**

1. **Explicitly Instantiate Intermediate Witnesses**:
   ```Coq
   (* Explicitly name the domain type: *)
   eapply T_App with (T1 := Nat_Type).
   - apply Ht1.
   - apply Ht2.
   ```
2. **Extract Existential Hypotheses Before Automation**:
   When hypotheses contain existential quantifiers, destruct them into concrete variables before invoking `eauto`:
   ```Coq
   destruct H_exists as [witness H_prop].
   eapply Rule; [exact H_prop | eauto].
   ```

---

### Case 7: Equivalence Rewriting in High-Order Contexts (Setoid Rewrite Failures)

When rewriting with equivalence relations (e.g., `Permutation l1 l2`) under custom or nested functions, standard `rewrite` fails with `Cannot find a relation to rewrite` if no `Proper` morphism is declared for the context.

**Failing Code (Before):**

```Coq
From Stdlib Require Import Sorting.Permutation.

Lemma perm_insert_example : forall (x a : nat) (l : list nat),
  Permutation (x :: l) (insert x l) ->
  Permutation (a :: x :: l) (a :: insert x l).
Proof.
  intros x a l H.
  (* Direct rewrite may fail if custom constructors wrap the list *)
  rewrite H.
Abort.
```

**Repaired Code (After - Manual Transitivity & Constructor Steps):**

Apply constructor congruence lemmas or bridge via explicit transitivity:

```Coq
From Stdlib Require Import Sorting.Permutation.

Lemma perm_insert_example : forall (x a : nat) (l : list nat),
  Permutation (x :: l) (insert x l) ->
  Permutation (a :: x :: l) (a :: insert x l).
Proof.
  intros x a l H.
  (* Use direct constructor preservation: *)
  apply perm_skip.
  exact H.
Qed.

Lemma perm_trans_bridge : forall (x a : nat) (l : list nat),
  Permutation (x :: a :: l) (insert x (a :: l)).
Proof.
  intros x a l.
  (* Bridge through intermediate permutation via transitivity: *)
  apply Permutation_trans with (a :: x :: l).
  - apply perm_swap.
  - apply perm_insert_example. apply perm_insert_base.
Qed.
```

---

### Case 8: Discharging Hidden Invariants in Linear Arithmetic

`lia` operates on linear integer arithmetic but cannot inspect inside higher-order predicates, tree structures, or abstract predicates (e.g., binary search tree invariants `ForallT (fun y => y < x) tree`).

**Failing Code (Before):**

```Coq
(* Context contains:
   H_bst : ForallT (fun y => y < x) left_tree
   H_in : InTree k left_tree
   Goal : k < x *)
lia. (* Fails: lia cannot peek inside ForallT *)
```

**Repaired Code (After - Exposing Inequalities into the Context):**

Extract the inequality into the local hypothesis context first:

```Coq
(* Extract the concrete inequality using the invariant accessor lemma: *)
assert (H_ineq : k < x) by (eapply forallt_in; eassumption).
(* Now lia immediately solves the goal *)
lia.
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
3. **Manual Arithmetic Decomposition**:
   When automation cannot close the goal, rewrite using standard arithmetic lemmas:
   - `rewrite Nat.mul_comm, Nat.add_assoc.`
   - `apply Nat.mul_le_mono_l; lia.`
