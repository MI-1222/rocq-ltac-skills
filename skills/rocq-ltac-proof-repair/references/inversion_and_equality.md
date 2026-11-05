# Inversion, Context Discipline & Sound Equality

This reference provides techniques to eliminate context explosion caused by bare `inversion`, prevent accidental Axiom K (`Eqdep.Eq_rect_eq.eq_rect_eq`) contamination from dependent destruction, and maintain a sound equality pipeline in Rocq 9.0+ and Coq 8.20.

---

## 1. Error Signatures

### Signature A: Hypothesis Explosion (Context Pollution)

```text
H0 : x = y
H1 : e1 = e2
H2 : e3 = e4
H3 : ... (dozens of redundant equality assumptions cluttering the context)
```

After executing multiple bare `inversion H.` calls, the proof context becomes unmanageable, leading to attention drift and script instability.

### Signature B: Soundness Gate Rejection (Axiom K Contamination)

```text
Axioms:
Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq :
  forall (U : Type) (p : U) (Q : p = p -> Type) (x : Q eq_refl) (h : p = p),
  x = eq_rect p (fun (p0 : U) (h0 : p = p0) => Q h0) x p h
```

or dependencies on:

```text
Coq.Logic.JMeq.JMeq_eq
Coq.Logic.Eqdep.inj_pair2
```

Verification at Tier 3 (`audit_axioms.py` / `Print Assumptions`) fails because a proof quietly relied on Uniqueness of Identity Proofs (UIP / Axiom K) or heterogeneous equality axioms introduced by dependent destruction.

---

## 2. Root Cause & Theoretical Background

1. **The Inversion Mechanism in CIC**:
   `inversion H` (`tactics/inversion.ml`) uses the constructors of $H$'s inductive type to derive equality equations between index terms.
   - By default, generated hypotheses are assigned fresh identifiers sequentially: `H, H0, H1, H2, ...`.
   - Scripts that reference these generated names (`H0`, `H1`) without explicit naming patterns are brittle and break when constructors or indices change.
   - If derived equalities are not eliminated via substitution (`subst`) and the source hypothesis is not removed (`clear H`), the context remains cluttered with redundant terms.
2. **Axiom K vs. Intensional Type Theory**:
   The Calculus of Inductive Constructions (CIC) does not include Uniqueness of Identity Proofs (Axiom K) by default. In intensional type theory, identity proofs for arbitrary types are not necessarily unique.
   - `dependent destruction` and `dependent inversion` from `theories/Program/Equality.v` internally rely on `Eqdep.Eq_rect_eq.eq_rect_eq` (Axiom K) and `JMeq.JMeq_eq`.
   - In projects targeting constructivist, homotopy-compatible, or axiom-free standards, using `dependent destruction` is a soundness violation.
   - When index types have decidable equality (e.g., `nat`, `bool`, `list nat`), UIP is provable constructively via `theories/Logic/Eqdep_dec.v` (`inj_pair2_eq_dec`) without any external axioms.

---

## 3. Anti-Patterns to Avoid

- ❌ **Bare `inversion H.`**: Never leave `inversion H.` without immediate substitution and hypothesis pruning.
- ❌ **Relying on auto-generated names (`H0`, `H1`)**: Always use `inversion H as [...]` or explicitly rename hypotheses immediately after inversion.
- ❌ **Unthinking use of `dependent destruction H`**: Avoid introducing Axiom K into constructive or kernel-closed proofs.
- ❌ **Inverting when `destruct` suffices**: If an inductive type has no indexed parameters (e.g., `nat`, `list`, or simple inductive records), use `destruct`, not `inversion`.

---

## 4. Concrete Prescriptions (Before & After)

### Case 1: Destructive Inversion Pipeline

**Failing Code (Before):**

```Coq
Inductive expr : Type :=
| EConst : nat -> expr
| EAdd : expr -> expr -> expr.

Inductive eval : expr -> nat -> Prop :=
| EvConst : forall n, eval (EConst n) n
| EvAdd : forall e1 e2 n1 n2,
    eval e1 n1 -> eval e2 n2 -> eval (EAdd e1 e2) (n1 + n2).

Lemma eval_const_inv : forall n m, eval (EConst n) m -> n = m.
Proof.
  intros n m H.
  inversion H. (* Leaves H, H0 : EConst n = EConst n0, H1 : m = n0 *)
  (* Context is cluttered; requires manual 'subst' and 'clear' steps *)
  subst.
  reflexivity.
Qed.
```

**Repaired Code (After):**

```Coq
(* Recommended project-level helper macro: *)
Ltac inv H := inversion H; subst; clear H.

Lemma eval_const_inv : forall n m, eval (EConst n) m -> n = m.
Proof.
  intros n m H.
  inv H. (* Performs inversion, substitutes all derived equalities, and clears H *)
  reflexivity.
Qed.
```

If not using a helper macro, write out the explicit atomic pipeline or structured pattern:

```Coq
inversion H as [n0 H0 H1]; subst; clear H.
```

---

### Case 2: Replacing `dependent destruction` to Avoid Axiom K

**Failing Code (Before - Uses Axiom K):**

```Coq
From Stdlib Require Import Program.Equality.

Inductive vector (A : Type) : nat -> Type :=
| vnil : vector A 0
| vcons : forall n, A -> vector A n -> vector A (S n).

Lemma vector_zero_inv : forall (A : Type) (v : vector A 0), v = vnil A.
Proof.
  intros A v.
  dependent destruction v. (* Quietly introduces Axiom K (eq_rect_eq) *)
  reflexivity.
Qed.
(* Print Assumptions vector_zero_inv shows Eqdep.Eq_rect_eq.eq_rect_eq *)
```

**Repaired Code (After - Pure Constructive CIC):**

```Coq
Inductive vector (A : Type) : nat -> Type :=
| vnil : vector A 0
| vcons : forall n, A -> vector A n -> vector A (S n).

Definition vhead {A : Type} {n : nat} (v : vector A (S n)) : A :=
  match v in vector _ k return match k with 0 => unit | S _ => A end with
  | vnil _ => tt
  | vcons _ _ h _ => h
  end.

Lemma vector_zero_inv : forall (A : Type) (v : vector A 0), v = vnil A.
Proof.
  intros A v.
  refine (match v as v' in vector _ n
                return match n with
                       | 0 => fun v'' => v'' = vnil A
                       | S _ => fun _ => True
                       end v' with
          | vnil _ => fun _ => eq_refl
          | vcons _ _ _ _ => fun _ => I
          end v).
Qed.
(* Print Assumptions vector_zero_inv resolves to: Closed under the global context *)
```

For inductive predicates, use the `remember ... as x eqn:Heqx` pattern instead of `dependent destruction`:

```Coq
remember 0 as n eqn:Heqn.
induction H as [...]; subst; [reflexivity | discriminate Heqn].
```

---

### Case 3: Constructor Equality and Distinctness

Use `discriminate` and `injection` for direct constructor manipulations:

```Coq
Lemma cons_inj : forall (A : Type) (x y : A) (l1 l2 : list A),
  x :: l1 = y :: l2 -> x = y /\ l1 = l2.
Proof.
  intros A x y l1 l2 H.
  injection H as Hhead Htail. (* Directly decomposes constructor equalities *)
  split; [exact Hhead | exact Htail].
Qed.

Lemma const_distinct : forall (n : nat),
  EConst n = EAdd (EConst 0) (EConst 0) -> False.
Proof.
  intros n H.
  discriminate H. (* Immediately proves False from distinct constructors *)
Qed.
```

---

### Case 4: Automating Contradiction Rejection (`solve_by_inverts` & Recovery)

In semantic systems with many typing or transition rules, non-matching constructor hypotheses frequently arise. Automated inversion macros discharge these by attempting recursive `inversion; subst; discriminate`.

**Helper Macro Definition:**

```Coq
Ltac solve_by_invert_step :=
  match goal with
  | H : _ |- _ => solve [ inversion H; subst; discriminate ]
  end.

Ltac solve_by_inverts n :=
  match n with
  | S ?n' => solve_by_invert_step || (
      match goal with
      | H : _ |- _ => inversion H; subst; clear H; solve_by_inverts n'
      end)
  | O => fail "Depth exhausted"
  end.
```

**Diagnosing `No matching clauses for match goal`:**

When `solve_by_inverts n` fails:

1. **Depth Exhaustion**: The contradiction requires more inversions than depth $n$ allows (e.g., intermediate syntax wrapping). Increase depth from 2 to 3, or manually invert the outer wrapper first.
2. **Missing Invertible Premise**: The contradiction requires an equality or predicate that is not yet introduced into the context. Ensure premises are brought into scope (`intros`) before calling the macro.
3. **Manual Fallback**: Identify the exact conflicting hypothesis $H$ and execute:
   ```Coq
   inversion H; subst; clear H; try discriminate.
   ```

---

### Case 5: Boolean Reflection & Case Splitting (`reflect` vs `bdestruct`)

When branching on computable comparison operations (e.g., `n =? m`, `n <=? m`, `string_dec`), directly analyzing booleans with `destruct (n =? m)` yields boolean flags without equality hypotheses in `Prop`.

**Failing Code (Before - Lost Propositional Equality):**

```Coq
From Stdlib Require Import Nat.

Lemma eqb_example : forall n m : nat, (n =? m) = true -> n = m.
Proof.
  intros n m H.
  destruct (n =? m).
  - (* We know the flag was true, but n = m is NOT introduced into context! *)
Abort.
```

**Repaired Code (After - Recording Equations via `eqn:` or Reflection Spec):**

1. **Explicit Equation Recording**:
   ```Coq
   destruct (n =? m) eqn:Heq.
   - apply Nat.eqb_eq in Heq. exact Heq.
   - discriminate H.
   ```
2. **Using Reflection Lemmas Directly (`_spec`)**:
   ```Coq
   destruct (Nat.eqb_spec n m) as [Heq | Hneq].
   - exact Heq.
   - (* In false branch, Hneq : n <> m *)
     discriminate H.
   ```
3. **Recovery when Custom Reflection Tactics (e.g., `bdestruct`) Fail**:
   If a reflection macro fails with `No matching clauses for match goal`, the comparison operator is not registered in the macro's pattern list. Deconstruct the expression manually:
   ```Coq
   destruct (target_expr) eqn:Heq; [apply op_spec in Heq | ...].
   ```

---

### Case 6: Preventing Over-Substitution in Environment & Map Updates

In operational semantics and compilers using functional maps or association lists (`x |-> v; Gamma`), running unconditional `subst` can replace recently updated keys with older shadowed definitions if both share equality hypotheses.

**Anti-Pattern:**

```Coq
(* Context has:
   H1 : x = y
   H2 : update (update m x v1) y v2 = m' *)
subst.
(* Indiscriminate substitution may overwrite shadowed variable names unpredictably *)
```

**Repaired Code (Controlled Rewriting via Lemmas):**

Instead of bare `subst`, rewrite systematically using environment theorems:

```Coq
(* Update on same key shadows previous value *)
rewrite update_shadow in H.
(* Updates on distinct keys commute *)
rewrite update_permute in H by auto.
(* Reading most recent update *)
rewrite update_eq.
(* Reading distinct key *)
rewrite update_neq by auto.
```

---

## 5. Fallback Procedures

1. **Decidable Equality Elimination (`Eqdep_dec`)**:
   If an equality over a type with decidable equality (like `nat` or `string`) appears in an inductive index, import `Eqdep_dec`:
   ```Coq
   From Stdlib Require Import Eqdep_dec.
   (* Use inj_pair2_eq_dec with PeanoNat.Nat.eq_dec to eliminate dependent equalities constructively without Axiom K *)
   apply (inj_pair2_eq_dec _ PeanoNat.Nat.eq_dec) in H.
   ```
2. **Targeted `subst`**:
   If full `subst` fails due to circular dependencies (e.g., `x = f x`), use targeted variable substitution:
   ```Coq
   subst x.
   ```
