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

After executing multiple bare `inversion H.` calls, the proof context becomes unmanageable, leading to attention drift and performance degradation.

### Signature B: Soundness Gate Rejection (Axiom K Contamination)

```text
Axioms:
Coq.Logic.Eqdep.Eq_rect_eq.eq_rect_eq :
  forall (U : Type) (p : U) (Q : p = p -> Type) (x : Q eq_refl) (h : p = p),
  x = eq_rect p (fun (p0 : U) (h0 : p = p0) => Q h0) x p h
```

Verification at Tier 3 (`audit_axioms.py` / `Print Assumptions`) fails because a proof relied on Streicher's Axiom K or `JMeq_eq`.

---

## 2. Root Cause & Theoretical Background

1. **The Inversion Mechanism in CIC**:
   `inversion H` uses the inductive constructors of $H$'s type to derive equality equations between index terms. It introduces new equality hypotheses ($H_0, H_1, \dots$) into the local context.
   - If these equalities are not eliminated via substitution (`subst`), they linger indefinitely.
   - If the inverted hypothesis $H$ is not removed (`clear H`), subsequent automation tactics may repeatedly invert the same hypothesis.
2. **Axiom K vs. Intensional Type Theory**:
   The Calculus of Inductive Constructions (CIC) does not include Uniqueness of Identity Proofs (UIP / Axiom K) by default. In intensional type theory, identity proofs for arbitrary types are not necessarily unique.
   - `dependent destruction` and `dependent inversion` from `Program.Equality` internally rely on `Eqdep.Eq_rect_eq.eq_rect_eq` (Axiom K).
   - In projects targeting constructivist, homotopy-compatible, or axiom-free standards, using `dependent destruction` is a soundness violation.
   - When types have decidable equality (e.g., `nat`, `bool`, `list nat`), UIP is a theorem (Hedberg's Theorem via `Eqdep_dec`), not an axiom.

---

## 3. Anti-Patterns to Avoid

- ❌ **Bare `inversion H.`**: Never leave `inversion H.` without immediate substitution and hypothesis pruning.
- ❌ **Unthinking use of `dependent destruction H`**: Avoid introducing Axiom K into what should be purely constructive or kernel-closed proofs.
- ❌ **Inverting when `destruct` suffices**: If an inductive type has no indexed parameters (e.g., `nat`, `list`, or simple inductive records), use `destruct`, not `inversion`.

---

## 4. Concrete Prescriptions (Before & After)

### Case 1: CompCert Destructive Inversion Pipeline

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

If not using a helper macro, write out the explicit atomic pipeline:

```Coq
inversion H; subst; clear H.
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

## 5. Fallback Procedures

1. **Decidable Equality Elimination (`Eqdep_dec`)**:
   If an equality over a type with decidable equality (like `nat` or `string`) appears in an inductive index, import `Eqdep_dec`:
   ```Coq
   From Stdlib Require Import Eqdep_dec.
   (* Use inj_pair2_eq_dec with PeanoNat.Nat.eq_dec to eliminate dependent equalities without Axiom K *)
   apply (inj_pair2_eq_dec _ PeanoNat.Nat.eq_dec) in H.
   ```
2. **Targeted `subst`**:
   If full `subst` fails due to circular dependencies (e.g., `x = f x`), use targeted variable substitution:
   ```Coq
   subst x.
   ```
