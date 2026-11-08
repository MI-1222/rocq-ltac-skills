# Computer Science Verification Idioms

This reference provides implementation-grounded skeletons and proof patterns for the core domains of computer science verification in Rocq: programming language semantics, state transition systems, compiler correctness, and well-founded termination.

---

## 1. Programming Language Semantics: Progress & Preservation

Type soundness in operational semantics is established by the dual theorems of **Progress** and **Preservation** (Subject Reduction).

```coq
Ltac inv H := inversion H; subst; clear H.
```

### Pattern 1: Progress Theorem

Progress states that every well-typed closed term is either a final value or can take an evaluation step:

```coq
Theorem progress : forall t T,
  has_type empty t T ->
  value t \/ exists t', step t t'.
Proof.
  intros t T Ht.
  remember empty as Gamma eqn:HeqGamma.
  induction Ht; subst.
  - (* T_Var: Variables cannot be typed in an empty context *)
    discriminate HeqGamma.
  - (* T_Abs: Abstractions are immediate values *)
    left. constructor.
  - (* T_App: Function application *)
    right.
    (* Destruct induction hypothesis for function position *)
    destruct (IHHt1 eq_refl) as [Hval1 | [t1' Hstep1]].
    + (* t1 is a value: check argument t2 *)
      destruct (IHHt2 eq_refl) as [Hval2 | [t2' Hstep2]].
      * (* Canonical Forms: value of arrow type must be an abstraction *)
        inv Hval1; try solve [ inv Ht1 ].
        eexists. apply step_beta; eauto 2.
      * (* t2 takes a step *)
        eexists. apply step_app2; eauto 2.
    + (* t1 takes a step *)
      eexists. apply step_app1; eauto 2.
Qed.
```

### Pattern 2: Preservation Theorem & Context Generalization

Preservation states that evaluation steps preserve the type of an expression.

#### Architectural Rules for Preservation:

1. **Induction on Typing Derivation**: Always perform induction on the typing derivation `has_type empty t T` rather than the evaluation step `step t t'`. Inducting on evaluation requires reconstructing typing derivations for subexpressions through inversion lemmas across all cases.
2. **Mandatory Step Generalization**: You **must** execute `generalize dependent t'` before `induction Ht`. Otherwise, the induction hypothesis `IHHt` binds to a specific target term `t'`, destroying the ability to instantiate it for subexpression transitions.

```coq
Theorem preservation : forall t t' T,
  has_type empty t T ->
  step t t' ->
  has_type empty t' T.
Proof.
  intros t t' T Ht.
  generalize dependent t'.
  remember empty as Gamma eqn:HeqGamma.
  induction Ht; intros t' Hstep; subst; try solve [ inv Hstep ].
  - (* T_App *)
    inv Hstep.
    + (* step_beta: apply substitution lemma *)
      inv Ht1.
      eapply substitution_preserves_typing; eauto.
    + (* step_app1: apply IH on first term *)
      eapply T_App; eauto.
    + (* step_app2: apply IH on second term *)
      eapply T_App; eauto.
Qed.
```

### Pattern 3: Generalized Contexts in the Substitution Lemma

The Substitution Lemma states that substituting a closed well-typed value `s : S` into a term `t : T` preserves typing.

#### Architectural Mandate:

Because variable binders (abstractions) extend the local typing context, you **must** generalize both the context `Gamma` and the target type `T` before structural induction on term `t`:

```coq
Lemma substitution_preserves_typing : forall Gamma x s t S T,
  has_type (update Gamma x S) t T ->
  has_type empty s S ->
  has_type Gamma (subst x s t) T.
Proof.
  intros Gamma x s t S T Ht.
  generalize dependent Gamma.
  generalize dependent T.
  induction t; intros T Gamma Ht Hs;
    inv Ht; simpl; eauto.
  - (* Variable case: split on identifier equality *)
    destruct (String.eqb_spec x0 x); subst.
    + (* x0 = x: target variable matches; invoke weakening on Hs *)
      rewrite update_eq in H1. injection H1 as ->; subst.
      apply weakening_empty; assumption.
    + (* x0 <> x: context update exchange *)
      rewrite update_neq in H1; [| assumption ].
      constructor. assumption.
Qed.
```

### Pattern 4: Determinism via Cross-Inversion

Determinism states that single-step evaluation produces a unique successor:

```coq
Theorem step_deterministic : forall t t1 t2,
  step t t1 ->
  step t t2 ->
  t1 = t2.
Proof.
  intros t t1 t2 Hstep1.
  generalize dependent t2.
  induction Hstep1; intros t2 Hstep2; inv Hstep2; try reflexivity.
  - (* Conflicting step vs value: contradiction via irreducibility lemma *)
    exfalso. eapply value_cannot_step; eauto.
  - (* Congruence step: apply induction hypothesis *)
    apply IHHstep1 in H3. subst. reflexivity.
Qed.
```

---

## 2. State Transition Systems & Invariant Preservation

Verifying reactive systems, protocols, and abstract machines requires reasoning over the **reflexive transitive closure (RTC)** of a transition relation.

### Definition: Head-Stepping vs Binary Transitivity

Always define RTC using a **left-associative head-stepping constructor** (`rtc_step`) rather than a symmetric binary transitivity constructor (`rtc_trans : rtc R x y -> rtc R y z -> rtc R x z`):

```coq
Inductive rtc {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| rtc_refl : forall x, rtc R x x
| rtc_step : forall x y z, R x y -> rtc R y z -> rtc R x z.
```

#### Why Head-Stepping is Architecturally Superior:

- When applying `induction` to an `rtc` term, head-stepping makes the induction isomorphic to natural number induction on execution trace length.
- A binary `rtc_trans` constructor creates unconstrained existential intermediate states $y$ at each induction step, blowing up the search space and causing induction hypotheses to become too weak to close the goal.

### The Three Prerequisite RTC Lemmas

Before proving high-level system theorems, always establish these three prerequisite lemmas:

```coq
(** 1. Single-step embedding *)
Lemma rtc_R : forall {A : Type} (R : A -> A -> Prop) (x y : A),
  R x y -> rtc R x y.
Proof.
  intros A R x y H.
  eapply rtc_step; [eassumption | constructor].
Qed.

(** 2. Transitivity lemma *)
Lemma rtc_trans : forall {A : Type} (R : A -> A -> Prop) (x y z : A),
  rtc R x y -> rtc R y z -> rtc R x z.
Proof.
  intros A R x y z H1 H2.
  induction H1 as [| x1 x2 x3 HR Hrest IH].
  - assumption.
  - eapply rtc_step; [eassumption | apply IH; assumption].
Qed.

(** 3. Universal Invariant Preservation Lifting *)
Theorem rtc_invariant : forall {A : Type} (R : A -> A -> Prop) (P : A -> Prop) (x y : A),
  (forall s s', P s -> R s s' -> P s') ->
  P x ->
  rtc R x y ->
  P y.
Proof.
  intros A R P x y Hstep Hinit Hreach.
  induction Hreach as [s | s1 s2 s3 Htrans Hrest IH].
  - assumption.
  - apply IH.
    eapply Hstep; [apply Hinit | apply Htrans].
Qed.
```

---

## 3. Separation Logic & Heap Predicate Verification

When verifying programs that manipulate pointers, mutable state, or distributed resources, proof terms easily explode if heap equalities are rewritten manually.

### Core Separation Logic Monoid Skeletons

```coq
Parameter loc : Type.
Parameter val : Type.

Definition heap : Type := loc -> option val.
Definition hprop : Type := heap -> Prop.

Parameter hempty : hprop.
Parameter hsingle : loc -> val -> hprop.
Parameter hstar : hprop -> hprop -> hprop.
Parameter himpl : hprop -> hprop -> Prop.

Notation "\[]" := hempty (at level 0) : heap_scope.
Notation "p '~~>' v" := (hsingle p v) (at level 32) : heap_scope.
Notation "H1 '\*' H2" := (hstar H1 H2) (at level 41, right associativity) : heap_scope.
Notation "H1 '==>' H2" := (himpl H1 H2) (at level 55) : heap_scope.
```

### Two-Phase Automated Normalization (`xsimpl`)

Never attempt manual rewriting with associativity and commutativity lemmas for $\star$. Design an automated, non-diverging two-phase Ltac macro:

```coq
Axiom hstar_assoc : forall H1 H2 H3, (H1 \* H2) \* H3 ==> H1 \* (H2 \* H3).
Axiom hstar_comm  : forall H1 H2, H1 \* H2 ==> H2 \* H1.
Axiom hstar_empty_l : forall H, \[] \* H ==> H.
Axiom himpl_refl  : forall H, H ==> H.
Axiom hstar_congr_l : forall H1 H2 H3, H2 ==> H3 -> H1 \* H2 ==> H1 \* H3.

(** Phase 1: Structural Canonicalization & Phase 2: Term Cancellation *)
Ltac xsimpl_step :=
  match goal with
  | |- (?H1 \* ?H2) ==> (?H1 \* ?H3) =>
      (* Cancel identical head predicates (Frame cancellation) *)
      apply hstar_congr_l
  | |- (_ \* _) \* _ ==> _ =>
      (* Re-associate to right-associative normal form *)
      eapply himpl_trans; [apply hstar_assoc |]
  | |- \[] \* ?H ==> ?H =>
      apply hstar_empty_l
  | |- ?H ==> ?H =>
      apply himpl_refl
  end.

Ltac xsimpl :=
  repeat progress xsimpl_step.
```

### Frame Rule & Evar Discipline

When applying a Hoare triple with a frame rule:

1. Generate an existential variable (Evar `?Frame`) for the unmodified residue of the heap.
2. Immediately invoke `xsimpl` to unify `?Frame` against the remaining conjuncts.
3. **Mandatory Discipline**: Never leave `?Frame` uninstantiated across branching subgoals. If an Evar remains unresolved, subsequent tactics across sibling goals can constrain it incompatibly, causing proof paralysis.

---

## 4. Data Structure Invariants & Functional Correctness

When verifying algorithms (e.g., search trees, heaps, sorting), conflating representation invariants with functional correctness leads to intractable, monolithic inductions.

### Principle 1: Strict Orthogonality of Representation & Specification

Separate structural well-formedness from input/output input relations:

```coq
Inductive tree : Type :=
| E : tree
| T : tree -> nat -> nat -> tree -> tree.

Fixpoint forall_tree (P : nat -> Prop) (t : tree) : Prop :=
  match t with
  | E => True
  | T l k v r => P k /\ forall_tree P l /\ forall_tree P r
  end.

(** Representation Invariant: Binary Search Tree *)
Inductive BST : tree -> Prop :=
| BST_E : BST E
| BST_T : forall l k v r,
    BST l ->
    BST r ->
    forall_tree (fun k' => k' < k) l ->
    forall_tree (fun k' => k' > k) r ->
    BST (T l k v r).

Parameter insert : nat -> nat -> tree -> tree.
Parameter lookup : nat -> tree -> option nat.

(** Theorem 1: Representation Invariant Preservation (Proven Independently) *)
Theorem insert_BST : forall k v t,
  BST t -> BST (insert k v t).
Proof.
  (* Structural induction on t without mixing lookup logic *)
Admitted.

(** Theorem 2: Functional Correctness (Assumes Invariant as Precondition) *)
Theorem lookup_insert_eq : forall k v t,
  BST t -> lookup k (insert k v t) = Some v.
Proof.
  (* Leverages insert_BST to guarantee BST preservation at each step *)
Admitted.
```

### Principle 2: Sorting Correctness via Decoupled Relations

Always decouple sorting verification into two orthogonal properties:

1. **Permutation Equivalence**: Elements are neither created nor destroyed (`Permutation al (sort al)`).
2. **Sortedness**: Output elements satisfy the ordering relation (`Sorted (sort al)`).

```coq
Definition is_correct_sorting (sort : list nat -> list nat) : Prop :=
  forall al, Permutation al (sort al) /\ Sorted (sort al).
```

### Principle 3: Branch Analysis via Boolean Reflection (`bdestruct`)

**Anti-Pattern**: Bare `destruct (x =? y)` drops the connection between the condition and the branched subgoals, leaving `x =? y = true` without propositional equalities `x = y`.

**Prescription**: Use boolean reflection (`reflect`) to introduce propositional equalities into hypotheses:

```coq
From Stdlib Require Import Arith Lia.

(** Macro reflecting boolean comparison into propositional equality / inequality *)
Ltac bdestruct X :=
  let H := fresh "H" in
  destruct X eqn:H;
  [ apply Nat.eqb_eq in H
  | apply Nat.eqb_neq in H ].
```

With `bdestruct (x =? y)`, the branches immediately introduce `H : x = y` and `H : x <> y` into hypotheses, enabling `subst` and `lia` to discharge arithmetic constraints automatically.

---

## 5. Compiler Correctness: Forward Simulation Diagrams

Compiler correctness proofs establish that target code executions simulate source code executions according to a state matching relation:

```mermaid
graph TD
  s1["Source State s1"] -->|"step_rel S"| s2["Source State s2"]
  t1["Target State t1"] -->|"step_rel T (rtc)"| t2["Target State t2"]
  s1 -.->|"match_states"| t1
  s2 -.->|"match_states"| t2
```

### Forward Simulation Skeleton

```coq
Theorem simulation_step : forall (S T : TransitionSystem) (match_states : state S -> state T -> Prop),
  (forall s t s',
     match_states s t ->
     step_rel S s s' ->
     exists t', step_rel T t t' /\ match_states s' t') ->
  forall s0 sn, rtc (step_rel S) s0 sn ->
  forall t0, match_states s0 t0 ->
  exists tn, rtc (step_rel T) t0 tn /\ match_states sn tn.
Proof.
  intros S T match_states Hstep_sim s0 sn Hreach.
  induction Hreach as [s | s1 s2 s3 Hstep_s Hreach_rest IH]; intros t0 Hmatch.
  - (* Base: zero steps *)
    exists t0. split; [constructor | assumption].
  - (* Inductive step: advance one simulation step *)
    edestruct Hstep_sim as [t1 [Hstep_t Hmatch1]]; eauto.
    edestruct IH as [tn [Hreach_t Hmatch_final]]; eauto.
    exists tn. split; [| assumption].
    econstructor; eauto.
Qed.
```

---

## 6. Well-Founded Termination with `Program Fixpoint`

When recursive functions do not decrease structurally on a single syntactic argument, use Rocq's `Program Fixpoint` with a `{measure ...}` clause:

```coq
From Stdlib Require Import Program.
From Stdlib Require Import Arith Lia.

(* Euclidean GCD: terminates because second argument strictly decreases *)
Program Fixpoint gcd_euclid (a b : nat) {measure b} : nat :=
  match b with
  | 0 => a
  | S _ => gcd_euclid b (a mod b)
  end.
Next Obligation.
  (* Discharge termination proof obligation *)
  apply Nat.mod_upper_bound.
  lia.
Qed.
```

### Multi-Argument Lexicographic Measure

For functions with multiple decreasing arguments (e.g., Ackermann function):

```coq
From Stdlib Require Import Program.
From Stdlib Require Import Arith Lia.

Program Fixpoint ackermann (m n : nat) {measure (m + n)} : nat :=
  match m, n with
  | 0, _ => S n
  | S m', 0 => ackermann m' 1
  | S m', S n' => ackermann m' (ackermann (S m') n')
  end.
Next Obligation.
  (* Ackermann nested calls require lexicographic pairs or well-founded recursion *)
Admitted.
```

---

## 7. Canonical Forms & Inversion Lemmas

In large operational semantics developments, direct inversion inside theorems causes excessive branching. Always formulate explicit **Canonical Forms Lemmas** for values:

```coq
(** Canonical Forms for Arrow Types *)
Lemma canonical_forms_arrow : forall t T1 T2,
  value t ->
  has_type empty t (TArrow T1 T2) ->
  exists x t', t = TAbs x t'.
Proof.
  intros t T1 T2 Hval Htype.
  inv Hval; inv Htype.
  eexists; reflexivity.
Qed.
```

---

## 8. Specification Modeling: Boolean Equality vs. Propositional Negation in Branching Code

When proving correctness or roundtrip properties for programs with explicit boolean conditional branching (e.g., `if (tag =? TARGET) then ... else ...` or `if (tag s= TARGET) then ... else ...`), the formulation of preconditions in relational specifications directly impacts proof friction.

### The Friction: Propositional Negation vs. Boolean Decision

If an invariant or specification record models a non-matching condition as a pure proposition:

```coq
(* ❌ Cumbersome precondition: Requires reflection case-splitting *)
Hypothesis Hneq : tag <> TARGET.
```

In order to reduce the program expression `if (tag =? TARGET) then code_then else code_else`, direct `rewrite` cannot apply. The prover must execute:

```coq
destruct (tag =? TARGET) eqn:Heq.
- (* Branch 1: (tag =? TARGET) = true -> contradiction with Hneq *)
  apply eqb_eq in Heq; contradiction.
- (* Branch 2: Continues with code_else *)
```

### The Idiomatic Pattern: Direct Boolean Equations

Formulate relational specifications and inductive predicates using direct boolean equalities matching the program's conditional tests:

```coq
(* ✅ Idiomatic precondition: Directly aligns with the program AST *)
Hypothesis Hcond : (tag =? TARGET) = false.
```

With this formulation, reducing the conditional branch requires only a single, deterministic rewrite:

```coq
rewrite Hcond. (* Directly simplifies "if false then ... else code_else" to "code_else" *)
```

**Rule of Thumb**: When specifying operational contracts for functional parsers, deserializers, or state decoders, represent branching discriminator guards using their executable boolean equalities (`cond = true` or `cond = false`) rather than propositional equivalents (`P` or `~ P`).

---

## 9. Modeling Opaque Axiom Boundaries: Axiom-Boundary Behavioral Record Pattern

When verifying code generated by extraction pipelines (e.g., Charon / Aeneas from Rust, or C/LLVM translation tools), low-level memory operations, array indexing, and slice accesses (such as `array_index_usize` or `slice_index_usize`) are typically declared as non-computable, opaque `Axiom`s.

Directly reducing these primitives via `compute` or `simpl` in the Rocq kernel is impossible. Furthermore, introducing ad-hoc global `Axiom`s to assume specific access behaviors is strictly rejected by the soundness audit (`scripts/audit_axioms.py`).

### The Pattern: Behavioral Contract Records (Sort `Type`)

Instead of postulating global axioms, encapsulate the serialized data layout and primitive operations into a **Behavioral Contract Record** in sort `Type`:

```coq
(** [MODEL]
    Behavioral specification characterizing serialized byte slice for a structured packet.
    Defined in Type (not Prop) to ensure informative projections for elements. *)
Record is_serialized_packet (p : Packet_t) (bytes : slice u8) : Type :=
mk_is_serialized_packet {
  (* High-level invariant preservation *)
  ser_valid_magic : p.(packet_magic) = PACKET_MAGIC;
  ser_bytes_len   : slice_len bytes = PACKET_HEADER_LEN;

  (* Abstract byte values for structured fields *)
  ser_b0 : u8;
  ser_b1 : u8;
  ser_b2 : u8;
  ser_b3 : u8;

  (* Equational contracts modeling opaque axiom indexing results *)
  ser_idx0 : slice_index_usize bytes 0%usize = Ok ser_b0;
  ser_idx1 : slice_index_usize bytes 1%usize = Ok ser_b1;
  ser_idx2 : slice_index_usize bytes 2%usize = Ok ser_b2;
  ser_idx3 : slice_index_usize bytes 3%usize = Ok ser_b3;
  ser_idx4 : slice_index_usize bytes 4%usize = Ok p.(packet_version);

  (* Reconstruction contract for sub-arrays *)
  ser_reconstruct_magic :
    mk_array 4%usize [ser_b0; ser_b1; ser_b2; ser_b3] = PACKET_MAGIC;

  (* Slice residue extraction contract *)
  ser_extract_rest :
    slice_subslice bytes PACKET_HEADER_LEN = Ok slice_empty;
}.
```

### Key Architectural Guidelines

1. **Sort Discipline (`Record ... : Type`)**: Always declare behavioral contract records containing field values or byte witnesses in sort `Type` rather than `Prop`. If declared in `Prop`, Rocq's elimination restrictions prevent extracting informative projections (`ser_b0`, `ser_b1`) into computational terms.
2. **Local Equational Hypotheses**: By packaging indexing behaviors as fields in the record, proofs can destruct the record (`destruct Hser as [...]`) to bring concrete equational hypotheses into the local context.
3. **Soundness Audit Compliance**: Because all assumptions remain localized within the theorem's hypotheses, the resulting proof term remains completely closed (`Closed under the global context`), passing `scripts/audit_axioms.py` without introducing illegal axioms.

---

## 10. Monadic Chain Reduction in Aeneas / Result: Avoiding Destructive `cbn [bind]` Expansions

When verifying code generated by Aeneas from Rust, monadic error handling is represented via the `result` monad with bind notation (`x <- c1 ; c2`, expanded to `bind c1 (fun x => c2)`). A frequent proof hazard occurs when reducing intermediate steps in long monadic pipelines (such as deserializers, decoders, or stateful transaction validators).

### The Hazard: Premature Monadic AST Blowup

Executing `cbn [bind]` or `simpl` on a monadic chain without restriction triggers Rocq to eagerly unfold **every** occurrence of `bind` in the goal down to its pattern-matching definition:

```coq
match c1 with
| Ok x => match c2 with
          | Ok y => ...
          | Fail_ err => Fail_ err
          end
| Fail_ err => Fail_ err
end
```

Once subsequent `bind` occurrences are shredded into nested `match` trees:

1. Subterms like `c2` or subsequent slice operations (`core_slice_index_Slice_index`, `slice_index_usize`) become deeply embedded in pattern matching arms.
2. Equational rewrite lemmas (such as Behavioral Contract Record projections `rewrite (ser_extract_rest ...)` or `rewrite (ser_idx ...)`) immediately fail with:
   ```text
   Error: Found no subterm matching ... in the current goal
   ```
3. Proof scripts degrade into dozens of manual `destruct` and `change` invocations attempting to recover the syntactic shape.

### The Correct Idiom: Direct Consecutive Rewriting

#### Rule 1: Chain Equational Rewrites Directly Without Intermediate `cbn [bind]`

When each operation is characterized by an equational lemma or behavioral record projection of the form `op arg = Ok val`:

- Apply consecutive `rewrite` steps directly without interleaving `cbn [bind]`.
- Rocq's unification engine transparently matches subterms inside `bind` without requiring `bind` to be reduced to `match`.

```coq
(* ❌ Fragile: Premature reduction alters the AST shape of subsequent bindings *)
rewrite (ser_vault_cast_slot_count v bytes Hser).
cbn [bind]. (* Destroys subsequent "bind (core_slice_index ...)" into nested match *)
rewrite (ser_vault_extract_rest2 v bytes Hser). (* Fails: Found no subterm matching! *)

(* ✅ Robust: Direct rewrite chaining maintains syntactic structure *)
rewrite (ser_vault_cast_slot_count v bytes Hser).
rewrite (ser_vault_extract_rest2 v bytes Hser).
rewrite (ser_vault_record_payload v bytes Hser).
cbn [bind]. (* Only reduce bind when all component operations are rewritten to Ok/Return *)
```

#### Rule 2: Localized Unfolding with Occurrence Specifiers (`unfold bind at 1`)

When an intermediate step strictly requires exposing the head value to proceed with a dependent computation or case split, do not use `cbn [bind]` globally. Instead, unfold exclusively the leftmost monadic bind:

```coq
(* Selectively unfold only the outer head bind, leaving the tail pipeline intact *)
unfold bind at 1.
```

#### Rule 3: Avoid Superfluous `change` Coercions

Avoid inserting speculative `change` tactics to cast intermediate types (e.g., between polymorphic slice projections and concrete byte records). Rely on explicit projection equations and `subst` / `rewrite` to let the Rocq unification algorithm verify type compatibility naturally.

---

## 11. Surgical Type Normalization for Aeneas / Charon Aliases (`usize` vs `scalar Usize`)

When verifying programs extracted with Aeneas from Rust, primitive scalar types are frequently defined as transparent aliases:

```coq
Definition usize := scalar Usize.
Definition u8 := scalar U8.
```

### The Unification Hazard in `rewrite`

Rocq's `rewrite` engine matches subterms syntactically before attempting definitional conversion. If a lemma specifies `core_ops_range_RangeFrom_t usize` but the subterm in the goal was instantiated with `core_ops_range_RangeFrom_t (scalar Usize)` (or constructor `@mkcore_ops_range_RangeFrom_t (scalar Usize)`), `rewrite` fails with:

```text
Error: Found no subterm matching ... in the current goal
```

### Dangerous Anti-Pattern: Global Alias `change`

```coq
(* ❌ DANGEROUS: Unfolds and corrupts numeric literals like 16%usize across the goal *)
change (scalar Usize) with usize.
```

Executing `change (scalar Usize) with usize` without structural bounds replaces subterms inside constant literals, bounds proofs, and integer arithmetic constraints, causing cascading failure in subsequent tactics.

### The Idiom: Surgical Constructor & Record Type Alignment

Wrap the alias normalization in the immediate surrounding record type or constructor to protect numeric literals:

```coq
(* 1. Normalize record type parameter *)
change (core_ops_range_RangeFrom_t (scalar Usize)) with (core_ops_range_RangeFrom_t usize).

(* 2. Normalize constructor application with explicit type argument *)
change (@mkcore_ops_range_RangeFrom_t (scalar Usize)) with (@mkcore_ops_range_RangeFrom_t usize).

(* 3. Rewrite now succeeds without syntactic head mismatch *)
rewrite (slice_index_range_from ...).
```
