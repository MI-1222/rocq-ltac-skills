# Rocq Gallina and Vanilla Ltac Syntax Reference

This document serves as the canonical grammar, lexical, and vernacular syntax specification for formal program verification and semantics in Rocq 9.0+ (with backward compatibility for Coq 8.20). All AI agents and formalization scripts must adhere strictly to these rules to guarantee deterministic compilation and error-free AST parsing.

## 1. Lexical Conventions & Lexer Architecture

Rocq's lexical analyzer (`cLexer.ml`) processes input through strict tokenization boundaries. Deviations at the lexer level halt compilation before the tactic engine or type elaborator can evaluate terms.

### 1.1. Sentence Terminator (`.`)

A period (`.`) is parsed as a vernacular sentence terminator **if and only if it is immediately followed by whitespace ( , `\t`, `\n`, `\r`) or the end of file (`EOF`)**.

- **Valid terminators**:
  ```Coq
  intros x y. induction x.
  ```
  ```Coq
  Proof.
    reflexivity.
  Qed.
  ```
- **Invalid (Lexer Collisions)**:
  - `intros x.induction x.` — Parsed as an invalid single token `x.induction` rather than two tactics.
  - `Theorem add_0_r : forall n, n + 0 = n.Proof.` — Collides into an invalid identifier `n.Proof`.
- **Exemptions (Non-terminating periods)**:
  - Qualified module paths: `Nat.add`, `Coq.Init.Prelude`, `List.map`.
  - Record field projections: `state.env`, `r.(field)`.
  - Floating-point literals: `1.0`, `3.1415`.
  - Periods occurring inside string literals or comments.

### 1.2. Recursive Nested Comments (`(* ... *)`)

Comments are delimited by `(*` and `*)` and support **arbitrary depth recursive nesting**.

- Opening `(*` increments the parser comment counter; closing `*)` decrements it.
- Whitespace, newlines, and sentence-terminating periods inside comments are masked and do not affect outer code execution.
- Any unmatched opening `(*` remaining at `EOF` raises a fatal lexer error:`Syntax Error: Lexer: Unterminated comment`.

```Coq
(* Level 1 comment
   (* Nested Level 2 comment
      (* Nested Level 3 comment *)
      Still Level 2 *)
   Back to Level 1 *)
```

### 1.3. String Literals & Escaping (`"..."`)

Strings are enclosed in double quotes (`"..."`) and can span multiple lines.

- Double quotes inside string literals are escaped exclusively by **doubling the double quote (`""`)**.
- Backslash escaping (`\"`) is invalid in standard Gallina and triggers an illegal character error.
- An unclosed double quote reaching `EOF` raises:`Syntax Error: Lexer: Unterminated string`.

```Coq
Definition greeting : string := "Hello, ""World""!".
Definition multiline : string := "Line 1
Line 2".
```

## 2. Gallina Specification Grammar (Core Declarations)

Gallina is the functional specification and term language of Rocq. Program definitions, inductive types, and relations must use pure term-mode syntax.

### 2.1. Inductive Types & Relations

Inductive declarations define data types, transition systems, and inference rules.

```Coq
(* Parameterized inductive data type *)
Inductive list (A : Type) : Type :=
| nil : list A
| cons : A -> list A -> list A.

(* Inductive proposition / evaluation relation *)
Inductive step : tm -> tm -> Prop :=
| ST_AppAbs : forall x T t12 v2,
    value v2 ->
    step (tm_app (tm_abs x T t12) v2) (subst x v2 t12)
| ST_App1 : forall t1 t1' t2,
    step t1 t1' ->
    step (tm_app t1 t2) (tm_app t1' t2)
| ST_App2 : forall v1 t2 t2',
    value v1 ->
    step t2 t2' ->
    step (tm_app v1 t2) (tm_app v1 t2').
```

### 2.2. Functions & Definitions (`Definition`, `Fixpoint`)

- **Non-recursive Definitions**:
  ```Coq
  Definition id {A : Type} (x : A) : A := x.
  ```
- **Recursive Functions (`Fixpoint`)**: Recursive functions must be structurally decreasing on one argument to satisfy Rocq's termination checker (Calculus of Inductive Constructions).
  - When a recursive function accepts multiple arguments, **always declare the structural decreasing argument explicitly** using `{struct <arg>}` to avoid `Cannot guess decreasing argument of fix`.
  ```Coq
  Fixpoint plus (n m : nat) {struct n} : nat :=
    match n with
    | O => m
    | S p => S (plus p m)
    end.
  ```

### 2.3. Pattern Matching (`match ... with ... end`)

Every pattern matching construct in Gallina must be closed with an explicit `end` keyword.

- **Standard Pattern Match**:
  ```Coq
  Definition is_zero (n : nat) : bool :=
    match n with
    | O => true
    | S _ => false
    end.
  ```
- **Dependent Pattern Match**: When the return type depends on the matched term or constructor index, use `as ... in ... return ...`:
  ```Coq
  Definition head {A : Type} {n : nat} (v : vec A (S n)) : A :=
    match v in vec _ (S m) return A with
    | vcons _ h _ => h
    end.
  ```

### 2.4. Records & Structures

```Coq
Record state : Type := mk_state {
  pc : nat;
  regs : nat -> nat;
  mem : nat -> nat
}.
```

### 2.5. Implicit Arguments (`Arguments`)

Explicitly designate implicit parameters to clean up term calls:

```Coq
Arguments nil {A}.
Arguments cons {A} _ _.
Arguments mk_state pc regs mem.
```

### 2.6. Scopes & Notations

Always configure scopes explicitly rather than relying on ambiguous implicit bindings:

```Coq
Open Scope string_scope.
Open Scope list_scope.
Open Scope nat_scope.

(* Local delimiter annotation *)
Compute (3 + 4)%nat.
Compute ("abc" ++ "def")%string.
```

## 3. Rocq 9.0+ Modernization: Namespaces, Attributes & Universes

Rocq 9.0 introduced structural reorganization to separate the core logical engine from the standard library.

### 3.1. Standard Library Namespaces (`Stdlib` / `Corelib`)

- **Core / Prelude Declarations**: Reside under `From Corelib Require Import ...`.
- **Standard Library**: Reside under `From Stdlib Require Import ...`.
- ❌ **Deprecated**: `From Coq Require Import ...` triggers `deprecated-from-Coq` warnings or errors in Rocq 9.0+.
- **Cross-compatibility with Coq 8.20**: If maintaining compatibility with older Coq environments where `Stdlib` does not exist, control logical path bindings via `_CoqProject`.

```Coq
(* ✅ Correct Modern Rocq 9.0+ *)
From Stdlib Require Import Arith.
From Stdlib Require Import Lists.List.
From Stdlib Require Import Lia.
Import ListNotations.
```

### 3.2. Standardized Attribute Syntax (`#[...]`)

Bare command-prefix modifiers are deprecated. Locality and behaviors must be declared via bracketed attributes:

| **Legacy Syntax (Deprecated) doc02-syntax.md** | **Standard Modern Syntax (Rocq 9.0+) doc02-syntax.md** | **Scope / Meaning**                                |
| ---------------------------------------------- | ------------------------------------------------------ | -------------------------------------------------- |
| `Local Hint Resolve foo : core.`               | `#[local] Hint Resolve foo : core.`                    | Restricts hint strictly to current module/section. |
| `Global Hint Constructors step : core.`        | `#[global] Hint Constructors step : core.`             | Exports hint across global module dependencies.    |
| `Export Instance foo : Bar.`                   | `#[export] Instance foo : Bar.`                        | Exports instance when module is imported.          |
| `Local Definition x := 1.`                     | `#[local] Definition x := 1.`                          | Local definition inside a module.                  |

### 3.3. Linear Integer Arithmetic: `lia` vs `omega`

- `omega`, `romega`, and `sos` were permanently removed from the engine.
- Always import `From Stdlib Require Import Lia.` and use `lia.`.
- For non-linear integer terms, pre-process with `zify` and call `nia.`.

### 3.4. Universe Polymorphism Syntax

- ❌ **Deprecated**: `Type@{s;l}` (triggers `deprecated-type-sort-poly-syntax`).
- ✅ **Modern**: `Univ@{s;l}`.

## 4. Pure Vanilla Ltac Tactic Grammar

All proof scripts must be implemented exclusively in **Pure Vanilla Ltac**. SSReflect / MathComp syntax is strictly forbidden.

### 4.1. SSReflect Dialect Elimination Table

Mixing SSReflect and Vanilla Ltac causes immediate parser rejection. Follow these direct conversions:

| **Operation**           | **❌ FORBIDDEN (SSReflect) doc02-syntax.md** | **✅ MANDATORY (Vanilla Ltac) doc02-syntax.md** |
| ----------------------- | -------------------------------------------- | ----------------------------------------------- |
| **Intro variables**     | `move=> x y H.`                              | `intros x y H.`                                 |
| **Destructuring intro** | `move=> [x [y H]].`                          | `intros [x [y H]].`                             |
| **Terminal solve**      | `by [].` / `done.`                           | `now auto.` / `reflexivity.` / `easy.`          |
| **Forward assertion**   | `have H: P by ...`                           | `assert (H : P) by ...`                         |
| **Backward step**       | `suff: P by ...`                             | `enough (H : P) by ...`                         |
| **Branch discharge**    | `//`                                         | `; try easy.` / `; auto.`                       |
| **Simplification**      | `/=`                                         | `simpl.` / `cbn.`                               |
| **Outer congruence**    | `congr f.`                                   | `f_equal.`                                      |
| **Induction step**      | `elim: n => [\| n' IH].`                     | `induction n as [\| n' IH].`                    |
| **Push to goal**        | `move: x.`                                   | `revert x.`                                     |

### 4.2. Vanilla Ltac Categorical Reference

#### A. Forward Reasoning

```Coq
(* Introduce hypothesis into context *)
assert (Hle : x <= y).
{ apply le_trans with (m := z); assumption. }

(* Immediate forward assertion using by tactical *)
assert (Heq : a = b) by reflexivity.

(* Pose instantiated lemma *)
pose proof (Nat.add_comm x y) as Hcomm.

(* Specialize universally quantified hypothesis in-place *)
specialize (Hall x Hpremise).
```

#### B. Backward Reasoning

```Coq
(* Unification and resolution *)
apply H.
eapply lemma_with_existentials.
exact H.

(* Refine goal leaving explicit holes *)
refine (conj _ _).
```

#### C. Equational Reasoning

```Coq
(* Rewriting using equations *)
rewrite H.           (* Left to right *)
rewrite <- H.        (* Right to left *)
rewrite H in Hctx.   (* Rewrite inside local hypothesis *)

(* Simultaneous substitution of all variable equalities *)
subst.

(* Injectivity and discrimination on constructors *)
injection H as H1 H2.
discriminate.        (* Derives False from distinct constructor equality *)
```

#### D. Structural Case Analysis & Induction

```Coq
(* Structural case split *)
destruct x as [| x'] eqn:Heq.

(* Structural induction with named components *)
induction l as [| h t IH].
- (* Base: l = nil *)
  reflexivity.
- (* Step: l = cons h t *)
  simpl. rewrite IH. reflexivity.
```

## 5. Software Foundations & CompCert Proof Disciplines

When engineering proofs for programming language theory (e.g., _Software Foundations_, _CompCert_, _Iris_), adhere to standard proof engineering idioms:

### 5.1. Destructive Inversion Macro (`inv`)

Executing bare `inversion H.` without immediate cleanup pollutes the local context with stale hypotheses, duplicate variables, and redundant equations. Standardize the CompCert destruction macro:

```Coq
Ltac inv H := inversion H; subst; clear H.
```

- ❌ **Forbidden**: Leaving raw `inversion H.` in production proofs.
- ✅ **Mandatory**: Use `inv H.` (or explicitly `inversion H; subst; clear H.`).

### 5.2. Inductive Index Protection (`remember ... as ... eqn:...`)

If an inductive relation contains compound terms or constants in its index positions (e.g., `step (t_app t1 t2) t'` or `empty |- t \in T`), applying `induction` directly generalizes and erases these structural indices, rendering subgoals unprovable.

- ❌ **Anti-Pattern (Loses Index Information)**:
  ```Coq
  Theorem progress : forall t T, empty |- t \in T -> value t \/ (exists t', step t t').
  Proof.
    intros t T Ht.
    induction Ht. (* Fails: empty is generalized into arbitrary Gamma *)
  ```
- ✅ **Mandatory Pattern (Preserves Structural Equalities)**:
  ```Coq
  Theorem progress : forall t T, empty |- t \in T -> value t \/ (exists t', step t t').
  Proof.
    intros t T Ht.
    remember empty as Gamma eqn:HeqGamma.
    induction Ht; subst.
    - (* T_Var: empty has no variables; discriminate on HeqGamma *)
      discriminate.
    - (* T_Abs *) left. constructor.
    - (* T_App *) right. (* ... *)
  Qed.
  ```

## 6. Proof Structuring & Delimiters

### 6.1. Delimiter Placement

Proof boundaries must reside on dedicated standalone lines:

```Coq
Theorem sample_thm : forall n : nat, n + 0 = n.
Proof.
  induction n as [| n' IH].
  - reflexivity.
  - simpl. rewrite IH. reflexivity.
Qed.
```

Never concatenate proof commands onto a single line like `Proof. intros. reflexivity. Qed.`.

### 6.2. Focus Bullet Tree Invariants (`-`, `+`, `*`)

Bullets isolate subgoals into independent proof branches.

- Valid bullet symbols: `-`, `+`, `*`, `--`, `++`, `**`.
- ❌ **Period on Bullet is Forbidden**: `-. reflexivity.` or `+. lia.` triggers an immediate syntax error. Bullets are selectors, not vernacular sentences.
- **Strict Depth Ordering**: A sibling bullet cannot be opened until all subgoals under the active bullet are discharged (`Error: Wrong bullet -: Current bullet - is not finished.`).
- **Subproof Block Wrapping**: For deep branching (> 3 levels), replace excessive bullet chains with curly braces `{ ... }`:
  ```Coq
  destruct x.
  - (* Branch 1 *)
    destruct y.
    + (* Branch 1.1 *)
      { (* Explicit scope block *)
        destruct z.
        * reflexivity.
        * lia.
      }
    + (* Branch 1.2 *)
      reflexivity.
  - (* Branch 2 *)
    reflexivity.
  ```

## 7. Contract Invariance (Header Fence) & Soundness

To eliminate specification drift or reward hacking in autonomous agents, proof integrity is strictly enforced:

### 7.1. Header Fence

The entire signature of an assigned target theorem—from the leading declaration keyword (`Theorem`, `Lemma`, `Corollary`, `Proposition`, `Fact`, `Remark`) up to the colon `:` and closing period `.` before `Proof.`—is **completely immutable**.

- Binders must not be reordered, added, or removed.
- Premises must not be strengthened or trivialized (e.g., adding `False ->` is rejected as cheating).
- Conclusions must not be altered.

### 7.2. Frozen Specification Comments

Existing specification comments marked with `(** [SPEC] ... *)` are frozen contracts. Deleting, altering, or re-scoping specification docstrings is forbidden.

### 7.3. Zero Soundness Leaks

Final deliverables must contain **zero proof holes**:

- No `admit.` tactics.
- No `Admitted.` vernacular declarations.
- No unapproved `Axiom`, `Conjecture`, or `Parameter` additions.
- Every completed theorem must resolve in the Rocq kernel under `Closed under the global context`.
