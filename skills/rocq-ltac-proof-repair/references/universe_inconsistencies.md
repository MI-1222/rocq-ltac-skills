# Universe Inconsistencies & Level Stratification

This reference provides techniques to diagnose and repair universe hierarchy cycles, sort overflows (`Set+1 <= Set`), and universe polymorphism issues in Rocq 9.0+ and Coq 8.20.

---

## 1. Error Signatures

### Signature A: Set Overflow / Self-Referential Quantification

```text
Error: The term "forall X : Set, X -> X" has type "Type" while it is expected to have type "Set"
(universe inconsistency: Cannot enforce Set+1 <= Set).
```

### Signature B: Cumulative Hierarchy Positive Cycle

```text
Error: Universe inconsistency: Cannot enforce Top.42 <= Top.41 because Top.41 <= Top.42.
```

or

```text
Error: Universe inconsistency: Cannot enforce Type@{i} <= Type@{j}.
```

A circular constraint $u < v \le \dots \le u$ was generated while elaborating higher-order terms or storing types inside inductive structures.

---

## 2. Root Cause & Theoretical Background

1. **Stratified Universe Hierarchy in CIC**:
   To maintain logical consistency and prevent paradoxes arising from type self-containment ($\text{Type} : \text{Type}$), Rocq stratifies types into an infinite hierarchy of universes:
   $$\text{Prop} \subset \text{Type}_0 \subset \text{Type}_1 \subset \text{Type}_2 \subset \dots$$
   - `Prop` is **impredicative**: a proposition can quantify over all propositions ($\forall P : \text{Prop}, P$) and still reside in `Prop`.
   - `Set` and `Type` are **predicative**: quantifying over `Type_i` produces a term residing strictly in $\text{Type}_{i+1}$.
   - Attempting to declare a type that quantifies over all `Set` while forcing the resulting type to live in `Set` generates the fatal constraint `Set+1 <= Set`.
2. **Universe Constraint Graphs (`kernel/uGraph.ml`)**:
   Rocq represents universe constraints as a weighted directed graph $(\text{Univ}_1, w, \text{Univ}_2)$:
   - An edge $u \xrightarrow{0} v$ represents $u \le v$.
   - An edge $u \xrightarrow{+1} v$ represents $u < v$.
     When adding a constraint $u \le v$, if a path from $v$ to $u$ already exists with total weight plus the new edge weight greater than zero ($W > 0$), a **positive cycle** is formed, and `UniverseInconsistency` is raised.
3. **Monomorphic vs. Polymorphic Definitions**:
   By default, definitions in Rocq are universe-monomorphic: each occurrence of `Type` is assigned a fixed global universe level. When a generic data structure (e.g., containers, monads, or state transformers) is reused at different universe levels, monomorphic definitions force all levels to coalesce, frequently causing positive cycles.
4. **Universe Polymorphism (`#[universes(polymorphic)]`)**:
   Adding universe polymorphism allows definitions to be parameterized by abstract universe levels (`Univ.AUContext.t`), instantiating fresh universe variables at each usage site.

---

## 3. Anti-Patterns to Avoid

- ❌ **Replacing `Type` with `Set` indiscriminately**: Forcing definitions into `Set` when they contain polymorphic functions triggers immediate `Set+1 <= Set` errors.
- ❌ **Disabling universe checking**: Never use unsafe compiler flags (e.g., `-type-in-type`) to silence errors, as this destroys logical consistency.
- ❌ **Ignoring transitive cycles**: Attempting to fix a cycle by tweaking random lemma statements rather than inspecting the universe dependency graph.

---

## 4. Concrete Prescriptions (Before & After)

### Case 1: Promoting `Set` to `Type`

**Failing Code (Before):**

```Coq
(* Attempting to define a polymorphic identity in Set *)
Definition PolyId : Set := forall X : Set, X -> X.
(* Error: The term "forall X : Set, X -> X" has type "Type"
   while it is expected to have type "Set" (Set+1 <= Set). *)
```

**Repaired Code (After):**

```Coq
(* Promote the return sort to Type *)
Definition PolyId : Type := forall X : Type, X -> X.
```

---

### Case 2: Universe Polymorphism for Generic Datatypes

When a container or transformer is used at multiple levels and triggers a cycle:

**Failing Code (Before - Monomorphic):**

```Coq
Inductive Box (A : Type) : Type :=
| box : A -> Box A.

(* Later in the file: nesting Box with types at different universe levels *)
Definition box_type := Box Type.
(* Subsequent reuse may cause: Universe inconsistency: Cannot enforce Top.1 <= Top.2 *)
```

**Repaired Code (After - Universe Polymorphic):**

```Coq
#[universes(polymorphic)]
Inductive Box (A : Type) : Type :=
| box : A -> Box A.

#[universes(polymorphic)]
Definition wrap (A : Type) (x : A) : Box A := box A x.
```

For structures with universe subtyping across levels:

```Coq
#[universes(polymorphic, cumulative)]
Record Container (A : Type) := {
  elem : A
}.
```

---

### Case 3: Modern Universe Syntax in Rocq 9.0+

Legacy Coq syntax `Type@{s;l}` triggers `deprecated-type-sort-poly-syntax`. Rocq 9.0+ standardizes bracketed attributes:

**Modern Syntax (Rocq 9.0+):**

```Coq
#[universes(polymorphic)]
Definition id_poly (A : Type) (x : A) : A := x.
```

---

## 5. Fallback Procedures

1. **Inspecting Universe Levels (`Set Printing Universes`)**:
   Turn on universe printing to display internal universe indexes ($Top.1, Top.2, \dots$):
   ```Coq
   Set Printing Universes.
   Check (Box Type).
   Unset Printing Universes.
   ```
2. **Stratifying Higher-Order Data Representations**:
   Instead of storing raw types inside a datatype, store an inductive representation of syntax (a shallow embedding) or parameterize by an explicit signature:
   ```Coq
   (* First-order syntax representation avoids higher-order universe cycles *)
   Inductive ty :=
   | TyNat
   | TyBool
   | TyArrow : ty -> ty -> ty.
   ```
