# Vernacular Query Reference & Lemma Search Guide

This reference documents the query commands available in the Rocq (formerly Coq) environment—`Search`, `Locate`, `About`, `Check`, and `Print`.

---

## 1. Principles of Vernacular Queries & Token Conservation

In autonomous formal verification, running broad or unconstrained search queries (e.g., `Search (_ = _).`) returns thousands of lines of output, overwhelming LLM attention buffers and causing the "Lost in the Middle" phenomenon.

### Operational Principles

1. **Constrain First**: Always qualify search patterns with positional modifiers (`concl:`, `headconcl:`, `hyp:`, `headhyp:`) or target types before executing.
2. **Limit Result Counts**: By default, `scripts/rocq_goal.py` limits search results to 25 entries (`--max-search 25`).
3. **Two-Stage Lookup for Notations**: When encountering an unfamiliar symbol (such as `++`, `==>`, or `|->`), never query it directly with `Search`. First execute `Locate "<symbol>"` to identify the canonical underlying identifier, then query that identifier with `Search`.
4. **Inspect Arguments Before Applying**: Before issuing an `apply my_lemma` tactic, inspect its implicit argument structure using `About my_lemma.` to avoid argument count mismatch errors.

---

## 2. High-Precision `Search` Patterns

The `Search` vernacular command searches loaded libraries for lemmas and constants matching specified Gallina patterns and constraints.

### Syntax Specification

```coq
Search query_item+ [inside [ qualid+ ] | outside [ qualid+ ] | in Top]? .
```

### Complete Query Modifiers Table

| Pattern / Modifier                 | Syntax Example                                | Meaning                                                                                    |
| :--------------------------------- | :-------------------------------------------- | :----------------------------------------------------------------------------------------- |
| **Gallina Term Pattern**           | `Search (_ + _ <= _ + _).`                    | Matches any lemma containing addition within an inequality.                                |
| **Non-Linear Pattern**             | `Search (?x + ?y = ?y + ?x).`                 | Matches commutativity patterns where terms `?x` and `?y` are unified.                      |
| **Conclusion Filter (`concl:`)**   | `Search concl:(_ <= _).`                      | Restricts search to lemmas whose conclusion is an inequality (ideal for backward `apply`). |
| **Head Conclusion (`headconcl:`)** | `Search headconcl:le.`                        | Matches lemmas whose conclusion head constant is `le`.                                     |
| **Hypothesis Filter (`hyp:`)**     | `Search hyp:(_ = _).`                         | Matches lemmas that require an equality hypothesis.                                        |
| **Head Hypothesis (`headhyp:`)**   | `Search headhyp:gt.`                          | Matches lemmas that require a hypothesis whose head symbol is `gt`.                        |
| **Negation Filter (`-`)**          | `Search Nat.add -Nat.mul.`                    | Includes lemmas mentioning `Nat.add` while excluding any mentioning `Nat.mul`.             |
| **Disjunction (`[ ... \| ... ]`)** | `Search [ concl:(_ = _) \| concl:(_ <> _) ].` | Matches lemmas concluding in either equality or disequality.                               |

### Practical Search Recipes

#### Backward Reasoning (Applying to Target)

When trying to solve a goal `x <= y + z`:

```coq
Search concl:(_ <= _ + _) inside Stdlib.Arith.
```

#### Monotonicity Lemmas

When preserving inequalities across operations:

```coq
Search (?x <= ?y -> _ ?x <= _ ?y).
```

#### Rewriting Equalities

When seeking simplification rules for a specific function:

```coq
Search (?f (_ :: _) = _) inside Stdlib.Lists.List.
```

---

## 3. Module Scope Scoping (`inside`, `outside`, `in Top`)

By default, `Search` searches across all currently loaded modules. Restricting module scope speeds up search and avoids namespace pollution from unrelated libraries.

### Scope Modifiers

1. **`inside [ <ModulePath> ... ]`**: Restricts results exclusively to definitions in the specified library or module hierarchy:
   ```coq
   Search concl:(_ <= _) inside Stdlib.Arith.PeanoNat.Nat.
   ```
2. **`outside [ <ModulePath> ... ]`**: Excludes standard library definitions or legacy modules:
   ```coq
   Search (_ + _) outside Stdlib.Reals.
   ```
3. **`in Top.`**: Restricts search exclusively to definitions, lemmas, and inductive types declared in the current active file:
   ```coq
   Search _ in Top.
   ```

> **Important**: `Search` only inspects modules that are **already loaded** in memory. If a required library (e.g., `From Stdlib Require Import List.`) has not been imported, `Search` will yield no results for its contents. Ensure necessary prelude imports are in scope.

---

## 4. `Locate` for Notations & Identifier Resolution

The `Locate` command maps user-facing notations, symbols, and unqualified identifiers to their fully qualified canonical definitions.

### Mapping Custom Notations to Definitions

When reading or generating code involving notations:

```coq
Locate "++".
(* Output: Notation "x ++ y" := (app x y) : list_scope *)
```

Once the underlying function `app` is identified, query its theorems directly:

```coq
Search app inside Stdlib.Lists.List.
```

### Resolving Ambiguous Identifiers

When multiple libraries define homonymous identifiers:

```coq
Locate add.
(* Output:
   Constant Nat.add (qualified to Stdlib.Arith.PeanoNat.Nat.add)
   Constant Pos.add (qualified to Stdlib.PArith.BinPos.Pos.add)
*)
```

---

## 5. `About` for Implicit & Maximally Inserted Arguments

The `About` command displays full metadata for a constant or lemma, including its type, module location, and argument status.

### Example Output & Interpretation

```coq
About eq_trans.
```

Output:

```text
eq_trans : forall [A : Type] {x y z : A}, x = y -> y = z -> x = z

Arguments eq_trans [A]%type_scope {x y z} (e1 e2)%core_scope
```

### Argument Annotations

| Notation    | Argument Kind                   | Caller Responsibility                                                           |
| :---------- | :------------------------------ | :------------------------------------------------------------------------------ |
| `[ A ]`     | **Maximally Inserted Implicit** | Automatically inferred even without arguments following. Never pass explicitly. |
| `{ x y z }` | **Standard Implicit Argument**  | Inferred from context when subsequent explicit arguments are supplied.          |
| `( e1 e2 )` | **Explicit Argument**           | Must be passed explicitly by the caller: `apply (eq_trans H1 H2).`              |

If you need to bypass implicit argument inference and supply all arguments manually, prefix the identifier with `@`:

```coq
apply (@eq_trans nat x y z H1 H2).
```

---

## 6. `Check` and `Print` for Local Terms & Inductive Types

### `Check <term>`: Type Validation in Context

Use `Check` to verify whether an expression or lemma instance is well-typed under the current hypotheses before invoking a tactic like `apply` or `rewrite`:

```coq
Check (Nat.add_comm x y).
(* Output: x + y = y + x : Prop *)
```

### `Print <ident>`: Examining Inductive Structures & Definitions

Use `Print` to inspect the inductive constructors, record fields, or transparent body of a definition:

```coq
Print list.
(* Output:
   Inductive list (A : Type) : Type :=
   | nil : list A
   | cons : A -> list A -> list A.
*)
```

This is essential for determining the correct constructor names for `destruct`, `induction`, and `constructor` tactics.
