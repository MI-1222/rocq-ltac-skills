# Namespaces, Module Paths & Scope Resolution

This reference provides techniques for resolving identifier lookups, migrating from legacy `Coq` namespaces to `Corelib` and `Stdlib` in Rocq 9.0+, and managing notation scopes (`Z_scope`, `string_scope`).

---

## 1. Error Signatures

### Signature A: Missing Identifier / Reference

```text
Error: The reference Nat.add_comm was not found in the current environment.
```

or

```text
Error: The reference Z was not found in the current environment.
```

### Signature B: Deprecated Namespace / Path Resolution Error

```text
Warning: From Coq is deprecated since 9.0. Use From Stdlib instead.
```

or

```text
Error: Cannot find a physical path bound to logical path Stdlib.Arith with prefix Stdlib.
```

### Signature C: Scope Mismatch (Implicit Nat Overload)

```text
The term "1" has type "nat" while it is expected to have type "Z".
```

The numeral `1` or operators `+`, `-` are bound to `nat_scope` by default instead of `Z_scope`.

---

## 2. Root Cause & Theoretical Background

1. **Rocq 9.0+ Namespace Reorganization**:
   In Rocq 9.0+, the legacy monolithic `Coq` library hierarchy was split into distinct logical libraries:
   - **`Corelib`**: Foundational prelude, core inductive types, logic axioms, and basic datatype constructors.
   - **`Stdlib`**: Standard data structures (`List`, `Arith`, `ZArith`, `Strings`, `Bool`, `Sets`, `FSets`).
     Writing `From Coq Require Import ...` triggers `deprecated-from-Coq` warnings or fails if `_CoqProject` strictly binds `Stdlib`.
2. **Notation Scopes in Gallina**:
   Rocq uses a scope stack to interpret overloaded symbols (`+`, `*`, `<`, `-`) and numeric literals.
   - Default: `nat_scope`.
   - Integer arithmetic: `Z_scope`.
   - String manipulation: `string_scope`.
     Without opening the scope (`Open Scope Z_scope.`) or delimiting terms (`(1 + 2)%Z`), terms default to `nat`.

---

## 3. Anti-Patterns to Avoid

- ❌ **Inventing ad-hoc module names**: Guessing module locations without using `Locate` or `Search`.
- ❌ **Mixing bare `Coq` and `Stdlib` prefixes in the same project**: Inconsistent imports lead to duplicate symbol definitions or type incompatibility.
- ❌ **Omitting Scope Delimiters**: Mixing integer `Z` and `nat` operations in the same expression without explicit `%Z` or `%nat` tags.

---

## 4. Concrete Prescriptions (Before & After)

### Case 1: Migrating from `Coq` to `Stdlib` (Rocq 9.0+)

**Failing / Deprecated Code (Before):**

```Coq
From Coq Require Import Arith.
From Coq Require Import List.
From Coq Require Import Lia.
From Coq Require Import Strings.String.
```

**Repaired Code (After):**

```Coq
From Stdlib Require Import Arith.
From Stdlib Require Import List.
From Stdlib Require Import Lia.
From Stdlib Require Import Strings.String.
Import ListNotations.
```

#### Mapping Table for Common Libraries:

| Legacy Coq 8.20 Import                    | Modern Rocq 9.0+ Import                      | Primary Contents                        |
| :---------------------------------------- | :------------------------------------------- | :-------------------------------------- |
| `From Coq Require Import Arith.`          | `From Stdlib Require Import Arith.`          | Natural number operations, `Nat` module |
| `From Coq Require Import Lia.`            | `From Stdlib Require Import Lia.`            | Linear integer arithmetic (`lia`)       |
| `From Coq Require Import List.`           | `From Stdlib Require Import List.`           | Lists and `ListNotations`               |
| `From Coq Require Import ZArith.`         | `From Stdlib Require Import ZArith.`         | Binary integers (`Z`), `Z_scope`        |
| `From Coq Require Import Strings.String.` | `From Stdlib Require Import Strings.String.` | Byte/Ascii strings, `string_scope`      |
| `From Coq Require Import Bool.`           | `From Stdlib Require Import Bool.`           | Boolean functions and reflection        |
| `From Coq Require Import Program.`        | `From Stdlib Require Import Program.`        | `Program Fixpoint`, obligations         |

---

### Case 2: Opening Notation Scopes for Integers (`Z`)

**Failing Code (Before):**

```Coq
From Stdlib Require Import ZArith.

Definition offset : Z := 1 + 2.
(* Fails: The term "1 + 2" has type "nat" while it is expected to have type "Z" *)
```

**Repaired Code (Option A: Explicit Open Scope):**

```Coq
From Stdlib Require Import ZArith.
Open Scope Z_scope.

Definition offset : Z := 1 + 2. (* Evaluates correctly to Z *)
```

**Repaired Code (Option B: Term-Level Scope Delimitation `%Z`):**

```Coq
From Stdlib Require Import ZArith.

Definition offset : Z := (1 + 2)%Z. (* Delimits expression directly *)
```

---

### Case 3: Resolving Unknown Notations or Constants

When encountering an unknown symbol or identifier:

1. **Locate the defining module**:
   ```bash
   python3 skills/rocq-ltac-interactive-proof/scripts/rocq_goal.py --file <file.v> --line <N> --search "Locate \"++\""
   ```
   Output:
   ```text
   Notation "x ++ y" := (app x y) : list_scope (default interpretation)
   ```
2. **Import the required module and open the scope**:
   ```Coq
   From Stdlib Require Import List.
   Import ListNotations.
   ```

---

## 5. Fallback Procedures

1. **Use Fully Qualified Names**:
   If an import shadows a name or cannot be imported globally, use its fully qualified path:
   ```Coq
   apply Stdlib.Arith.PeanoNat.Nat.add_comm.
   ```
2. **Inspect Active Scopes**:
   If notations behave unexpectedly:
   ```Coq
   Print Scopes.
   Print Visibility.
   ```
3. **Verify Logical Path in `_CoqProject`**:
   Ensure `_CoqProject` includes the appropriate logical bindings:
   ```text
   -Q theories MyProject
   ```
