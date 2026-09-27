# Classification Families Integration

## 1. Purpose

This document describes one unified family layer for the classification components
C, X₄, X₅, Y, and Z. All five components are implemented in
`LeanProject/Families.lean`, with source correspondence checked separately in
`Tests/FamiliesIntegration.lean`. This replaces the earlier C/Y-only scope in
these same files; there is no second integration layer.

The mathematical entries and parameter behavior of the existing C/Y definitions
are unchanged. Z comes from the existing source branch. After exhaustive local
search found no X implementation, the user authorized using the paper as the
source of the two fixed X matrices.

## 2. Source branches and files

Repository: https://github.com/ckhj123/lean_project

Working directory: `C:\Users\gaosh\Documents\lean\github_for_lean\lean_project`.
Working branch: `ModifiedWork`, at
`0d9588ae195d5839fe9d11a2c88d1c38a84c1981`.
Changes remain uncommitted for review.

Source snapshots:

- `origin/BarryShiqing`:
  `a45d13ee5cbee24a7629ee894665dbffc7f66713`.
- `origin/ckhj-lemma2`:
  `4a09a2be9599b371bd5a61e128f01c0f53719b17`.

| Component | Authoritative source used |
| --- | --- |
| C | `origin/BarryShiqing:LeanProject/CFamily.lean` |
| X₄ | Mykola Matviichuk, [arXiv:2310.05284v1](https://arxiv.org/html/2310.05284v1), Example 2.1; PDF page 5 |
| X₅ | Matviichuk, [published paper](https://doi.org/10.1007/s00029-024-01014-5), §3.1; PDF page 13; identical displayed matrix in arXiv:2310.05284v1 §3.1 |
| Y | `origin/ckhj-lemma2:LeanProject/Family_Y.lean` |
| Z | `origin/ckhj-lemma2:LeanProject/Family_Z.lean` |
| Graph interface / Lemma 1 | `LeanProject/SkewMatrixGraph.lean`, identical on both source snapshots |
| Lemma 2, inspected but separate | `LeanProject/Lemma2.lean`, identical on both source snapshots |

Paper bibliographic record: Mykola Matviichuk, *Elliptic log symplectic brackets
on projective bundles*, Selecta Mathematica, 31, article 20 (2025),
DOI 10.1007/s00029-024-01014-5. The author preprint is arXiv:2310.05284v1.
The X entries are transcribed without rescaling, permutation, or sign reversal.

### Repository/source search

Before editing the extension, the working tree, every local/remote-tracking branch,
all 16 reachable commits, historical file paths, notes/comments/tests, and Markdown
were inspected. Searches included X4, X5, X_4, X_5, xMatrix, Family_X,
Matrix X, exceptional/classification keywords, fixed Fin 4/5 matrix types,
and matrix literal notation. No repository source for X was found. There were
no tracked or non-dependency working-tree PDF/TeX papers or mathematical notes
providing those matrices. Historical `Family_Y_Z.lean` and
`Practice/Chapter1.lean` were also inspected; they contain draft Y data or
practice code, not X matrices. No tags provide additional source versions.

An older draft at `bae7f02193ece8adc32d6146138079d14cc00ca4` in
`LeanProject/Family_Y_Z.lean` used `N / 2 - 2` for Row1's cutoff. The requested
latest Y source uses `N / 2 + 2`. The integration preserves the latest snapshot
and the already-verified definition; it does not mix the older draft into it.

The source branches, remote-tracking refs, and local BarryShiqing ref have not
been modified, merged into, deleted, or moved. No commit or push was performed.

## 3. Shared project conventions

All production family definitions use `namespace SkewMatrixGraph`.
Rows are ordinary functions `Fin N → α`; public matrices are Mathlib's
`Matrix (Fin N) (Fin N) ℂ`. There is no custom Matrix or RowVector alias.

Y/Z integer source entries use the canonical embedding into ℂ. X constants
are interpreted directly in ℂ. No cast or wrapper is required when stating
`IsSkewSymmetric` or `IsSmoothableEdge` for any public family matrix.

There is one generic production shift:

```lean
def cyclicRightShift {n : ℕ} {α : Type*}
    (m : ℕ) (r : Fin n → α) : Fin n → α :=
  fun j => r (((finRotate n).symm^[m]) j)
```

T always means RIGHT shift: `(T r)_j = r_{j-1}`. The inverse rotation acts
on the read index; the old entry at column j moves to j+1 with wraparound.
The helper works even for an empty row. Its one-step subtraction theorem uses
`[NeZero n]` to make the Fin subtraction notation available.

Reusable public facts:

- `cyclicRightShift_zero`: shifting by zero is the identity.
- `cyclicRightShift_one_apply`: `shift 1 r j = r (j - 1)`.
- `cyclicRightShift_add`: `shift (a+b) r = shift b (shift a r)`.

Production contains only construction and structural lemmas. Private source
reference models, entry checks, and boundary counterexamples belong to the
separate test module, which is not imported by the production library.

## 4. C-family

The C source already has the correct namespace, complex coefficients, and
Mathlib matrix type. Its definition is retained.

`ValidC n k` means `1 ≤ k ∧ 3 ≤ n ∧ 2 * k < n`. The raw matrix definitions
remain total without requiring this predicate.

For the seed r(k), `cFirstRow n k` tests these cases in order:

1. j = 0: entry 0.
2. j ≤ k: entry 1.
3. n - k ≤ j: entry -1.
4. Otherwise: entry 0.

```text
row_i(C_{n,k}) = T^i r(k).
```

For d = gcd(n,k), I has type `Fin d → Bool`. The witness `hd : 0 < d`
makes i mod d a valid finite index, and false/true correspond to 0/1 through
`Bool.toNat`.

```text
row_i(C_{n,k,I}) = T^i r(k - I_{i mod d}).
```

The subtraction remains in ℕ, with its truncation behavior. No parameter
boundaries, condition priorities, or periodic-index construction changed.
The public definitions remain `ValidC`, `cFirstRow`, `cMatrix`, `cMatrixI`.

## 5. X_4

X₄ is a fixed matrix, transcribed in its displayed row/column order:

```text
  0   2  -1  -1
 -2   0   3  -1
  1  -3   0   2
  1   1  -2   0
```

Its source is the author's [Example 2.1](https://arxiv.org/html/2310.05284v1).
The public definition is

```lean
x4Matrix : Matrix (Fin 4) (Fin 4) ℂ
```

It uses Mathlib's direct matrix literal. The ±3 entries are intentional.
No row recurrence or shift machinery is invented for this fixed matrix.

## 6. X_5

X₅ is a distinct fixed matrix:

```text
  0   1   1  -1  -1
 -1   0   2   0  -1
 -1  -2   0   2   1
  1   0  -2   0   1
  1   1  -1  -1   0
```

The source is [published §3.1](https://doi.org/10.1007/s00029-024-01014-5),
also displayed identically in the preprint's §3.1. The public definition is

```lean
x5Matrix : Matrix (Fin 5) (Fin 5) ℂ
```

The off-diagonal zeros at (1,3) and (3,1) are preserved. X₅ is not identified
with the source Z definition at k = 0.

## 7. Y-family

N = 2(2k+1). The existing integrated seeds and recurrence are unchanged.

`yRow0` has ordered cases j = 0 → 0, j = 1 → 2, j < N/2 → 1,
otherwise -1. `yRow1` has ordered cases j = 0 → -2, j = 1 → 0,
j < N/2+2 → 1, otherwise -1.

```text
r_0 = yRow0 k
r_1 = yRow1 k
r_{i+2} = T² r_i
yMatrix k i j = yRow k i.val j
```

The source code accepts all k : ℕ. The classification's admissible range is
k ≥ 1; this is separate from the total code definition. The full cast
correspondence still includes k = 0.

## 8. Z-family

The source Z API has exactly one parameter k : ℕ. Its dimension is
N = 5(2k+1), which is odd. There is no additional index-set, parity-selection,
Boolean-sequence, or other parameter in this source implementation.

Let H = (N - 1) / 2. The following table gives the ordered cases, not unordered
sets of assignments. All column comparisons use the ordinary natural value
of a Fin N index.

| Seed | Fixed cases, in priority order | Remaining entry 1 condition | Otherwise |
| --- | --- | --- | --- |
| `zRow0` | j=0 → 0 | j < H+1 | -1 |
| `zRow1` | j=0 → -1; j=1 → 0; j=2 → 2; j=3 → 2 | j < H+1 | -1 |
| `zRow2` | j=0 → -1; j=1 → -2; j=2 → 0; j=3 → 2 | j < H+3 | -1 |
| `zRow3` | j=0 → -1; j=1 → -2; j=2 → -2; j=3 → 0 | j < H+5 | -1 |
| `zRow4` | j=0,1,2,3 → -1, in that order; j=4 → 0 | j < H+5 | -1 |

All strict inequalities, exceptional entries, signs, and case ordering are
retained. Natural subtraction in N-1 is retained. The five base rows feed the
exact source recurrence:

```text
r_0,...,r_4 = zRow0 k,...,zRow4 k
r_{i+5} = T⁵ r_i
zMatrix k i j = zRow k i.val j
```

The public matrix has type
`Matrix (Fin (5 * (2 * k + 1))) (Fin (5 * (2 * k + 1))) ℂ`.
Its row recurrence remains total on ℕ; it is not replaced by a guessed
closed form. The original parameter domain is preserved, including k = 0.

## 9. Incompatibilities found

- C/graph use `SkewMatrixGraph`; Y/Z use `Family_Y_n_k` /
  `Family_Z_n_k`.
- Y/Z have integer coefficients, whereas graph predicates accept complex
  matrices.
- Y/Z use custom `RowVector` and `Matrix` aliases, with Matrix shadowing the
  Mathlib name.
- C uses inverse-rotation iteration; Y/Z duplicate subtraction-based T and
  recursive useT. All represent the same right-shift direction.
- Row0, Row1, Row_Periodic, Y, and Z do not form a uniform family-prefixed API.
- Y/Z contain broad and redundant imports, evaluations, list conversion, and
  custom matrix pretty-printers.
- X has no source implementation in the repository; exact paper transcriptions
  are needed rather than new recursive constructions.
- The tracked starting working branch lacks the graph source file. It was
  restored during the preceding integration and is retained unchanged.
- The previous root theorem repair was unrelated to family integration. Its
  reversal is detailed below.

### Parameter-range difference and boundary discrepancy

The [paper's classification](https://link.springer.com/article/10.1007/s00029-024-01014-5)
uses k ≥ 1 for Y/Z. The source code defines both for every natural k.
The integration preserves this total extension and does not silently claim
classification properties at k = 0.

The test module proves `¬ IsSkewSymmetric (zMatrix 0)`: entries (0,4) and
(4,0) are both -1. It also proves that row 0 of yMatrix 0 sums to 2 and row 1
of zMatrix 0 sums to 2. These are source boundary behaviors outside the
classification's admissible range, not defects introduced by the integration.
Future family-property theorems must use the intended parameter assumptions.

Similarly, raw `cMatrix 2 1` is outside ValidC and is not skew-symmetric.
No raw family definition is automatically certified by its name.

The older Y draft's different Row1 cutoff is explicitly recorded in §2.
The source's informal Fin-addition comment `(i.val mod n)+1` is inaccurate
at wraparound; the correct value formula is `(i.val+1) mod n`. The comment
is not carried into production; the actual subtraction-based shift is retained.

## 10. Refactoring decisions

1. Extend the existing Families file rather than adding a competing family
   layer. C/Y code and its correspondence proofs remain unchanged.
2. Add two direct fixed Mathlib matrices for X with exact source order,
   coefficients, dimensions, and normalization.
3. Move Z into SkewMatrixGraph, embed its integer entries into ℂ, and reuse
   cyclicRightShift 5 in the original five-step recurrence.
4. Preserve total raw definitions and document the admissible classification
   parameter ranges separately; do not impose new witnesses on Y/Z callers.
5. Use standard types directly. Remove source Matrix/RowVector aliases,
   duplicate shift definitions, display-only code, and duplicate imports.
6. Keep source reference models private and in Tests. No production definition
   depends on those reference models.
7. Keep the source graph predicates and complete Lemma 1 statement/proof
   unchanged. No Lemma 1 edits are made in this extension.
8. Leave Lemma 2 separately available on the source snapshots. It is not needed
   to define or typecheck the family matrices.

### Unrelated root theorem modification reverted

The previous integration rewrote `ratio_neg_of_triangle_cond` and completed
its unfinished proof. Inspection showed that the pre-integration theorem
already compiles with its existing placeholder; this repair is not required
to import or build the family layer.

As explicitly requested, `LeanProject.lean` is restored to its exact
pre-integration HEAD content, with only this additional import:

```lean
import LeanProject.Families
```

The original theorem statement, implicit parameter inference, formatting,
and unfinished proof are restored. Thus the root still has its **pre-existing**
proof-placeholder warning. The final diff against HEAD introduces no new
placeholder: it adds only the import line. The integrated Families, Tests,
and restored graph module contain no proof placeholders or axiom declarations.

## 11. Mathematical fidelity

All correspondence theorems are in `namespace FamiliesIntegrationTest`.

| Component | Kernel-checked correspondence |
| --- | --- |
| C | `cMatrix_matches_source` for every n,k; `cMatrixI_matches_source` for every n,k,hd,I |
| X₄ | `x4Matrix_matches_source`, covering every Fin 4 × Fin 4 entry |
| X₅ | `x5Matrix_matches_source`, covering every Fin 5 × Fin 5 entry |
| Y | `y_shift_matches_source`, `yRow0_matches_source`, `yRow1_matches_source`, `yRow_matches_source`, `yMatrix_matches_source` |
| Z | `z_shift_matches_source`, `zRow0_matches_source` through `zRow4_matches_source`, `zRow_matches_source`, `zMatrix_matches_source` |

C's private reference retains the source's seed cases, lambda-wrapped inverse
rotation, Boolean conditional, and gcd-periodic index. The plain C equality
is definitional; the I-variant equality splits the Boolean converter's two
cases. Both proofs cover every natural parameter, without ValidC assumptions.

X references are integer entry-case transcriptions of the displayed matrices,
independent of the production matrix-literal representation.
Finite index case analysis proves all 16 and 25 entries after casting.
The kernel verifies the encoding agrees with this transcription; the paper-to-
transcription step is the explicitly cited, manually checked source boundary.

Y/Z references preserve the original integer seeds, Boolean equality tests,
subtraction-based T, recursively defined useT, and source row recurrences.
Shift equality is proved for every count and arbitrary coefficient type.
`cast_commutes_with_shift` establishes the generic ℤ → ℂ compatibility.
Y's row proof uses two-step induction; Z's recursive proof uses its five base
cases and the i+5 recurrence. Matrix equality follows entrywise for every k,
including k = 0, rather than from sampled evaluations.

Additional named tests prove X₄/X₅ skew-symmetry and zero row sums:
`x4_skewSymmetric`, `x5_skewSymmetric`,
`x4_rowSum_zero`, `x5_rowSum_zero`.
The boundary facts are
`zMatrix_zero_not_skewSymmetric`, `yMatrix_zero_row0_sum`,
and `zMatrix_zero_row1_sum`.

Right-shift wraparound and seed cutoffs are checked separately.
All public matrices typecheck directly with both graph predicates.
A test also applies Lemma 1 with its unchanged existing signature.

No mathematical semantics changed for C/Y/Z. The X definitions encode the
paper's displayed matrices exactly; no entries were inferred from memory,
rescaled, permuted, or reversed.

## 12. Old-to-new API table

New production names below are qualified by `SkewMatrixGraph`.
Old Y/Z names are qualified by `Family_Y_n_k` / `Family_Z_n_k`.

| Family | Source branch/file | Old definition | New definition | Change |
| --- | --- | --- | --- | --- |
| C | BarryShiqing / CFamily.lean | `ValidC` | `ValidC` | Same predicate and parameters; retained in Families. |
| C | BarryShiqing / CFamily.lean | `cFirstRow` | `cFirstRow` | Same ordered complex seed cases. |
| C | BarryShiqing / CFamily.lean | `cyclicShift` | `cyclicRightShift` | Shared helper, explicitly right-shifting and generic in coefficient type. |
| C | BarryShiqing / CFamily.lean | `bitValue b` | `Bool.toNat b` | Standard conversion; false/true remain 0/1. |
| C | BarryShiqing / CFamily.lean | `cMatrix` | `cMatrix` | Same entries; uses shared shift. |
| C | BarryShiqing / CFamily.lean | `cMatrixI` | `cMatrixI` | Same n,k,hd,I signature and row formula. |
| X₄ | Paper / Example 2.1 | displayed `𝒳₄` | `x4Matrix` | New exact fixed complex Mathlib matrix; no repository implementation existed. |
| X₅ | Paper / §3.1 | displayed `𝒳₅` | `x5Matrix` | New exact fixed complex Mathlib matrix; no repository implementation existed. |
| Y | ckhj-lemma2 / Family_Y.lean | `Row0` | `yRow0` | Family-prefixed name and ℤ → ℂ. |
| Y | ckhj-lemma2 / Family_Y.lean | `Row1` | `yRow1` | Same cases and N/2+2 cutoff; ℤ → ℂ. |
| Y | ckhj-lemma2 / Family_Y.lean | `T k r` | `cyclicRightShift 1 r` | Duplicate shift removed, direction retained. |
| Y | ckhj-lemma2 / Family_Y.lean | `useT k m r` | `cyclicRightShift m r` | Source recursive iteration replaced by equivalent shared helper. |
| Y | ckhj-lemma2 / Family_Y.lean | `Row_Periodic` | `yRow` | Same two-step recurrence; ℤ → ℂ. |
| Y | ckhj-lemma2 / Family_Y.lean | `Y` | `yMatrix` | Standard complex Mathlib matrix. |
| Z | ckhj-lemma2 / Family_Z.lean | `Row0` | `zRow0` | Same cases and H+1 cutoff; ℤ → ℂ. |
| Z | ckhj-lemma2 / Family_Z.lean | `Row1` | `zRow1` | Same exceptional entries and H+1 cutoff; ℤ → ℂ. |
| Z | ckhj-lemma2 / Family_Z.lean | `Row2` | `zRow2` | Same exceptional entries and H+3 cutoff; ℤ → ℂ. |
| Z | ckhj-lemma2 / Family_Z.lean | `Row3` | `zRow3` | Same exceptional entries and H+5 cutoff; ℤ → ℂ. |
| Z | ckhj-lemma2 / Family_Z.lean | `Row4` | `zRow4` | Same case priorities and H+5 cutoff; ℤ → ℂ. |
| Z | ckhj-lemma2 / Family_Z.lean | `T k r` | `cyclicRightShift 1 r` | Duplicate shift removed, direction retained. |
| Z | ckhj-lemma2 / Family_Z.lean | `useT k m r` | `cyclicRightShift m r` | Shared shift; all-count equivalence proved. |
| Z | ckhj-lemma2 / Family_Z.lean | `Row_Periodic` | `zRow` | Same five base rows and i+5 recurrence; ℤ → ℂ. |
| Z | ckhj-lemma2 / Family_Z.lean | `Z` | `zMatrix` | Same k parameter and N=5(2k+1); standard complex Mathlib matrix. |
| Y/Z | ckhj-lemma2 / Family_Y.lean, Family_Z.lean | `Family_Y_n_k`, `Family_Z_n_k` | `SkewMatrixGraph` | Unified namespace; no compatibility namespace aliases. |
| Y/Z | Same source files | `RowVector N α` | `Fin N → α` | Redundant type alias removed. |
| Y/Z | Same source files | custom `Matrix m n α` | Mathlib `Matrix (Fin m) (Fin n) α` | Shadowing aliases removed. |
| Y/Z | Same source files | `finToList` | None | Display-only helpers omitted. |
| Y/Z | Same source files | custom matrix `Repr` | None | Pretty-printers omitted. |
| Y/Z | Same source files | `#eval` | None | Debug evaluations omitted. |
| C/Y/Z | CFamily.lean, Family_Y.lean, Family_Z.lean | Separate imports/modules | `import LeanProject.Families` | One production family module; no copied duplicate imports. |
| Graph | Both branches / SkewMatrixGraph.lean | `IsSkewSymmetric` | `IsSkewSymmetric` | Source definition unchanged. |
| Graph | Both branches / SkewMatrixGraph.lean | `IsSmoothableEdge` | `IsSmoothableEdge` | Source definition unchanged. |
| Graph | Both branches / SkewMatrixGraph.lean | `lemma1` | `lemma1` | Statement/proof unchanged. |
| Root | Pre-integration HEAD / LeanProject.lean | `ratio_neg_of_triangle_cond` | Same original theorem | Previous unrelated repair reverted; only Families import added. |

No old-name compatibility aliases are retained. Source consumers should replace
their old family imports and apply this mapping.

## 13. Final public API

All definitions are in `SkewMatrixGraph`.

| Definition | Type / signature |
| --- | --- |
| `cyclicRightShift` | `{n : ℕ} → {α : Type*} → ℕ → (Fin n → α) → Fin n → α` |
| `ValidC` | `ℕ → ℕ → Prop` |
| `cFirstRow` | `(n k : ℕ) → Fin n → ℂ` |
| `cMatrix` | `(n k : ℕ) → Matrix (Fin n) (Fin n) ℂ` |
| `cMatrixI` | `(n k : ℕ) → (hd : 0 < Nat.gcd n k) → (Fin (Nat.gcd n k) → Bool) → Matrix (Fin n) (Fin n) ℂ` |
| `x4Matrix` | `Matrix (Fin 4) (Fin 4) ℂ` |
| `x5Matrix` | `Matrix (Fin 5) (Fin 5) ℂ` |
| `yRow0` | `(k : ℕ) → Fin (2 * (2 * k + 1)) → ℂ` |
| `yRow1` | `(k : ℕ) → Fin (2 * (2 * k + 1)) → ℂ` |
| `yRow` | `(k : ℕ) → ℕ → Fin (2 * (2 * k + 1)) → ℂ` |
| `yMatrix` | `(k : ℕ) → Matrix (Fin (2 * (2 * k + 1))) (Fin (2 * (2 * k + 1))) ℂ` |
| `zRow0` | `(k : ℕ) → Fin (5 * (2 * k + 1)) → ℂ` |
| `zRow1` | Same row type as zRow0 |
| `zRow2` | Same row type as zRow0 |
| `zRow3` | Same row type as zRow0 |
| `zRow4` | Same row type as zRow0 |
| `zRow` | `(k : ℕ) → ℕ → Fin (5 * (2 * k + 1)) → ℂ` |
| `zMatrix` | `(k : ℕ) → Matrix (Fin (5 * (2 * k + 1))) (Fin (5 * (2 * k + 1))) ℂ` |

Public structural theorems are the three shift facts in §3,
`yRow_zero`, `yRow_one`, `yRow_add_two`,
`zRow_zero`, `zRow_one`, `zRow_two`, `zRow_three`,
`zRow_four`, and `zRow_add_five`. The base-row equalities and recurrences
are exact definitional equalities.

The graph module continues to expose `IsSkewSymmetric`,
`IsSmoothableEdge`, and `lemma1`. Test-only source models and theorems
are not part of the production import interface.

## 14. Files created/modified

This extension updates the existing integration artifacts:

| File | Change relative to the preceding C/Y integration |
| --- | --- |
| `LeanProject/Families.lean` | Add X₄/X₅ and Z; update scope documentation; retain C/Y and shared helper. |
| `Tests/FamiliesIntegration.lean` | Retain C/Y checks; add complete X entry references and proofs, Z all-parameter references and proofs, all-new-matrix interface checks, X invariants, and boundary facts. |
| `docs/FAMILIES_INTEGRATION.md` | Replace the C/Y-only document with this complete classification-family document and mapping. |
| `LeanProject.lean` | Revert unrelated theorem repair; retain only a new Families import relative to HEAD. |

`LeanProject/SkewMatrixGraph.lean` remains exactly the restored source content;
it is not edited during this extension. No new competing production module,
verification module, documentation file, or temporary debug source is added.

Relative to the original Git HEAD, Families, the graph module, the verification
file, and this document are still new untracked files; the root has a one-line
import change. They remain in the working tree for review.

Unchanged: Basic.lean, Practice sources, Lake configuration, dependency
lockfile, toolchain declaration, all source-branch files/refs.
Lemma2.lean remains on the source branches and is not copied into the working
branch as an unrelated change.

## 15. Verification

Verification environment: 2026-09-27, Lean 4.35.0-rc1,
Mathlib tag v4.35.0-rc1 at
`c32e1ec0d1eb5237ba344eee50162f45d5b0fc76`.
The existing installed toolchain bin directory is placed first on PATH to avoid
the sandbox's elan network lookup. No toolchain/dependency versions changed.

Required commands:

```powershell
$env:PATH = 'C:\Users\gaosh\.elan\toolchains\leanprover--lean4---v4.35.0-rc1\bin;' + $env:PATH
lake env lean LeanProject/Families.lean
lake env lean Tests/FamiliesIntegration.lean
lake build
```

| Command | Final result |
| --- | --- |
| `lake env lean LeanProject/Families.lean` | Exit 0; no Lean errors |
| `lake env lean Tests/FamiliesIntegration.lean` | Exit 0; all five components and boundary/interface checks pass |
| `lake build` | Exit 0; build completed successfully, 8931 jobs |

The three required commands were run on the final Lean sources. The production
module was built before the final test command so that the imported artifact
matches the current implementation.

Warnings are distinguished carefully:

- Mathlib style warnings concern missing copyright/module headers and blank
  lines in the preserved graph proof. They are non-fatal.
- The root's original theorem has its pre-existing proof-placeholder warning,
  restored because the unrelated proof change was explicitly requested to be
  reverted. This is not a completed theorem proof, nor merely a style warning.
  It is outside the integrated family/test work.
- Families, the integration tests, and the restored graph module introduce no
  `sorry`, `admit`, or `axiom`. A source scan checks these modules separately.
  The final root diff contains only an import, so it introduces no such token.

The source refs and unchanged Lemma 1 module are checked against the recorded
snapshots. `git diff --check` is also part of final review.
No claim of a globally placeholder-free repository is made.

## 16. Remaining mathematical work

**Definitions completed:** C, X₄, X₅, Y, and Z, with direct complex Mathlib
matrix interfaces and source correspondence. There is no missing X source or
unresolved matrix-entry discrepancy.

**Skew-symmetry:** X₄/X₅ are checked in the verification module. General
C/C-I/Y/Z proofs under their valid parameter assumptions remain to be developed
and, where useful, exposed as production theorems. Z at k=0 is explicitly
proved not skew-symmetric; a general theorem must not quantify over all k
without a validity assumption.

**Zero row sums:** X₄/X₅ are checked in the verification module. Parameterized
row-sum proofs for C/C-I/Y/Z remain. The verified k=0 Y/Z nonzero row sums
prevent claiming this property for the source's entire total extension.

**Smoothable edges:** Classify/prove the relevant edges for each family.
Direct acceptance by IsSmoothableEdge is only type compatibility.

**Full smoothable cycles:** Define the required graph/cycle notions and prove
the full-cycle results with correct index wraparound and parameter assumptions.

**Classification/completeness:** Formalize equivalence under scaling and
simultaneous row/column permutation, and prove that every admissible matrix
falls into the classification list.

**Lemma 2:** Its complete source proof was inspected and is compatible with the
unchanged graph layer. Integration remains separate from this family-definition
task. The pre-existing unrelated rational root theorem is also still unfinished.

Optional future work includes deriving equivalent parity/five-residue closed
forms, with proofs before replacing the retained recurrences, and deriving
positive-gcd witnesses from valid C parameters.

## 17. Conventions for future work

1. Use SkewMatrixGraph and Mathlib `Matrix (Fin N) (Fin N) ℂ`.
2. Use ordinary `Fin N → α` row functions; avoid type/namespace aliases.
3. Reuse cyclicRightShift; T always means RIGHT shift. Cite the one-step and
   composition lemmas rather than introducing another implementation.
4. Prefer family-prefixed names such as x4Matrix, yRow, and zMatrix.
5. Encode fixed displayed matrices directly and retain their source index
   order/normalization. Record the paper/version and exact location.
6. Preserve seed case priorities, strict inequalities, cutoffs, signs, exceptional
   entries, recurrences, and all source parameters.
7. Separate total definitions from assumptions needed for classification
   properties. Boundary extensions are not automatically valid family members.
8. Keep reference implementations private in a verification module. Prove
   all-parameter or all-entry correspondence whenever practical.
9. Keep evaluations, pretty-printers, display conversions, and temporary debug
   examples out of production.
10. Keep definition integration separate from family-property proofs and from
    unrelated theorem repairs. Preserve Lemma 1 when evolving the family layer.
11. Update this same unified module/test/documentation set; do not add a
    competing integration interface.
12. Verify the production file, correspondence file, and full Lake build. Record
    warnings accurately and distinguish inherited proof debt from new work.
