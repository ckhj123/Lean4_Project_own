# Proof review and provenance

The `main` branch contains skew symmetry and zero row sum for all five
families. The `ai` branch includes those results and adds cyclic adjacent
smoothability for each family. Lean has checked the stated theorems.
Mathematical review is pending.


The production matrices are defined in `LeanProject/Families.lean` over `ℂ`.
The graph predicates are in `LeanProject/SkewMatrixGraph.lean`. The milestone
does not change these definitions or weaken the predicates.

## The 15 properties

| Family | Property and public theorem | Valid parameters | Proof provenance | Lean | Mathematics |
| --- | --- | --- | --- | --- | --- |
| C | Zero row sum: `SkewMatrixGraph.cMatrix_row_sum_zero` | `ValidC n k` | AI, `CFamilyProperties.lean`; Jason also proved the related `cMatrix_C_all_row_sums_zero` in `AddSumLemma.lean` | Verified | Review pending |
| C | Skew symmetry: `SkewMatrixGraph.cMatrix_skewSymmetric` | `ValidC n k` | AI, `CFamilyProperties.lean` | Verified | Review pending |
| C | Cyclic adjacent smoothability: `SkewMatrixGraph.cMatrix_adjacent_smoothable` | `ValidC n k` | AI, `SmoothabilityProperties.lean`; Jason's `Smooth_cycle.lean` supplies a cyclic-equivalence framework, with later AI completions | Verified | Review pending |
| X4 | Zero row sum: `x4Matrix_all_row_sums_zero` | Fixed matrix | AI addition to Jason's `AddSumLemma.lean` in `0cd49a8` | Verified | Review pending |
| X4 | Skew symmetry: `SkewMatrixGraph.x4Matrix_skewSymmetric` | Fixed matrix | AI, `SkewSymmetryProperties.lean` | Verified | Review pending |
| X4 | Cyclic adjacent smoothability: `SkewMatrixGraph.x4Matrix_adjacent_smoothable` | Fixed matrix | AI, `SmoothabilityProperties.lean` | Verified | Review pending |
| X5 | Zero row sum: `x5Matrix_all_row_sums_zero` | Fixed matrix | AI addition to Jason's `AddSumLemma.lean` in `0cd49a8` | Verified | Review pending |
| X5 | Skew symmetry: `SkewMatrixGraph.x5Matrix_skewSymmetric` | Fixed matrix | AI, `SkewSymmetryProperties.lean` | Verified | Review pending |
| X5 | Cyclic adjacent smoothability: `SkewMatrixGraph.x5Matrix_adjacent_smoothable` | Fixed matrix | AI, `SmoothabilityProperties.lean` | Verified | Review pending |
| Y | Zero row sum: `yMatrix_all_row_sums_zero` | `0 < k` | Jason, `AddSumLemma.lean` | Verified | Review pending |
| Y | Skew symmetry: `SkewMatrixGraph.yMatrix_skewSymmetric` | Any `k : ℕ` | AI, `SkewSymmetryProperties.lean` | Verified | Review pending |
| Y | Cyclic adjacent smoothability: `SkewMatrixGraph.yMatrix_adjacent_smoothable` | `0 < k` | AI, `SmoothabilityProperties.lean` | Verified | Review pending |
| Z | Zero row sum: `zMatrix_all_row_sums_zero` | `0 < k` | Jason, `AddSumLemma.lean`, completed in `24c9659` | Verified | Review pending |
| Z | Skew symmetry: `SkewMatrixGraph.zMatrix_skewSymmetric` | `1 ≤ k` | AI, `SkewSymmetryProperties.lean` | Verified | Review pending |
| Z | Cyclic adjacent smoothability: `SkewMatrixGraph.zMatrix_adjacent_smoothable` | `0 < k` | AI, `SmoothabilityProperties.lean` | Verified | Review pending |

For smoothability, “cyclic adjacent” means the edge from `i` to
`finRotate n i`. X4 and X5 are checked by finite cases. The Y and Z proofs
reduce arbitrary indices to seed edges through periodic row shifts. The Z
proof compares seed cutoffs and handles the final wraparound edge separately.

## File provenance

- **Jason original:** `AddSumLemma.lean` up to `24c9659` contains his C, Y,
  and Z row-sum work. `Smooth_cycle.lean` at `c13d15d` contains his cyclic
  equivalence and smoothability framework. Its three original `sorry`
  placeholders are part of that historical source state.
- **Mixed Jason and AI:** `AddSumLemma.lean` adds only the X4 and X5
  row-sum theorems after `24c9659`. `Smooth_cycle.lean` has AI completions
  of Jason's three placeholders, an import of `CFamilyProperties`, and a
  corrected statement using `finRotate` for cyclic adjacency.
- **AI proof files:** `CFamilyProperties.lean` and
  `SkewSymmetryProperties.lean` were added in `ca2625d` and introduced to
  `ModifiedWork` unchanged through PR #1 (`c4e8138`, merged at `c7a3a5b`).
  `SmoothabilityProperties.lean` was added in `0cd49a8`. They use the
  existing production definitions; they do not replace Jason's files.
- **Existing shared source:** `Families.lean` and `SkewMatrixGraph.lean`
  remain available on both branches. This audit does not attribute every
  line of those earlier shared definitions to a single author.

The merge diffs for `12732d3`, `2598995`, and `c7a3a5b` were checked
against both parents. No additional collaborator file lost in those merges
was identified. `CFamilyProperties.lean` and `SkewSymmetryProperties.lean`
have exact blob matches between `ca2625d` and PR #1; neither existed in
Jason's pre-PR tree.

## Verification evidence and limits

The following checks succeeded for the milestone at `0cd49a8`:

```text
lake env lean LeanProject/CFamilyProperties.lean
lake env lean LeanProject/SmoothabilityProperties.lean
lake build LeanProject.CFamilyProperties LeanProject.Smooth_cycle LeanProject.SkewSymmetryProperties LeanProject.AddSumLemma LeanProject.SmoothabilityProperties
lake build
```

A search of the targeted proof files found no `sorry`, `admit`, or new
`axiom`. An axiom audit of all 15 public theorems reported only `propext`,
`Classical.choice`, and `Quot.sound`, with no `sorryAx` or project-specific
axiom. The unrelated root `LeanProject.lean` has a pre-existing `sorry` and
may emit a warning during the default build.

The Z production extension at `k = 0` is not skew-symmetric; this is
formalized by `zMatrix_zero_not_skewSymmetric`. The stated Z properties
therefore use `k ≥ 1`. The Y row-sum and smoothability theorems also use
the nondegenerate source range `k > 0`. These boundary hypotheses should
be checked against the source paper during mathematical review.

**Next review:** compare the production entries and parameter ranges with
the paper, then review the seed-row calculations, cyclic reindexing, and
`IsSmoothableEdge` witnesses line by line. Lean acceptance establishes that
the proofs follow from the encoded definitions; it is not a substitute for
reviewing whether those definitions encode the intended mathematics.
