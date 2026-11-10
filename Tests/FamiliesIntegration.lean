import LeanProject.Families

/-!
Kernel-checked correspondence for C, X₄, X₅, Y, Z.
The private reference definitions below retain the source expressions,
including integer Y/Z coefficients, Boolean comparisons, and recursive useT.
X matrices are transcribed from the primary paper.
This file is verification code, not imported by the production library.
-/

namespace FamiliesIntegrationTest

open SkewMatrixGraph

private def sourceCRow (n k : ℕ) : Fin n → ℂ :=
  fun j =>
    if j.val = 0 then 0
    else if j.val ≤ k then 1
    else if n - k ≤ j.val then -1
    else 0

private def sourceCShift {n : ℕ} (m : ℕ) (r : Fin n → ℂ) : Fin n → ℂ :=
  fun j => r (((fun x => (finRotate n).symm x)^[m]) j)

private def sourceCMatrix (n k : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => sourceCShift i.val (sourceCRow n k) j

private def sourceCMatrixI (n k : ℕ) (hd : 0 < Nat.gcd n k)
    (I : Fin (Nat.gcd n k) → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    let d := Nat.gcd n k
    let idx : Fin d := ⟨i.val % d, Nat.mod_lt _ hd⟩
    let ε : ℕ := if I idx then 1 else 0
    sourceCShift i.val (sourceCRow n (k - ε)) j

theorem cMatrix_matches_source (n k : ℕ) :
    cMatrix n k = sourceCMatrix n k := rfl

theorem cMatrixI_matches_source (n k : ℕ) (hd : 0 < Nat.gcd n k)
    (I : Fin (Nat.gcd n k) → Bool) :
    cMatrixI n k hd I = sourceCMatrixI n k hd I := by
  funext i j
  simp only [cMatrixI, sourceCMatrixI]
  cases I ⟨i.val % Nat.gcd n k, Nat.mod_lt _ hd⟩ <;> rfl

private def sourceYRow0 (k : ℕ) : Fin (2 * (2 * k + 1)) → ℤ :=
  fun i =>
    let n := 2 * (2 * k + 1)
    if i.val == 0 then 0
    else if i.val == 1 then 2
    else if i.val < n / 2 then 1
    else -1

private def sourceYRow1 (k : ℕ) : Fin (2 * (2 * k + 1)) → ℤ :=
  fun i =>
    let n := 2 * (2 * k + 1)
    if i.val == 0 then -2
    else if i.val == 1 then 0
    else if i.val < n / 2 + 2 then 1
    else -1

private def sourceYT (k : ℕ) {α : Type*}
    (v : Fin (2 * (2 * k + 1)) → α) : Fin (2 * (2 * k + 1)) → α :=
  fun i => v (i - 1)

private def sourceYUseT (k : ℕ) {α : Type*} :
    ℕ → (Fin (2 * (2 * k + 1)) → α) → Fin (2 * (2 * k + 1)) → α
  | 0, v => v
  | m + 1, v => sourceYT k (sourceYUseT k m v)

private def sourceYRow (k : ℕ) : ℕ → Fin (2 * (2 * k + 1)) → ℤ
  | 0 => sourceYRow0 k
  | 1 => sourceYRow1 k
  | i + 2 => sourceYUseT k 2 (sourceYRow k i)

private def sourceYMatrix (k : ℕ) :
    Matrix (Fin (2 * (2 * k + 1))) (Fin (2 * (2 * k + 1))) ℤ :=
  fun i => sourceYRow k i.val

theorem y_shift_matches_source (k m : ℕ) {α : Type*}
    (r : Fin (2 * (2 * k + 1)) → α) :
    cyclicRightShift m r = sourceYUseT k m r := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext j
    rw [sourceYUseT, sourceYT, ← ih]
    simp only [cyclicRightShift, Function.iterate_succ_apply, finRotate_symm_apply]

theorem yRow0_matches_source (k : ℕ) :
    yRow0 k = fun j => (sourceYRow0 k j : ℂ) := by
  funext j
  simp [yRow0, sourceYRow0]

theorem yRow1_matches_source (k : ℕ) :
    yRow1 k = fun j => (sourceYRow1 k j : ℂ) := by
  funext j
  simp [yRow1, sourceYRow1]

/-- Integer embedding commutes with the shared shift at every dimension/count. -/
theorem cast_commutes_with_shift {n : ℕ} (m : ℕ) (r : Fin n → ℤ) :
    cyclicRightShift m (fun j => (r j : ℂ)) =
      fun j => ((cyclicRightShift m r j : ℤ) : ℂ) := rfl

theorem yRow_matches_source (k i : ℕ) :
    yRow k i = fun j => (sourceYRow k i j : ℂ) := by
  induction i using Nat.twoStepInduction with
  | zero => exact yRow0_matches_source k
  | one => exact yRow1_matches_source k
  | more i hi _ =>
    rw [yRow_add_two, hi, cast_commutes_with_shift, y_shift_matches_source]
    rfl

/-- Every entry agrees for every k, including k = 0; this is not a sample test. -/
theorem yMatrix_matches_source (k : ℕ) :
    yMatrix k = fun i j => (sourceYMatrix k i j : ℂ) := by
  funext i j
  exact congrFun (yRow_matches_source k i.val) j

-- Right-shift wraparound: [0, 1, 2, 3] becomes [3, 0, 1, 2].
example : cyclicRightShift 1 (fun j : Fin 4 => j.val) 0 = 3 := by decide
example : cyclicRightShift 1 (fun j : Fin 4 => j.val) 1 = 0 := by decide

-- Boundary values and source cutoffs.
example : yMatrix 0 0 1 = 2 := by norm_num [yMatrix, yRow, yRow0]
example : yMatrix 0 1 0 = -2 := by norm_num [yMatrix, yRow, yRow1]
example : yRow0 1 3 = -1 := by norm_num [yRow0]
example : yRow1 1 4 = 1 := by norm_num [yRow1]
example : yRow1 1 5 = -1 := by norm_num [yRow1]

-- Public matrices can be passed directly to both graph predicates.
example (n k : ℕ) : Prop := IsSkewSymmetric (cMatrix n k)
example (k : ℕ) : Prop := IsSkewSymmetric (yMatrix k)
example (n k : ℕ) (hd : 0 < Nat.gcd n k)
    (I : Fin (Nat.gcd n k) → Bool) (i j : Fin n) : Prop :=
  IsSmoothableEdge (cMatrixI n k hd I) i j
example (k : ℕ) (i j : Fin (2 * (2 * k + 1))) : Prop :=
  IsSmoothableEdge (yMatrix k) i j

-- Preserve the exact Lemma 1 interface and make it available through Families.
example {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : IsSkewSymmetric B) (i j₁ j₂ : Fin n) (hj : j₁ ≠ j₂)
    (h₁ : IsSmoothableEdge B i j₁) (h₂ : IsSmoothableEdge B i j₂) :
    ∃ q : ℚ, q < 0 ∧ B i j₁ = (q : ℂ) * B i j₂ :=
  lemma1 B hB i j₁ j₂ hj h₁ h₂


-- Integer transcriptions of the paper's fixed matrices, using an independent
-- entry-case representation. Indices and normalization are unchanged.
-- X₄: arXiv:2310.05284v1, Example 2.1.
private def sourceX4Matrix : Matrix (Fin 4) (Fin 4) ℤ :=
  fun i j => match i.val, j.val with
    | 0, 1 => 2
    | 0, 2 => -1
    | 0, 3 => -1
    | 1, 0 => -2
    | 1, 2 => 3
    | 1, 3 => -1
    | 2, 0 => 1
    | 2, 1 => -3
    | 2, 3 => 2
    | 3, 0 => 1
    | 3, 1 => 1
    | 3, 2 => -2
    | _, _ => 0

-- X₅: Matviichuk, published §3.1 (also arXiv:2310.05284v1, §3.1).
private def sourceX5Matrix : Matrix (Fin 5) (Fin 5) ℤ :=
  fun i j => match i.val, j.val with
    | 0, 1 => 1
    | 0, 2 => 1
    | 0, 3 => -1
    | 0, 4 => -1
    | 1, 0 => -1
    | 1, 2 => 2
    | 1, 4 => -1
    | 2, 0 => -1
    | 2, 1 => -2
    | 2, 3 => 2
    | 2, 4 => 1
    | 3, 0 => 1
    | 3, 2 => -2
    | 3, 4 => 1
    | 4, 0 => 1
    | 4, 1 => 1
    | 4, 2 => -1
    | 4, 3 => -1
    | _, _ => 0

/-- All 16 X₄ entries, not just its upper triangle or a few selected entries. -/
theorem x4Matrix_matches_source :
    x4Matrix = fun i j => (sourceX4Matrix i j : ℂ) := by
  funext i j
  fin_cases i <;> fin_cases j <;> norm_num [x4Matrix, sourceX4Matrix]

/-- All 25 X₅ entries, including its off-diagonal zero entries. -/
theorem x5Matrix_matches_source :
    x5Matrix = fun i j => (sourceX5Matrix i j : ℂ) := by
  funext i j
  fin_cases i <;> fin_cases j <;> norm_num [x5Matrix, sourceX5Matrix]

theorem x4_skewSymmetric : IsSkewSymmetric x4Matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [x4Matrix, Matrix.transpose_apply]

theorem x5_skewSymmetric : IsSkewSymmetric x5Matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [x5Matrix, Matrix.transpose_apply]

theorem x4_rowSum_zero (i : Fin 4) : ∑ j, x4Matrix i j = 0 := by
  fin_cases i <;> norm_num [x4Matrix, Fin.sum_univ_succ]

theorem x5_rowSum_zero (i : Fin 5) : ∑ j, x5Matrix i j = 0 := by
  fin_cases i <;> norm_num [x5Matrix, Fin.sum_univ_succ]

-- Exact integer reference seeds from origin/ckhj-lemma2:LeanProject/Family_Z.lean.
private def sourceZRow0 (k : ℕ) : Fin (5 * (2 * k + 1)) → ℤ :=
  fun i =>
    let n := 5 * (2 * k + 1)
    if i.val == 0 then 0
    else if i.val < (n - 1) / 2 + 1 then 1
    else -1

private def sourceZRow1 (k : ℕ) : Fin (5 * (2 * k + 1)) → ℤ :=
  fun i =>
    let n := 5 * (2 * k + 1)
    if i.val == 0 then -1
    else if i.val == 1 then 0
    else if i.val == 2 then 2
    else if i.val == 3 then 2
    else if i.val < (n - 1) / 2 + 1 then 1
    else -1

private def sourceZRow2 (k : ℕ) : Fin (5 * (2 * k + 1)) → ℤ :=
  fun i =>
    let n := 5 * (2 * k + 1)
    if i.val == 0 then -1
    else if i.val == 1 then -2
    else if i.val == 2 then 0
    else if i.val == 3 then 2
    else if i.val < (n - 1) / 2 + 3 then 1
    else -1

private def sourceZRow3 (k : ℕ) : Fin (5 * (2 * k + 1)) → ℤ :=
  fun i =>
    let n := 5 * (2 * k + 1)
    if i.val == 0 then -1
    else if i.val == 1 then -2
    else if i.val == 2 then -2
    else if i.val == 3 then 0
    else if i.val < (n - 1) / 2 + 5 then 1
    else -1

private def sourceZRow4 (k : ℕ) : Fin (5 * (2 * k + 1)) → ℤ :=
  fun i =>
    let n := 5 * (2 * k + 1)
    if i.val == 0 then -1
    else if i.val == 1 then -1
    else if i.val == 2 then -1
    else if i.val == 3 then -1
    else if i.val == 4 then 0
    else if i.val < (n - 1) / 2 + 5 then 1
    else -1

private def sourceZT (k : ℕ) {α : Type*}
    (v : Fin (5 * (2 * k + 1)) → α) : Fin (5 * (2 * k + 1)) → α :=
  fun i => v (i - 1)

private def sourceZUseT (k : ℕ) {α : Type*} :
    ℕ → (Fin (5 * (2 * k + 1)) → α) → Fin (5 * (2 * k + 1)) → α
  | 0, v => v
  | m + 1, v => sourceZT k (sourceZUseT k m v)

private def sourceZRow (k : ℕ) : ℕ → Fin (5 * (2 * k + 1)) → ℤ
  | 0 => sourceZRow0 k
  | 1 => sourceZRow1 k
  | 2 => sourceZRow2 k
  | 3 => sourceZRow3 k
  | 4 => sourceZRow4 k
  | i + 5 => sourceZUseT k 5 (sourceZRow k i)

private def sourceZMatrix (k : ℕ) :
    Matrix (Fin (5 * (2 * k + 1))) (Fin (5 * (2 * k + 1))) ℤ :=
  fun i => sourceZRow k i.val

theorem z_shift_matches_source (k m : ℕ) {α : Type*}
    (r : Fin (5 * (2 * k + 1)) → α) :
    cyclicRightShift m r = sourceZUseT k m r := by
  induction m with
  | zero => rfl
  | succ m ih =>
    funext j
    rw [sourceZUseT, sourceZT, ← ih]
    simp only [cyclicRightShift, Function.iterate_succ_apply, finRotate_symm_apply]

theorem zRow0_matches_source (k : ℕ) :
    zRow0 k = fun j => (sourceZRow0 k j : ℂ) := by
  funext j
  simp [zRow0, sourceZRow0]

theorem zRow1_matches_source (k : ℕ) :
    zRow1 k = fun j => (sourceZRow1 k j : ℂ) := by
  funext j
  simp [zRow1, sourceZRow1]

theorem zRow2_matches_source (k : ℕ) :
    zRow2 k = fun j => (sourceZRow2 k j : ℂ) := by
  funext j
  simp [zRow2, sourceZRow2]

theorem zRow3_matches_source (k : ℕ) :
    zRow3 k = fun j => (sourceZRow3 k j : ℂ) := by
  funext j
  simp [zRow3, sourceZRow3]

theorem zRow4_matches_source (k : ℕ) :
    zRow4 k = fun j => (sourceZRow4 k j : ℂ) := by
  funext j
  simp [zRow4, sourceZRow4]

/-- All Z rows, with the exact five-step recurrence and all natural parameters. -/
theorem zRow_matches_source (k : ℕ) :
    ∀ i, zRow k i = fun j => (sourceZRow k i j : ℂ)
  | 0 => zRow0_matches_source k
  | 1 => zRow1_matches_source k
  | 2 => zRow2_matches_source k
  | 3 => zRow3_matches_source k
  | 4 => zRow4_matches_source k
  | i + 5 => by
    rw [zRow_add_five, zRow_matches_source k i, cast_commutes_with_shift,
      z_shift_matches_source]
    rfl

theorem zMatrix_matches_source (k : ℕ) :
    zMatrix k = fun i j => (sourceZMatrix k i j : ℂ) := by
  funext i j
  exact congrFun (zRow_matches_source k i.val) j

-- Source boundaries: row-specific fixed entries precede the cutoff.
example : zRow0 1 7 = 1 := by norm_num [zRow0]
example : zRow0 1 8 = -1 := by norm_num [zRow0]
example : zRow1 1 2 = 2 := by norm_num [zRow1]
example : zRow2 1 9 = 1 := by norm_num [zRow2]
example : zRow2 1 10 = -1 := by norm_num [zRow2]
example : zRow3 1 11 = 1 := by norm_num [zRow3]
example : zRow3 1 12 = -1 := by norm_num [zRow3]
example : zRow4 0 3 = -1 := by norm_num [zRow4]

/-- The source's total extension to k = 0 is outside the paper's valid range. -/
theorem zMatrix_zero_not_skewSymmetric : ¬ IsSkewSymmetric (zMatrix 0) := by
  intro h
  change (zMatrix 0).transpose = -(zMatrix 0) at h
  have hentry := congrFun (congrFun h 0) 4
  norm_num [Matrix.transpose_apply, zMatrix, zRow, zRow0, zRow4] at hentry

theorem yMatrix_zero_row0_sum : ∑ j, yMatrix 0 0 j = 2 := by
  norm_num [yMatrix, yRow, yRow0, Fin.sum_univ_succ]

theorem zMatrix_zero_row1_sum : ∑ j, zMatrix 0 1 j = 2 := by
  norm_num [zMatrix, zRow, zRow1, Fin.sum_univ_succ]

-- Direct graph interfaces for every newly added component, without casts.
example : Prop := IsSkewSymmetric x4Matrix
example : Prop := IsSkewSymmetric x5Matrix
example (k : ℕ) : Prop := IsSkewSymmetric (zMatrix k)
example (i j : Fin 4) : Prop := IsSmoothableEdge x4Matrix i j
example (i j : Fin 5) : Prop := IsSmoothableEdge x5Matrix i j
example (k : ℕ) (i j : Fin (5 * (2 * k + 1))) : Prop :=
  IsSmoothableEdge (zMatrix k) i j

end FamiliesIntegrationTest
