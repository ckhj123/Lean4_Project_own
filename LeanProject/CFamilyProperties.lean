import LeanProject.Families

/-!
# Properties of the ordinary C-family

For valid parameters, every row sums to zero and the matrix is skew-symmetric.
Both statements use the production `cFirstRow`, `cMatrix`, and graph predicates.
-/

set_option linter.style.haveILetI false

namespace SkewMatrixGraph

/-- A right shift reads the seed row at the cyclic difference of the indices. -/
theorem cyclicRightShift_apply_sub {n : ℕ} [NeZero n] {α : Type*}
    (r : Fin n → α) (m : ℕ) (j : Fin n) :
    cyclicRightShift m r j = r (j - Fin.ofNat n m) := by
  induction m generalizing j with
  | zero => simp
  | succ m ih =>
      rw [cyclicRightShift_add, cyclicRightShift_one_apply, ih]
      have hcast : Fin.ofNat n (m + 1) = Fin.ofNat n m + 1 := by
        ext
        simp [Fin.ofNat, Fin.add_def, Nat.add_mod]
      rw [hcast]
      congr 1
      abel

/-- The seed row changes sign under cyclic negation. -/
theorem cFirstRow_neg {n k : ℕ} (h : ValidC n k) (a : Fin n) :
    cFirstRow n k (-a) = -cFirstRow n k a := by
  haveI : NeZero n := ⟨by have := h.2.1; omega⟩
  by_cases ha : a = 0
  · subst a
    simp [cFirstRow]
  have ha0 : a.val ≠ 0 := by
    intro hz
    exact ha (Fin.ext hz)
  have hav : 0 < a.val := by omega
  have hnv : (-a).val = n - a.val := by simpa [ha] using Fin.val_neg a
  have hnpos : 0 < n - a.val := by have := a.isLt; omega
  have hk : 2 * k < n := h.2.2
  by_cases hp : a.val ≤ k
  · have hnp : ¬ n - a.val ≤ k := by omega
    have hnn : n - k ≤ n - a.val := by omega
    simp [cFirstRow, hnv, hav.ne', hnpos.ne', hp, hnp, hnn]
  · by_cases hn : n - k ≤ a.val
    · have hnp : n - a.val ≤ k := by omega
      have hnn : n ≤ a.val + k := by omega
      simp [cFirstRow, hnv, hav.ne', hnpos.ne', hp, hnp, hnn]
    · have hnp : ¬ n - a.val ≤ k := by omega
      have hnn : ¬ n - k ≤ n - a.val := by omega
      simp [cFirstRow, hnv, hav.ne', hnpos.ne', hp, hn, hnp, hnn]

/-- Every C entry is the seed value at the cyclic column-minus-row difference. -/
theorem cMatrix_apply {n k : ℕ} (h : ValidC n k) (i j : Fin n) :
    cMatrix n k i j = cFirstRow n k (j - i) := by
  haveI : NeZero n := ⟨by have := h.2.1; omega⟩
  have hcast : Fin.ofNat n i.val = i := by
    ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt i.isLt]
  simpa [cMatrix, hcast] using cyclicRightShift_apply_sub (cFirstRow n k) i.val j

/-- Negation pairs every +1 in the seed row with a -1. -/
theorem cFirstRow_sum_zero {n k : ℕ} (h : ValidC n k) :
    ∑ j : Fin n, cFirstRow n k j = 0 := by
  haveI : NeZero n := ⟨by have := h.2.1; omega⟩
  have hperm :
      (∑ j : Fin n, cFirstRow n k j) =
        ∑ j : Fin n, cFirstRow n k (-j) := by
    apply Fintype.sum_equiv (Equiv.neg (Fin n))
    intro j
    simp
  have hneg :
      (∑ j : Fin n, cFirstRow n k (-j)) =
        -(∑ j : Fin n, cFirstRow n k j) := by
    simp_rw [cFirstRow_neg h]
    simp
  have hsum := hperm.trans hneg
  linear_combination (1 / 2 : ℂ) * hsum

/-- Reindexing a sum by the cyclic permutation preserves its value. -/
private theorem cyclicRightShift_sum {n m : ℕ} (r : Fin n → ℂ) :
    ∑ j : Fin n, cyclicRightShift m r j = ∑ j : Fin n, r j := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc
        ∑ j : Fin n, cyclicRightShift (m + 1) r j =
            ∑ j : Fin n, cyclicRightShift 1 (cyclicRightShift m r) j := by
              simp [cyclicRightShift_add]
        _ = ∑ j : Fin n, cyclicRightShift m r j := by
              apply Fintype.sum_equiv (finRotate n).symm
              intro j
              rfl
        _ = ∑ j : Fin n, r j := ih

/-- Every row is a permutation of the zero-sum seed row. -/
theorem cMatrix_row_sum_zero {n k : ℕ} (h : ValidC n k) (i : Fin n) :
    ∑ j : Fin n, cMatrix n k i j = 0 := by
  change ∑ j : Fin n, cyclicRightShift i.val (cFirstRow n k) j = 0
  rw [cyclicRightShift_sum, cFirstRow_sum_zero h]

/-- Reversing the cyclic difference reverses the sign of each entry. -/
theorem cMatrix_skewSymmetric {n k : ℕ} (h : ValidC n k) :
    IsSkewSymmetric (cMatrix n k) := by
  haveI : NeZero n := ⟨by have := h.2.1; omega⟩
  apply Matrix.ext
  intro i j
  change cMatrix n k j i = -cMatrix n k i j
  rw [cMatrix_apply h, cMatrix_apply h]
  have hd : i - j = -(j - i) := by simp
  rw [hd, cFirstRow_neg h]

end SkewMatrixGraph
