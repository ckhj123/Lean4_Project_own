import Mathlib
import LeanProject.Families
open SkewMatrixGraph
open BigOperators

def rowSumZ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℤ :=
  ∑ j : Fin n, A i j

def AllRowSum_Z {n : ℕ} (B : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ i : Fin n, rowSumZ B i = 0

lemma Sum_cyclic_0 {α : Type*} [AddCommMonoid α] {n : ℕ} (k : ℕ)
     (v : Fin n → α) (hv : ∑ j : Fin n, v j = 0) :
    ∑ j : Fin n, cyclicRightShift k v j = 0 := by
  dsimp [cyclicRightShift]
  change (∑ j : Fin n, v (((finRotate n).symm ^ k) j)) = 0
  calc
    _ = ∑ j : Fin n, v j := Equiv.sum_comp ((finRotate n).symm ^ k) v
    _ = 0 := hv

lemma cFirstRow_Z_add_neg (n k : ℕ) (hk : 2 * k < n) (j : Fin n) :
    cFirstRow_Z n k j + cFirstRow_Z n k (-j) = 0 := by
  have : NeZero n := ⟨by omega⟩
  have hj := j.isLt
  dsimp [cFirstRow_Z]
  have hneg := Fin.val_neg j
  by_cases h0 : j = 0
  · rw [h0]
    simp
  · rw [hneg, ite_eq_right h0]
    have hj0 : j.val ≠ 0 := fun h => h0 (Fin.ext h)
    split_ifs <;> omega

theorem cFirstRow_Z_sum_zero (n k : ℕ) (hk : 2 * k < n) :
    ∑ j : Fin n, cFirstRow_Z n k j = 0 := by
  have : NeZero n := ⟨by omega⟩
  have h_sum_neg : ∑ j : Fin n, cFirstRow_Z n k (-j) = ∑ j : Fin n, cFirstRow_Z n k j :=
    Equiv.sum_comp (Equiv.neg (Fin n)) (cFirstRow_Z n k)
  have h_double : 2 * (∑ j : Fin n, cFirstRow_Z n k j) = 0 := calc
    2 * (∑ j : Fin n, cFirstRow_Z n k j)
      = (∑ j : Fin n, cFirstRow_Z n k j) + (∑ j : Fin n, cFirstRow_Z n k j) := by ring
    _ = (∑ j : Fin n, cFirstRow_Z n k j) + (∑ j : Fin n, cFirstRow_Z n k (-j)) := by rw [h_sum_neg]
    _ = ∑ j : Fin n, (cFirstRow_Z n k j + cFirstRow_Z n k (-j)) := by rw [← Finset.sum_add_distrib]
    _ = ∑ j : Fin n, 0 := Finset.sum_congr rfl (fun j _ => cFirstRow_Z_add_neg n k hk j)
    _ = 0 := by simp
  omega

theorem cMatrix_Z_all_row_sums_zero (n k : ℕ) (hk : 2 * k < n) :
    AllRowSum_Z (cMatrix_Z n k) := by
  intro i
  dsimp [AllRowSum_Z, rowSumZ, cMatrix_Z]
  exact Sum_cyclic_0 i.val _ (cFirstRow_Z_sum_zero n k hk)

/- A General version for any ℂ valued matrix -/

def rowSumC {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : ℂ :=
  ∑ j : Fin n, A i j

def AllRowSum_C {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ i : Fin n, rowSumC B i = 0

-- Bridge lemma connecting ℂ definition to ℤ cast
lemma cFirstRow_eq_cast (n k : ℕ) (j : Fin n) :
    cFirstRow n k j = (cFirstRow_Z n k j : ℂ) := by
  dsimp [cFirstRow, cFirstRow_Z]
  split_ifs <;> simp

theorem cFirstRow_C_sum_zero (n k : ℕ) (hk : 2 * k < n) :
    ∑ j : Fin n, cFirstRow n k j = 0 := by
  simp_rw [cFirstRow_eq_cast]
  rw [← Int.cast_sum, cFirstRow_Z_sum_zero n k hk, Int.cast_zero]

theorem cMatrix_C_all_row_sums_zero (n k : ℕ) (hk : 2 * k < n) :
    AllRowSum_C (cMatrix n k) := by
  intro i
  dsimp [AllRowSum_C, rowSumC, cMatrix]
  exact Sum_cyclic_0 i.val _ (cFirstRow_C_sum_zero n k hk)

theorem cMatrixI_all_row_sums_zero (n k : ℕ) (hk : 2 * k < n)
    (hd : 0 < Nat.gcd n k) (I : Fin (Nat.gcd n k) → Bool) :
    AllRowSum_C (cMatrixI n k hd I) := by
  intro i
  dsimp [AllRowSum_C, rowSumC, cMatrixI]
  have hk' : 2 * (k - (I ⟨i.val % Nat.gcd n k, Nat.mod_lt _ hd⟩).toNat) < n := by omega
  exact Sum_cyclic_0 i.val _ (cFirstRow_C_sum_zero n _ hk')

  -- Helper lemmas for seed rows



theorem yRow0_sum_zero (k : ℕ) : ∑ j, yRow0 k j = 0 := by sorry
theorem yRow1_sum_zero (k : ℕ) : ∑ j, yRow1 k j = 0 := by sorry

-- Main theorem for Family Y using Sum_cyclic_0
theorem yRow_sum_zero (k : ℕ) : (i : ℕ) → ∑ j, yRow k i j = 0
  | 0 => yRow0_sum_zero k
  | 1 => yRow1_sum_zero k
  | i + 2 => by
    dsimp [yRow]
    exact Sum_cyclic_0 2 _ (yRow_sum_zero k i)

theorem yMatrix_all_row_sums_zero (k : ℕ) : AllRowSum_C (yMatrix k) := by
  intro i
  dsimp [AllRowSum_C, rowSumC, yMatrix]
  exact yRow_sum_zero k i.val




-- Helper lemmas for the 5 seed rows

lemma zRow0_add_neg (k : ℕ) (j : Fin (5 * (2 * k + 1))) :
  zRow0 k j + zRow0 k (-j) = 0 := by
  have : NeZero (5 * (2 * k + 1)) := ⟨by omega⟩
  dsimp [zRow0]
  have hneg := Fin.val_neg j
  by_cases h0 : j = 0
  · rw [h0]
    simp
  · rw [hneg, ite_eq_right h0]
    have hj0 : j.val ≠ 0 := fun h => h0 (Fin.ext h)
    split_ifs <;> first | omega | ring

theorem zRow0_sum_zero (k : ℕ) : ∑ j, zRow0 k j = 0 := by
  have : NeZero (5 * (2 * k + 1)) := ⟨by omega⟩
  have h_sum_neg : ∑ j, zRow0 k (-j) = ∑ j, zRow0 k j :=
    Equiv.sum_comp (Equiv.neg _) (zRow0 k)
  have h_double : 2 * (∑ j, zRow0 k j) = 0 := calc
    2 * (∑ j, zRow0 k j)
      = (∑ j, zRow0 k j) + (∑ j, zRow0 k j) := by ring
    _ = (∑ j, zRow0 k j) + (∑ j, zRow0 k (-j)) := by rw [h_sum_neg]
    _ = ∑ j, (zRow0 k j + zRow0 k (-j)) := by rw [← Finset.sum_add_distrib]
    _ = ∑ j, 0 := Finset.sum_congr rfl (fun j _ => zRow0_add_neg k j)
    _ = 0 := by simp
  -- omega / ring logic over ℂ:
  -- Since 2 * S = 0 in ℂ, S = 0
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  exact mul_eq_zero.mp h_double |>.resolve_left h2


theorem zRow1_sum_zero (k : ℕ) : ∑ j, zRow1 k j = 0 := by sorry
theorem zRow2_sum_zero (k : ℕ) : ∑ j, zRow2 k j = 0 := by sorry
theorem zRow3_sum_zero (k : ℕ) : ∑ j, zRow3 k j = 0 := by sorry
theorem zRow4_sum_zero (k : ℕ) : ∑ j, zRow4 k j = 0 := by sorry

-- Main theorem for Family Z using Sum_cyclic_0
theorem zRow_sum_zero (k : ℕ) : (i : ℕ) → ∑ j, zRow k i j = 0
  | 0 => zRow0_sum_zero k
  | 1 => zRow1_sum_zero k
  | 2 => zRow2_sum_zero k
  | 3 => zRow3_sum_zero k
  | 4 => zRow4_sum_zero k
  | i + 5 => by
    dsimp [zRow]
    exact Sum_cyclic_0 5 _ (zRow_sum_zero k i)

theorem zMatrix_all_row_sums_zero (k : ℕ) : AllRowSum_C (zMatrix k) := by
  intro i
  dsimp [AllRowSum_C, rowSumC, zMatrix]
  exact zRow_sum_zero k i.val
