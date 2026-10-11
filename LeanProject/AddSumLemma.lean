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

-- For Y Family
def yRow0_nat (k j : ℕ) : ℂ :=
  let n := 2 * (2 * k + 1)
  if j = 0 then 0
  else if j = 1 then 2
  else if j < n / 2 then 1
  else -1

def deltaY_nat (k j : ℕ) : ℂ :=
  if j = 0 then -2
  else if j = 1 then -2
  else if j = 2 * k + 1 then 2
  else if j = 2 * k + 2 then 2
  else 0

def deltaY (k : ℕ) (j : Fin (2 * (2 * k + 1))) : ℂ :=
  deltaY_nat k j.val

-------------------------------------------------------------------------------
-- Proof for yRow0
-------------------------------------------------------------------------------

theorem yRow0_sum_zero (k : ℕ) (hk : 0 < k) : ∑ j, yRow0 k j = 0 := by
  let n := 2 * (2 * k + 1)
  have hn2 : 2 ≤ n / 2 := by dsimp [n]; omega
  have hn : n / 2 ≤ n := by dsimp [n]; omega

  -- 1. Bridge Fin sum to range sum
  have h_eq : ∑ j : Fin n, yRow0 k j = ∑ j ∈ Finset.range n, yRow0_nat k j := by
    change ∑ j : Fin n, yRow0_nat k j.val = ∑ j ∈ Finset.range n, yRow0_nat k j
    exact Fin.sum_univ_eq_sum_range (yRow0_nat k) n
  rw [h_eq]

  -- 2. Partition range n into [0, 2), [2, n/2), and [n/2, n)
  rw [← Finset.sum_range_add_sum_Ico (yRow0_nat k) hn]
  rw [← Finset.sum_range_add_sum_Ico (yRow0_nat k) hn2]

  -- Evaluate head interval [0, 2)
  have h_head : ∑ j ∈ Finset.range 2, yRow0_nat k j = 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    dsimp [yRow0_nat]
    ring

  -- Evaluate middle interval [2, n/2)
  have h_mid : ∑ j ∈ Finset.Ico 2 (n / 2), yRow0_nat k j = ((n / 2 - 2 : ℕ) : ℂ) := by
    have h_mid_eq : ∀ j ∈ Finset.Ico 2 (n / 2), yRow0_nat k j = 1 := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      rcases hj with ⟨hj1, hj2⟩
      dsimp [yRow0_nat]
      split_ifs with c1 c2
      · omega
      · omega
      · rfl
    rw [Finset.sum_congr rfl h_mid_eq, Finset.sum_const]
    simp

  -- Evaluate tail interval [n/2, n)
  have h_tail : ∑ j ∈ Finset.Ico (n / 2) n, yRow0_nat k j = -((n - n / 2 : ℕ) : ℂ) := by
    have h_tail_eq : ∀ j ∈ Finset.Ico (n / 2) n, yRow0_nat k j = -1 := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      rcases hj with ⟨hj1, hj2⟩
      dsimp [yRow0_nat]
      split_ifs with c1 c2 c3
      · omega
      · omega
      · omega
      · rfl
    rw [Finset.sum_congr rfl h_tail_eq, Finset.sum_const]
    simp

  rw [h_head, h_mid, h_tail]

  -- 3. Resolve natural subtraction BEFORE casting to ℂ
  have h1 : n / 2 - 2 = 2 * k - 1 := by dsimp [n]; omega
  have h2 : n - n / 2 = 2 * k + 1 := by dsimp [n]; omega
  rw [h1, h2]

  have hk_ge : 1 ≤ 2 * k := by omega
  rw [Nat.cast_sub hk_ge]
  push_cast
  ring

-------------------------------------------------------------------------------
-- Proof for deltaY and yRow1
-------------------------------------------------------------------------------

lemma deltaY_sum_zero (k : ℕ) (hk : 0 < k) : ∑ j : Fin (2 * (2 * k + 1)), deltaY k j = 0 := by
  let n := 2 * (2 * k + 1)

  have h_eq : ∑ j : Fin n, deltaY k j = ∑ j ∈ Finset.range n, deltaY_nat k j := by
    change ∑ j : Fin n, deltaY_nat k j.val = ∑ j ∈ Finset.range n, deltaY_nat k j
    exact Fin.sum_univ_eq_sum_range (deltaY_nat k) n
  rw [h_eq]

  have h2 : 2 ≤ 2 * k + 1 := by omega
  have hmid : 2 * k + 1 ≤ 2 * k + 3 := by omega
  have htail : 2 * k + 3 ≤ n := by dsimp [n]; omega

  -- Split range n into four sub-intervals using exact arithmetic bounds
  rw [← Finset.sum_range_add_sum_Ico (deltaY_nat k) htail]
  rw [← Finset.sum_range_add_sum_Ico (deltaY_nat k) hmid]
  rw [← Finset.sum_range_add_sum_Ico (deltaY_nat k) h2]

  -- 1. Interval [0, 2)
  have h_head : ∑ j ∈ Finset.range 2, deltaY_nat k j = -4 := by
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    dsimp [deltaY_nat]
    ring

  -- 2. Interval [2, 2*k + 1)
  have h_mid1 : ∑ j ∈ Finset.Ico 2 (2 * k + 1), deltaY_nat k j = 0 := by
    have h_zero : ∀ j ∈ Finset.Ico 2 (2 * k + 1), deltaY_nat k j = 0 := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      rcases hj with ⟨hj1, hj2⟩
      dsimp [deltaY_nat]
      split_ifs <;> first | rfl | omega
    rw [Finset.sum_congr rfl h_zero, Finset.sum_const_zero]

  -- 3. Interval [2*k + 1, 2*k + 3)
  have h_mid2 : ∑ j ∈ Finset.Ico (2 * k + 1) (2 * k + 3), deltaY_nat k j = 4 := by
    have h_split : Finset.Ico (2 * k + 1) (2 * k + 3) = {2 * k + 1, 2 * k + 2} := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_insert, Finset.mem_singleton]
      omega
    rw [h_split]
    have h_disj : 2 * k + 1 ∉ ({2 * k + 2} : Finset ℕ) := by simp
    rw [Finset.sum_insert h_disj, Finset.sum_singleton]
    dsimp [deltaY_nat]
    split_ifs <;> first | rfl | omega | ring

  -- 4. Interval [2*k + 3, n)
  have h_tail : ∑ j ∈ Finset.Ico (2 * k + 3) n, deltaY_nat k j = 0 := by
    have h_zero : ∀ j ∈ Finset.Ico (2 * k + 3) n, deltaY_nat k j = 0 := by
      intro j hj
      rw [Finset.mem_Ico] at hj
      rcases hj with ⟨hj1, hj2⟩
      dsimp [deltaY_nat]
      split_ifs <;> first | rfl | omega
    rw [Finset.sum_congr rfl h_zero, Finset.sum_const_zero]

  rw [h_head, h_mid1, h_mid2, h_tail]
  ring

theorem yRow1_sum_zero (k : ℕ) (hk : 0 < k) : ∑ j, yRow1 k j = 0 := by
  have h_eq : ∀ j : Fin (2 * (2 * k + 1)), yRow1 k j = yRow0 k j + deltaY k j := by
    intro j
    let n := 2 * (2 * k + 1)
    have hn_div : n / 2 = 2 * k + 1 := by dsimp [n]; omega
    dsimp [yRow1, yRow0, deltaY, deltaY_nat]
    rw [hn_div]
    split_ifs <;> first | rfl | omega | ring
  simp_rw [h_eq]
  rw [Finset.sum_add_distrib, yRow0_sum_zero k hk, deltaY_sum_zero k hk, add_zero]

theorem yRow_sum_zero (k : ℕ) (hk : 0 < k) : (i : ℕ) → ∑ j, yRow k i j = 0
  | 0 => yRow0_sum_zero k hk
  | 1 => yRow1_sum_zero k hk
  | i + 2 => by
    dsimp [yRow]
    exact Sum_cyclic_0 2 _ (yRow_sum_zero k hk i)

theorem yMatrix_all_row_sums_zero (k : ℕ) (hk : 0 < k) : AllRowSum_C (yMatrix k) := by
  intro i
  dsimp [AllRowSum_C, rowSumC, yMatrix]
  exact yRow_sum_zero k hk i.val



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

--Row 1:

--note for Row1-4, we cannot use the symmetry, hence we do the perturbation to make
-- the row in sym in term of row0

def deltaRow1 (k : ℕ) (j : Fin (5 * (2 * k + 1))) : ℂ :=
  if j.val = 0 then -1
  else if j.val = 1 then -1
  else if j.val = 2 then 1
  else if j.val = 3 then 1
  else 0

lemma zRow1_eq_zRow0_add_delta (k : ℕ) (j : Fin (5 * (2 * k + 1))) :
    zRow1 k j = zRow0 k j + deltaRow1 k j := by
  dsimp [zRow1, zRow0, deltaRow1]
  split_ifs <;> ring_nf

lemma sum_piecewise_row {N h C : ℕ} (h_le_C : h ≤ C) (C_le_N : C ≤ N)
    (v : Fin N → ℂ) (head_sum : ℂ)
    (h_head : ∑ j ∈ Finset.range h, v ⟨j, by omega⟩ = head_sum)
    (h_mid  : ∀ j, h ≤ j → j < C → v ⟨j, by omega⟩ = 1)
    (h_tail : ∀ j, C ≤ j → j < N → v ⟨j, by omega⟩ = -1) :
    ∑ j : Fin N, v j = head_sum + (C - h : ℂ) - (N - C : ℂ) := by
  -- 1. Split Finset.univ into range C and its complement [C, N)
  rw [← Finset.sum_range_add_sum_Ico v C_le_N]
  -- 2. Split range C into range h and middle interval [h, C)
  rw [← Finset.sum_range_add_sum_Ico v h_le_C]
  -- 3. Replace head sum using hypothesis
  rw [h_head]
  -- 4. Evaluate middle sum over +1
  have h_mid_sum : ∑ j ∈ Finset.Ico h C, v ⟨j, by omega⟩ = (C - h : ℂ) := by
    rw [Finset.sum_congr rfl (fun j hj => h_mid j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2)]
    simp [Finset.sum_const, Card.fund]
  -- 5. Evaluate tail sum over -1
  have h_tail_sum : ∑ j ∈ Finset.Ico C N, v ⟨j, by omega⟩ = -(N - C : ℂ) := by
    rw [Finset.sum_congr rfl (fun j hj => h_tail j (Finset.mem_Ico.mp hj).1 (Finset.mem_Ico.mp hj).2)]
    simp [Finset.sum_const, Card.fund]
  -- Combine all three parts
  rw [h_mid_sum, h_tail_sum]
  ring



theorem zRow1_sum_zero (k : ℕ) : ∑ j, zRow1 k j = 0 := by
  simp_rw [zRow1_eq_zRow0_add_delta]
  rw [Finset.sum_add_distrib, zRow0_sum_zero k, deltaRow1_sum_zero k, add_zero]




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
