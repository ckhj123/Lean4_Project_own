import LeanProject.Families

/-!
# Properties of the ordinary C-family

For valid parameters, every row sums to zero, the matrix is skew-symmetric,
and every cyclic adjacent edge is smoothable. All statements use the
production `cFirstRow`, `cMatrix`, and graph predicates.
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
private theorem cFirstRow_neg {n k : ℕ} (h : ValidC n k) (a : Fin n) :
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
private theorem cMatrix_apply {n k : ℕ} (h : ValidC n k) (i j : Fin n) :
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

/-- Away from columns 0 and 1, moving one step right can only decrease the seed value.
The drop is 0, 1, or (when the two cutoffs meet) 2. -/
private theorem cFirstRow_adjacent_drop {n k : ℕ} [NeZero n] (h : ValidC n k)
    (l : Fin n) (hl0 : l ≠ 0) (hl1 : l ≠ 1) :
    ∃ m : ℕ, cFirstRow n k (l - 1) - cFirstRow n k l = (m : ℂ) := by
  have hx0 : l.val ≠ 0 := by
    intro hz
    apply hl0
    apply Fin.ext
    simpa using hz
  have hx1 : l.val ≠ 1 := by
    intro hz
    apply hl1
    apply Fin.ext
    simpa [Fin.val_one', Nat.mod_eq_of_lt (by have := h.2.1; omega : 1 < n)] using hz
  have hx2 : 2 ≤ l.val := by omega
  have hp : (l - 1).val = l.val - 1 := Fin.val_sub_one_of_ne_zero hl0
  have hp0 : l.val - 1 ≠ 0 := by omega
  have hpfin : l - 1 ≠ 0 := by
    intro hz
    have hv := congrArg Fin.val hz
    simp [hp, hp0] at hv
  have hk : 1 ≤ k := h.1
  have hsep : 2 * k < n := h.2.2
  refine ⟨(if l.val = k + 1 then 1 else 0) +
    (if l.val = n - k then 1 else 0), ?_⟩
  simp only [cFirstRow]
  rw [hp]
  -- The two indicators record the two possible downward jumps of the seed row.
  split_ifs <;> (try omega) <;> norm_num

/-- The first adjacent edge is smoothable: its coloring coefficients are seed drops. -/
private theorem cMatrix_base_adjacent_smoothable {n k : ℕ} [NeZero n] (h : ValidC n k) :
    IsSmoothableEdge (cMatrix n k) 0 1 := by
  have hone : cFirstRow n k (1 : Fin n) = 1 := by
    have hk := h.1
    have hn := h.2.1
    have hmod : 1 % n = 1 := Nat.mod_eq_of_lt (by omega)
    simp [cFirstRow, hmod, hk]
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have hv := congrArg Fin.val he
    have hn := h.2.1
    simp at hv
    omega
  · simp [cMatrix_apply h, hone]
  · intro l hl0 hl1
    obtain ⟨m, hm⟩ := cFirstRow_adjacent_drop h l hl0 hl1
    refine ⟨m, ?_⟩
    simpa [cMatrix_apply h, cFirstRow_neg h, hone, sub_eq_add_neg] using hm

/-- Adding the same cyclic offset to both indices leaves a circulant entry unchanged. -/
private theorem cMatrix_add_invariant {n k : ℕ} [NeZero n] (h : ValidC n k)
    (a b t : Fin n) :
    cMatrix n k (a + t) (b + t) = cMatrix n k a b := by
  rw [cMatrix_apply h, cMatrix_apply h]
  congr 1
  abel

/-- Every cyclic adjacent edge is smoothable, including the wraparound edge. -/
theorem cMatrix_adjacent_smoothable {n k : ℕ} (h : ValidC n k) (i : Fin n) :
    IsSmoothableEdge (cMatrix n k) i (finRotate n i) := by
  haveI : NeZero n := ⟨by have := h.2.1; omega⟩
  rw [finRotate_apply]
  obtain ⟨hbne, hbentry, hbcolor⟩ := cMatrix_base_adjacent_smoothable h
  have hentry : cMatrix n k i (i + 1) = cMatrix n k 0 1 := by
    simpa [add_comm] using cMatrix_add_invariant h 0 1 i
  refine ⟨?_, ?_, ?_⟩
  · intro he
    have h01 : (0 : Fin n) = 1 := by
      apply add_right_cancel (b := i)
      simpa [add_comm] using he
    exact hbne h01
  · rw [hentry]
    exact hbentry
  · intro l hli hlj
    let x : Fin n := l - i
    have hx0 : x ≠ 0 := by
      intro hx
      have hli' : l = i := by
        calc
          l = x + i := by dsimp [x]; abel
          _ = i := by simp [hx]
      exact hli hli'
    have hx1 : x ≠ 1 := by
      intro hx
      have hlj' : l = i + 1 := by
        calc
          l = x + i := by dsimp [x]; abel
          _ = i + 1 := by rw [hx]; abel
      exact hlj hlj'
    obtain ⟨m, hm⟩ := hbcolor x hx0 hx1
    refine ⟨m, ?_⟩
    have hleft : cMatrix n k (i + 1) l = cMatrix n k 1 x := by
      simpa [x, add_comm, sub_add_cancel] using cMatrix_add_invariant h 1 x i
    have hright : cMatrix n k l i = cMatrix n k x 0 := by
      simpa [x, sub_add_cancel] using cMatrix_add_invariant h x 0 i
    rw [hleft, hright, hentry]
    exact hm

end SkewMatrixGraph
