import LeanProject.SkewSymmetryProperties
import LeanProject.Smooth_cycle

/-! Smoothability of cyclic adjacent edges in the C, X₄, X₅, Y, and Z families.
The periodic families reduce to their seed edges by simultaneous cyclic shifts. -/

namespace SkewMatrixGraph

section CFamily

set_option linter.style.haveILetI false

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

theorem cMatrix_base_edge (n k : ℕ) (h_valid : ValidC n k) :
    IsSmoothableEdge (cMatrix n k)
      ⟨0, by have := h_valid.2.1; omega⟩
      ⟨1, by have := h_valid.2.1; omega⟩ := by
  haveI : NeZero n := ⟨by have := h_valid.2.1; omega⟩
  have hj : finRotate n (⟨0, by have := h_valid.2.1; omega⟩ : Fin n) =
      (⟨1, by have := h_valid.2.1; omega⟩ : Fin n) := by
    apply Fin.ext
    simp [finRotate_apply, Fin.add_def,
      Nat.mod_eq_of_lt (by have := h_valid.2.1; omega : 1 < n)]
  rw [← hj]
  exact cMatrix_adjacent_smoothable h_valid
    (⟨0, by have := h_valid.2.1; omega⟩ : Fin n)

theorem cMatrix_all_edges (n k : ℕ) (h_valid : ValidC n k) (i : Fin n) :
    IsSmoothableEdge (cMatrix n k) i (finRotate n i) := by
  exact cMatrix_adjacent_smoothable h_valid i

end CFamily

/-- Every cyclic adjacent edge of the fixed X₄ matrix is smoothable. -/
theorem x4Matrix_adjacent_smoothable (i : Fin 4) :
    IsSmoothableEdge x4Matrix i (finRotate 4 i) := by
  fin_cases i <;>
    simp only [IsSmoothableEdge, finRotate_apply] <;>
    refine ⟨by decide, by norm_num [x4Matrix], ?_⟩ <;>
    intro t ht0 ht1 <;>
    fin_cases t <;>
    solve
    | exact False.elim (ht0 rfl)
    | exact False.elim (ht1 rfl)
    | refine ⟨0, ?_⟩; norm_num [x4Matrix]
    | refine ⟨1, ?_⟩; norm_num [x4Matrix]
    | refine ⟨2, ?_⟩; norm_num [x4Matrix]

/-- Every cyclic adjacent edge of the fixed X₅ matrix is smoothable. -/
theorem x5Matrix_adjacent_smoothable (i : Fin 5) :
    IsSmoothableEdge x5Matrix i (finRotate 5 i) := by
  fin_cases i <;>
    simp only [IsSmoothableEdge, finRotate_apply] <;>
    refine ⟨by decide, by norm_num [x5Matrix], ?_⟩ <;>
    intro t ht0 ht1 <;>
    fin_cases t <;>
    solve
    | exact False.elim (ht0 rfl)
    | exact False.elim (ht1 rfl)
    | refine ⟨0, ?_⟩; norm_num [x5Matrix]
    | refine ⟨1, ?_⟩; norm_num [x5Matrix]
    | refine ⟨2, ?_⟩; norm_num [x5Matrix]

/-- After q seed blocks, a row and all its columns have shifted by the same amount. -/
private theorem periodic_row_block_smooth {n p : ℕ} {α : Type*}
    (row : ℕ → Fin n → α)
    (hstep : ∀ i, row (i + p) = cyclicRightShift p (row i))
    (q a : ℕ) :
    row (p * q + a) = cyclicRightShift (p * q) (row a) := by
  induction q with
  | zero => simp
  | succ q ih =>
      calc
        row (p * (q + 1) + a) = row ((p * q + a) + p) := by congr 1; ring
        _ = cyclicRightShift p (row (p * q + a)) := hstep _
        _ = cyclicRightShift p (cyclicRightShift (p * q) (row a)) := by rw [ih]
        _ = cyclicRightShift (p * (q + 1)) (row a) := by
          rw [← cyclicRightShift_add]
          congr 1

/-- Simultaneously shifting row and column indices by whole seed blocks
preserves a periodically generated matrix. -/
private theorem periodic_matrix_shift {p m : ℕ} [NeZero (p * m)]
    (hp : 0 < p) (hm : 0 < m)
    (row : ℕ → Fin (p * m) → ℂ)
    (hstep : ∀ i, row (i + p) = cyclicRightShift p (row i))
    (q : ℕ) (hq : q < m) (i j : Fin (p * m)) :
    row (i + Fin.ofNat (p * m) (p * q)).val
      (j + Fin.ofNat (p * m) (p * q)) = row i.val j := by
  let n := p * m
  let s := p * q
  haveI : NeZero n := ⟨by dsimp [n]; exact Nat.ne_of_gt (Nat.mul_pos hp hm)⟩
  have hs : s < n := Nat.mul_lt_mul_of_pos_left hq hp
  have hcast : (Fin.ofNat n s).val = s := by
    simp [Fin.ofNat, Nat.mod_eq_of_lt hs]
  have hval : (i + Fin.ofNat n s).val = (i.val + s) % n := by
    simp [Fin.val_add, hcast, n]
  have hshift (u : ℕ) : cyclicRightShift n (row u) = row u := by
    funext x
    rw [cyclicRightShift_apply_sub]
    have hzero : Fin.ofNat n n = 0 := by
      apply Fin.ext
      simp [Fin.ofNat]
    rw [hzero]
    simp
  have hperiod (u : ℕ) : row (u + n) = row u := by
    have h := periodic_row_block_smooth row hstep m u
    simpa [n, Nat.add_comm, hshift u] using h
  have hmodrow : row ((i.val + s) % n) = row (i.val + s) := by
    by_cases hlt : i.val + s < n
    · rw [Nat.mod_eq_of_lt hlt]
    · have hlt2 : i.val + s < 2 * n := by have := i.isLt; omega
      have hmod : (i.val + s) % n = i.val + s - n := by
        rw [Nat.mod_eq_sub_mod (by omega : n ≤ i.val + s)]
        exact Nat.mod_eq_of_lt (by omega)
      rw [hmod]
      have heq : i.val + s - n + n = i.val + s := by omega
      have hperiod' := hperiod (i.val + s - n)
      rw [heq] at hperiod'
      exact hperiod'.symm
  change row (i + Fin.ofNat n s).val (j + Fin.ofNat n s) = row i.val j
  rw [hval, hmodrow]
  have hblock : row (i.val + s) = cyclicRightShift s (row i.val) := by
    simpa [s, Nat.add_comm] using periodic_row_block_smooth row hstep q i.val
  rw [hblock, cyclicRightShift_apply_sub]
  simp [n]

/-- It suffices to check the p adjacent edges in the seed block. -/
private theorem periodic_adjacent_smoothable {p m : ℕ} [NeZero (p * m)]
    (hp : 0 < p) (hm : 0 < m)
    (row : ℕ → Fin (p * m) → ℂ)
    (hstep : ∀ i, row (i + p) = cyclicRightShift p (row i))
    (hbase : ∀ a, a < p →
      IsSmoothableEdge (fun i : Fin (p * m) => row i.val)
        (Fin.ofNat (p * m) a) (Fin.ofNat (p * m) (a + 1)))
    (i : Fin (p * m)) :
    IsSmoothableEdge (fun i : Fin (p * m) => row i.val) i
      (finRotate (p * m) i) := by
  let n := p * m
  let q := i.val / p
  let a := i.val % p
  let s := p * q
  have ha : a < p := Nat.mod_lt _ hp
  have hq : q < m := by
    apply (Nat.div_lt_iff_lt_mul hp).2
    simpa [q, n, mul_comm] using i.isLt
  have hval : i.val = s + a := by
    simpa [q, a, s, Nat.add_comm] using (Nat.mod_add_div i.val p).symm
  have hcast (u v : ℕ) : Fin.ofNat n (u + v) =
      Fin.ofNat n u + Fin.ofNat n v := by
    apply Fin.ext
    simp [Fin.ofNat, Fin.add_def, Nat.add_mod]
  have hi : Fin.ofNat n a + Fin.ofNat n s = i := by
    rw [← hcast, Nat.add_comm a s, ← hval]
    apply Fin.ext
    simp [n, Fin.ofNat, Nat.mod_eq_of_lt i.isLt]
  let B : Matrix (Fin n) (Fin n) ℂ := fun i => row i.val
  let e : Fin n ≃ Fin n := Equiv.addRight (Fin.ofNat n s)
  have hB (x y : Fin n) : B (e x) (e y) = B x y := by
    exact periodic_matrix_shift hp hm row hstep q hq x y
  have hnext : e (Fin.ofNat n (a + 1)) = finRotate n i := by
    have hone : Fin.ofNat n 1 = (1 : Fin n) := by
      apply Fin.ext
      simp [Fin.ofNat]
    change Fin.ofNat n (a + 1) + Fin.ofNat n s = finRotate n i
    rw [hcast a 1, hone, finRotate_apply, ← hi]
    abel
  have h := (IsSmoothableEdge_equiv B e hB
    (Fin.ofNat n a) (Fin.ofNat n (a + 1))).2 (hbase a ha)
  change e (Fin.ofNat n a) = i at hi
  change IsSmoothableEdge B i (finRotate n i)
  rw [hi, hnext] at h
  exact h

private theorem y_base01 (k : ℕ) (hk : 0 < k) :
    IsSmoothableEdge (yMatrix k)
      (⟨0, by omega⟩ : Fin (2 * (2 * k + 1)))
      (⟨1, by omega⟩ : Fin (2 * (2 * k + 1))) := by
  let N := 2 * (2 * k + 1)
  let i : Fin N := ⟨0, by dsimp [N]; omega⟩
  let j : Fin N := ⟨1, by dsimp [N]; omega⟩
  change IsSmoothableEdge (yMatrix k) i j
  have hedge : yMatrix k i j = 2 := by
    norm_num [yMatrix, yRow, yRow0, i, j]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    norm_num [i, j] at hv
  · rw [hedge]
    norm_num
  · intro t ht0 ht1
    have hskew : yMatrix k t i = -yMatrix k i t := by
      have h := congrFun (congrFun (yMatrix_skewSymmetric k) i) t
      simpa [IsSkewSymmetric, Matrix.transpose_apply] using h
    rw [hskew, hedge]
    change ∃ m : ℕ, yRow1 k t - yRow0 k t = (m : ℂ) * 2
    have ht0val : t.val ≠ 0 := by
      intro hz
      apply ht0
      apply Fin.ext
      simpa [i] using hz
    have ht1val : t.val ≠ 1 := by
      intro hz
      apply ht1
      apply Fin.ext
      simpa [j] using hz
    have hhalf : N / 2 = 2 * k + 1 := by dsimp [N]; omega
    dsimp [yRow1, yRow0]
    split_ifs <;> (try omega) <;>
      solve
      | refine ⟨0, ?_⟩; norm_num
      | refine ⟨1, ?_⟩; norm_num

private theorem y_base12 (k : ℕ) (hk : 0 < k) :
    IsSmoothableEdge (yMatrix k)
      (⟨1, by omega⟩ : Fin (2 * (2 * k + 1)))
      (⟨2, by omega⟩ : Fin (2 * (2 * k + 1))) := by
  let N := 2 * (2 * k + 1)
  let i : Fin N := ⟨1, by dsimp [N]; omega⟩
  let j : Fin N := ⟨2, by dsimp [N]; omega⟩
  change IsSmoothableEdge (yMatrix k) i j
  have hedge : yMatrix k i j = 1 := by
    norm_num [yMatrix, yRow, yRow1, i, j]
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    norm_num [i, j] at hv
  · rw [hedge]
    norm_num
  · intro t ht1 ht2
    have hskew : yMatrix k t i = -yMatrix k i t := by
      have h := congrFun (congrFun (yMatrix_skewSymmetric k) i) t
      simpa [IsSkewSymmetric, Matrix.transpose_apply] using h
    rw [hskew, hedge]
    change ∃ m : ℕ, yRow k 2 t - yRow1 k t = (m : ℂ) * 1
    have ht1val : t.val ≠ 1 := by
      intro hz
      apply ht1
      apply Fin.ext
      simpa [i] using hz
    have ht2val : t.val ≠ 2 := by
      intro hz
      apply ht2
      apply Fin.ext
      simpa [j] using hz
    have hhalf : N / 2 = 2 * k + 1 := by dsimp [N]; omega
    by_cases ht0 : t.val = 0
    · have ht : t = (⟨0, by dsimp [N]; omega⟩ : Fin N) := Fin.ext ht0
      rw [ht]
      haveI : NeZero N := ⟨by dsimp [N]; omega⟩
      have htwo : (Fin.ofNat N 2).val = 2 := by
        simp [Fin.ofNat, Nat.mod_eq_of_lt (by dsimp [N]; omega : 2 < N)]
      have hv : ((⟨0, by dsimp [N]; omega⟩ : Fin N) - Fin.ofNat N 2).val =
          N - 2 := by
        rw [Fin.val_sub, htwo]
        simp [Nat.mod_eq_of_lt (by dsimp [N]; omega : N - 2 < N)]
      have hv' : ((⟨0, by omega⟩ : Fin (2 * (2 * k + 1))) -
          Fin.ofNat (2 * (2 * k + 1)) 2).val = 2 * (2 * k + 1) - 2 := by
        simpa [N] using hv
      have hbig : ¬ N - 2 < N / 2 := by rw [hhalf]; dsimp [N]; omega
      change ∃ m : ℕ,
        cyclicRightShift 2 (yRow0 k) (⟨0, by dsimp [N]; omega⟩ : Fin N) -
          yRow1 k (⟨0, by dsimp [N]; omega⟩ : Fin N) = (m : ℂ) * 1
      refine ⟨1, ?_⟩
      rw [cyclicRightShift_apply_sub]
      dsimp only [yRow0, yRow1]
      rw [hv']
      have hzero : N - 2 ≠ 0 := by dsimp [N]; omega
      have hone : N - 2 ≠ 1 := by dsimp [N]; omega
      have hnot : ¬ 2 * (2 * k + 1) ≤ 2 * k + 2 := by omega
      have hzero' : 2 * (2 * k + 1) - 2 ≠ 0 := by omega
      have hone' : 2 * (2 * k + 1) - 2 ≠ 1 := by omega
      simp [hzero', hone', hnot]
      norm_num
    · have htge : 3 ≤ t.val := by omega
      haveI : NeZero N := ⟨by dsimp [N]; omega⟩
      have htwo : (Fin.ofNat N 2).val = 2 := by
        simp [Fin.ofNat, Nat.mod_eq_of_lt (by dsimp [N]; omega : 2 < N)]
      have hle : Fin.ofNat N 2 ≤ t := by
        apply Fin.le_iff_val_le_val.mpr
        rw [htwo]
        omega
      have hv : (t - Fin.ofNat N 2).val = t.val - 2 := by
        rw [Fin.sub_val_of_le hle, htwo]
      have hv' : (t - (2 : Fin (2 * (2 * k + 1)))).val = t.val - 2 := by
        simpa [N] using hv
      change ∃ m : ℕ,
        cyclicRightShift 2 (yRow0 k) t - yRow1 k t = (m : ℂ) * 1
      rw [cyclicRightShift_apply_sub]
      dsimp [yRow0, yRow1]
      rw [hv']
      by_cases ht3 : t.val = 3
      · have hcut3 : 3 < N / 2 + 2 := by rw [hhalf]; omega
        refine ⟨1, ?_⟩
        rw [ht3]
        norm_num [hcut3, hk]
      · have htge4 : 4 ≤ t.val := by omega
        have hzero : t.val - 2 ≠ 0 := by omega
        have hone : t.val - 2 ≠ 1 := by omega
        have htzero : t.val ≠ 0 := by omega
        have hcut : (t.val - 2 < N / 2) ↔ t.val < N / 2 + 2 := by omega
        have htest : (t.val ≤ 2 * k + 2) ↔ t.val < 2 * k + 3 := by omega
        refine ⟨0, ?_⟩
        simp [hzero, hone, htzero, ht1val, hcut, htest]


/-- Every cyclic adjacent Y-edge is smoothable when the seed dimensions are nondegenerate. -/
theorem yMatrix_adjacent_smoothable (k : ℕ) (hk : 0 < k)
    (i : Fin (2 * (2 * k + 1))) :
    IsSmoothableEdge (yMatrix k) i (finRotate (2 * (2 * k + 1)) i) := by
  haveI : NeZero (2 * (2 * k + 1)) := ⟨by omega⟩
  change IsSmoothableEdge (fun j : Fin (2 * (2 * k + 1)) => yRow k j.val)
    i (finRotate (2 * (2 * k + 1)) i)
  apply periodic_adjacent_smoothable (by omega : 0 < 2)
    (by omega : 0 < 2 * k + 1) (yRow k) (yRow_add_two k)
  intro a ha
  interval_cases a
  · change IsSmoothableEdge (yMatrix k) 0 1
    exact y_base01 k hk
  · have h1 : Fin.ofNat (2 * (2 * k + 1)) 1 =
        (⟨1, by omega⟩ : Fin (2 * (2 * k + 1))) := by
      apply Fin.ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt (by omega : 1 < 2 * (2 * k + 1))]
    have h2 : Fin.ofNat (2 * (2 * k + 1)) 2 =
        (⟨2, by omega⟩ : Fin (2 * (2 * k + 1))) := by
      apply Fin.ext
      simp [Fin.ofNat, Nat.mod_eq_of_lt (by omega : 2 < 2 * (2 * k + 1))]
    rw [h1, h2]
    change IsSmoothableEdge (yMatrix k) _ _
    exact y_base12 k hk

/-- Beyond the first five columns, an increasing cutoff changes a row
difference only from 0 to 2. -/
private theorem z_large_adjacent_difference (k a b : ℕ) (w : ℂ) (r : ℕ)
    (ha : a < 5) (hb : b < 5)
    (hcut : zSeedCutoff k a ≤ zSeedCutoff k b)
    (hw : (2 : ℂ) = (r : ℂ) * w)
    (t : Fin (5 * (2 * k + 1))) (ht : 5 ≤ t.val) :
    ∃ m : ℕ, zRow k b t - zRow k a t = (m : ℂ) * w := by
  rw [zRow_large k b hb t ht, zRow_large k a ha t ht]
  by_cases hleft : t.val < zSeedCutoff k a
  · have hright : t.val < zSeedCutoff k b := lt_of_lt_of_le hleft hcut
    refine ⟨0, ?_⟩
    simp [hleft, hright]
  · by_cases hright : t.val < zSeedCutoff k b
    · refine ⟨r, ?_⟩
      simp only [if_pos hright, if_neg hleft]
      calc
        (1 : ℂ) - (-1) = 2 := by ring
        _ = (r : ℂ) * w := hw
    · refine ⟨0, ?_⟩
      simp [hleft, hright]

private theorem z_base01 (k : ℕ) (hk : 0 < k) :
    IsSmoothableEdge (zMatrix k)
      (⟨0, by omega⟩ : Fin (5 * (2 * k + 1)))
      (⟨1, by omega⟩ : Fin (5 * (2 * k + 1))) := by
  let N := 5 * (2 * k + 1)
  let i : Fin N := ⟨0, by dsimp [N]; omega⟩
  let j : Fin N := ⟨1, by dsimp [N]; omega⟩
  change IsSmoothableEdge (zMatrix k) i j
  have hedge : zMatrix k i j = 1 := by
    norm_num [zMatrix, zRow, zRow0, i, j] <;> omega
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    norm_num [i, j] at hv
  · rw [hedge]
    norm_num
  · intro t ht0 ht1
    have hskew : zMatrix k t i = -zMatrix k i t := by
      have h := congrFun (congrFun (zMatrix_skewSymmetric k hk) i) t
      simpa [IsSkewSymmetric, Matrix.transpose_apply] using h
    rw [hskew, hedge]
    change ∃ m : ℕ, zRow k 1 t - zRow k 0 t = (m : ℂ) * 1
    have ht0val : t.val ≠ 0 := by
      intro hz
      apply ht0
      apply Fin.ext
      simpa [i] using hz
    have ht1val : t.val ≠ 1 := by
      intro hz
      apply ht1
      apply Fin.ext
      simpa [j] using hz
    have hhalf : (5 * (2 * k + 1) - 1) / 2 = 5 * k + 2 := by omega
    by_cases hsmall : t.val < 5
    · have ht0fin : t ≠ (0 : Fin N) := by
        intro hz
        apply ht0val
        simpa [hz]
      have hcut : t.val ≤ (5 * (2 * k + 1) - 1) / 2 := by rw [hhalf]; omega
      by_cases h2 : t.val = 2
      · refine ⟨1, ?_⟩
        simp [zRow, zRow0, zRow1, ht0fin, ht1val, h2, hcut, hhalf]
        norm_num
      · by_cases h3 : t.val = 3
        · refine ⟨1, ?_⟩
          simp [zRow, zRow0, zRow1, ht0fin, ht1val, h2, h3, hcut, hhalf]
          norm_num [hk]
        · have h4 : t.val = 4 := by omega
          refine ⟨0, ?_⟩
          simp [zRow, zRow0, zRow1, ht0fin, ht1val, h2, h3, h4, hcut, hhalf]
    · have hlarge : 5 ≤ t.val := by omega
      rw [zRow_large k 1 (by omega) t hlarge,
        zRow_large k 0 (by omega) t hlarge]
      refine ⟨0, ?_⟩
      simp [zSeedCutoff]

/-- To check a consecutive pair of Z seed rows, only their first five
columns require a separate calculation; the rest follow from cutoffs. -/
private theorem z_seed_adjacent_of_rows (k : ℕ) (hk : 0 < k)
    (i j : Fin (5 * (2 * k + 1))) (hi : i.val < 4)
    (hj : j.val = i.val + 1) (w : ℂ) (hw : w ≠ 0)
    (hweight : zMatrix k i j = w)
    (hhead : ∀ t : Fin (5 * (2 * k + 1)), t.val < 5 →
      t.val ≠ i.val → t.val ≠ j.val →
      ∃ m : ℕ, zRow k j.val t - zRow k i.val t = (m : ℂ) * w)
    (hcut : zSeedCutoff k i.val ≤ zSeedCutoff k j.val)
    (r : ℕ) (hr : (2 : ℂ) = (r : ℂ) * w) :
    IsSmoothableEdge (zMatrix k) i j := by
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    have hv := congrArg Fin.val heq
    omega
  · simpa [hweight] using hw
  · intro t ht0 ht1
    have hskew : zMatrix k t i = -zMatrix k i t := by
      have h := congrFun (congrFun (zMatrix_skewSymmetric k hk) i) t
      simpa [IsSkewSymmetric, Matrix.transpose_apply] using h
    rw [hskew, hweight]
    change ∃ m : ℕ, zRow k j.val t - zRow k i.val t = (m : ℂ) * w
    have hti : t.val ≠ i.val := by
      intro heq
      exact ht0 (Fin.ext heq)
    have htj : t.val ≠ j.val := by
      intro heq
      exact ht1 (Fin.ext heq)
    by_cases hsmall : t.val < 5
    · exact hhead t hsmall hti htj
    · exact z_large_adjacent_difference k i.val j.val w r
        (by omega) (by omega) hcut hr t (by omega)

private theorem z_base12 (k : ℕ) (hk : 0 < k) :
    IsSmoothableEdge (zMatrix k)
      (⟨1, by omega⟩ : Fin (5 * (2 * k + 1)))
      (⟨2, by omega⟩ : Fin (5 * (2 * k + 1))) := by
  let i : Fin (5 * (2 * k + 1)) := ⟨1, by omega⟩
  let j : Fin (5 * (2 * k + 1)) := ⟨2, by omega⟩
  change IsSmoothableEdge (zMatrix k) i j
  refine z_seed_adjacent_of_rows k hk i j (by norm_num [i])
    (by norm_num [i, j]) 2 (by norm_num) ?_ ?_ ?_ 1 ?_
  · norm_num [zMatrix, zRow, zRow1, i, j]
  · intro t hsmall hti htj
    change ∃ m : ℕ, zRow2 k t - zRow1 k t = (m : ℂ) * 2
    have hhalf : (5 * (2 * k + 1) - 1) / 2 = 5 * k + 2 := by omega
    refine ⟨0, ?_⟩
    dsimp [zRow1, zRow2]
    split_ifs <;> (try omega) <;> norm_num
  · simp [zSeedCutoff, i, j]
  · norm_num

private theorem z_base23 (k : ℕ) (hk : 0 < k) :
    IsSmoothableEdge (zMatrix k)
      (⟨2, by omega⟩ : Fin (5 * (2 * k + 1)))
      (⟨3, by omega⟩ : Fin (5 * (2 * k + 1))) := by
  let i : Fin (5 * (2 * k + 1)) := ⟨2, by omega⟩
  let j : Fin (5 * (2 * k + 1)) := ⟨3, by omega⟩
  change IsSmoothableEdge (zMatrix k) i j
  refine z_seed_adjacent_of_rows k hk i j (by norm_num [i])
    (by norm_num [i, j]) 2 (by norm_num) ?_ ?_ ?_ 1 ?_
  · norm_num [zMatrix, zRow, zRow2, i, j]
  · intro t hsmall hti htj
    change ∃ m : ℕ, zRow3 k t - zRow2 k t = (m : ℂ) * 2
    refine ⟨0, ?_⟩
    dsimp [zRow2, zRow3]
    split_ifs <;> (try omega) <;> norm_num
  · simp [zSeedCutoff, i, j]
  · norm_num

private theorem z_base34 (k : ℕ) (hk : 0 < k) :
    IsSmoothableEdge (zMatrix k)
      (⟨3, by omega⟩ : Fin (5 * (2 * k + 1)))
      (⟨4, by omega⟩ : Fin (5 * (2 * k + 1))) := by
  let i : Fin (5 * (2 * k + 1)) := ⟨3, by omega⟩
  let j : Fin (5 * (2 * k + 1)) := ⟨4, by omega⟩
  change IsSmoothableEdge (zMatrix k) i j
  refine z_seed_adjacent_of_rows k hk i j (by norm_num [i])
    (by norm_num [i, j]) 1 (by norm_num) ?_ ?_ ?_ 2 ?_
  · norm_num [zMatrix, zRow, zRow3, i, j]
  · intro t hsmall hti htj
    change ∃ m : ℕ, zRow4 k t - zRow3 k t = (m : ℂ) * 1
    by_cases h12 : t.val = 1 ∨ t.val = 2
    · refine ⟨1, ?_⟩
      dsimp [zRow3, zRow4]
      split_ifs <;> (try omega) <;> norm_num
    · refine ⟨0, ?_⟩
      dsimp [zRow3, zRow4]
      split_ifs <;> (try omega) <;> norm_num
  · simp [zSeedCutoff, i, j]
  · norm_num


/-- The last Z seed edge wraps from row four to the shifted first seed row. -/
private theorem z_base45 (k : ℕ) (hk : 0 < k) :
    IsSmoothableEdge (zMatrix k)
      (⟨4, by omega⟩ : Fin (5 * (2 * k + 1)))
      (⟨5, by omega⟩ : Fin (5 * (2 * k + 1))) := by
  let N := 5 * (2 * k + 1)
  let i : Fin N := ⟨4, by dsimp [N]; omega⟩
  let j : Fin N := ⟨5, by dsimp [N]; omega⟩
  change IsSmoothableEdge (zMatrix k) i j
  have hedge : zMatrix k i j = 1 := by
    norm_num [zMatrix, zRow, zRow4, i, j] <;> omega
  refine ⟨?_, ?_, ?_⟩
  · intro h
    have hv := congrArg Fin.val h
    norm_num [i, j] at hv
  · rw [hedge]
    norm_num
  · intro t ht4 ht5
    have hskew : zMatrix k t i = -zMatrix k i t := by
      have h := congrFun (congrFun (zMatrix_skewSymmetric k hk) i) t
      simpa [IsSkewSymmetric, Matrix.transpose_apply] using h
    rw [hskew, hedge]
    change ∃ m : ℕ,
      cyclicRightShift 5 (zRow0 k) t - zRow4 k t = (m : ℂ) * 1
    have ht4val : t.val ≠ 4 := by
      intro hz
      exact ht4 (Fin.ext (by simpa [i] using hz))
    have ht5val : t.val ≠ 5 := by
      intro hz
      exact ht5 (Fin.ext (by simpa [j] using hz))
    haveI : NeZero N := ⟨by dsimp [N]; omega⟩
    have hfive : (Fin.ofNat N 5).val = 5 := by
      simp [Fin.ofNat, Nat.mod_eq_of_lt (by dsimp [N]; omega : 5 < N)]
    by_cases hsmall : t.val < 5
    · have hshift : (t - Fin.ofNat N 5).val = N - 5 + t.val := by
        rw [Fin.val_sub]
        rw [hfive]
        exact Nat.mod_eq_of_lt (by omega)
      have hshift' : (t - Fin.ofNat (5 * (2 * k + 1)) 5).val =
          5 * (2 * k + 1) - 5 + t.val := by
        simpa [N] using hshift
      have htail : ¬ 5 * (2 * k + 1) - 5 + t.val <
          (5 * (2 * k + 1) - 1) / 2 + 1 := by omega
      refine ⟨0, ?_⟩
      rw [cyclicRightShift_apply_sub]
      dsimp only [zRow0, zRow4]
      rw [hshift']
      split_ifs <;> (try omega) <;> norm_num
    · have hlarge : 5 ≤ t.val := by omega
      have hge6 : 6 ≤ t.val := by omega
      have hle : Fin.ofNat N 5 ≤ t := by
        apply Fin.le_iff_val_le_val.mpr
        rw [hfive]
        omega
      have hshift : (t - Fin.ofNat N 5).val = t.val - 5 := by
        rw [Fin.sub_val_of_le hle, hfive]
      have hshift' : (t - Fin.ofNat (5 * (2 * k + 1)) 5).val = t.val - 5 := by
        simpa [N] using hshift
      rw [cyclicRightShift_apply_sub]
      dsimp only [zRow0, zRow4]
      rw [hshift']
      have hnonzero : t.val - 5 ≠ 0 := by omega
      have h0 : t.val ≠ 0 := by omega
      have h1 : t.val ≠ 1 := by omega
      have h2 : t.val ≠ 2 := by omega
      have h3 : t.val ≠ 3 := by omega
      have h4 : t.val ≠ 4 := by omega
      have hhalf : (5 * (2 * k + 1) - 1) / 2 = 5 * k + 2 := by omega
      have hcut0 : (t.val - 5 < (5 * (2 * k + 1) - 1) / 2 + 1) ↔
          t.val < 5 * k + 8 := by rw [hhalf]; omega
      have hcut4 : (t.val < (5 * (2 * k + 1) - 1) / 2 + 5) ↔
          t.val < 5 * k + 7 := by rw [hhalf]
      simp only [hcut0, hcut4]
      by_cases hfirst : t.val < 5 * k + 7
      · refine ⟨0, ?_⟩
        have hnext : t.val < 5 * k + 8 := by omega
        simp [hnonzero, h0, h1, h2, h3, h4, hfirst, hnext]
      · by_cases hboundary : t.val = 5 * k + 7
        · refine ⟨2, ?_⟩
          simp [hnonzero, h0, h1, h2, h3, h4, hfirst, hboundary] <;> norm_num
        · refine ⟨0, ?_⟩
          have hnext : ¬ t.val < 5 * k + 8 := by omega
          simp [hnonzero, h0, h1, h2, h3, h4, hfirst, hboundary, hnext]

/-- All cyclic adjacent edges of the Z matrix are smoothable for `k ≥ 1`. -/
theorem zMatrix_adjacent_smoothable (k : ℕ) (hk : 0 < k)
    (i : Fin (5 * (2 * k + 1))) :
    IsSmoothableEdge (zMatrix k) i (finRotate (5 * (2 * k + 1)) i) := by
  haveI : NeZero (5 * (2 * k + 1)) := ⟨by omega⟩
  have hcast (a : ℕ) (ha : a < 5 * (2 * k + 1)) :
      Fin.ofNat (5 * (2 * k + 1)) a =
        (⟨a, ha⟩ : Fin (5 * (2 * k + 1))) := by
    apply Fin.ext
    simp [Fin.ofNat, Nat.mod_eq_of_lt ha]
  change IsSmoothableEdge (fun j : Fin (5 * (2 * k + 1)) => zRow k j.val)
    i (finRotate (5 * (2 * k + 1)) i)
  apply periodic_adjacent_smoothable (by omega : 0 < 5)
    (by omega : 0 < 2 * k + 1) (zRow k) (zRow_add_five k)
  intro a ha
  interval_cases a
  · change IsSmoothableEdge (zMatrix k)
      (Fin.ofNat (5 * (2 * k + 1)) 0) (Fin.ofNat (5 * (2 * k + 1)) 1)
    rw [hcast 0 (by omega), hcast 1 (by omega)]
    exact z_base01 k hk
  · change IsSmoothableEdge (zMatrix k)
      (Fin.ofNat (5 * (2 * k + 1)) 1) (Fin.ofNat (5 * (2 * k + 1)) 2)
    rw [hcast 1 (by omega), hcast 2 (by omega)]
    exact z_base12 k hk
  · change IsSmoothableEdge (zMatrix k)
      (Fin.ofNat (5 * (2 * k + 1)) 2) (Fin.ofNat (5 * (2 * k + 1)) 3)
    rw [hcast 2 (by omega), hcast 3 (by omega)]
    exact z_base23 k hk
  · change IsSmoothableEdge (zMatrix k)
      (Fin.ofNat (5 * (2 * k + 1)) 3) (Fin.ofNat (5 * (2 * k + 1)) 4)
    rw [hcast 3 (by omega), hcast 4 (by omega)]
    exact z_base34 k hk
  · change IsSmoothableEdge (zMatrix k)
      (Fin.ofNat (5 * (2 * k + 1)) 4) (Fin.ofNat (5 * (2 * k + 1)) 5)
    rw [hcast 4 (by omega), hcast 5 (by omega)]
    exact z_base45 k hk

end SkewMatrixGraph
