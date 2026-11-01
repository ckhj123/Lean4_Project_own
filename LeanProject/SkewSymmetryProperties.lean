import LeanProject.CFamilyProperties

/-!
# Skew-symmetry of the integrated matrix families

The ordinary C-family theorem is imported from `CFamilyProperties`. The fixed
X matrices are checked entrywise. For Y and Z, a periodic-row criterion reduces
the proof to compatibility of their seed rows at each cyclic block separation.
-/

set_option linter.style.haveILetI false

namespace SkewMatrixGraph

/-- The fixed X₄ matrix is skew-symmetric. -/
theorem x4Matrix_skewSymmetric : IsSkewSymmetric x4Matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [IsSkewSymmetric, x4Matrix, Matrix.transpose_apply]

/-- The fixed X₅ matrix is skew-symmetric. -/
theorem x5Matrix_skewSymmetric : IsSkewSymmetric x5Matrix := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [IsSkewSymmetric, x5Matrix, Matrix.transpose_apply]

private theorem periodic_row_block {n p : ℕ} {α : Type*}
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

/-- Read a periodically generated row from its seed at a cyclic difference. -/
private theorem periodic_row_entry {n p : ℕ} [NeZero n] {α : Type*}
    (row : ℕ → Fin n → α)
    (hstep : ∀ i, row (i + p) = cyclicRightShift p (row i))
    (q a : ℕ) (j : Fin n) :
    row (p * q + a) j = row a (j - Fin.ofNat n (p * q)) := by
  rw [periodic_row_block row hstep q a]
  exact cyclicRightShift_apply_sub (row a) (p * q) j

/-- Natural addition is compatible with casting into the cyclic index type. -/
private theorem finOfNat_add {n : ℕ} [NeZero n] (a b : ℕ) :
    Fin.ofNat n (a + b) = Fin.ofNat n a + Fin.ofNat n b := by
  ext
  simp [Fin.ofNat, Fin.add_def, Nat.add_mod]

private theorem finOfNat_sub {n : ℕ} [NeZero n] (a b : ℕ) (h : b ≤ a) :
    Fin.ofNat n (a - b) = Fin.ofNat n a - Fin.ofNat n b := by
  apply (add_right_cancel (b := Fin.ofNat n b))
  rw [← finOfNat_add, Nat.sub_add_cancel h, sub_add_cancel]

private theorem finOfNat_period {n : ℕ} [NeZero n] (a : ℕ) :
    Fin.ofNat n (n + a) = Fin.ofNat n a := by
  ext
  simp [Fin.ofNat]

/-- Removing an earlier block gives an ordinary forward offset. -/
private theorem block_forward {n p : ℕ} [NeZero n]
    (q r b : ℕ) (hqr : q ≤ r) (j : Fin n) (hj : j.val = p * r + b) :
    j - Fin.ofNat n (p * q) = Fin.ofNat n (p * (r - q) + b) := by
  have hcast : j = Fin.ofNat n (p * r + b) := by
    apply Fin.ext
    simp [Fin.ofNat, ← hj, Nat.mod_eq_of_lt j.isLt]
  have hmul : p * (r - q) = p * r - p * q := Nat.mul_sub_left_distrib p r q
  have hnat : p * r + b = p * q + (p * (r - q) + b) := by
    have hle : p * q ≤ p * r := Nat.mul_le_mul_left p hqr
    omega
  rw [hcast, hnat, finOfNat_add]
  abel

/-- Removing a later block wraps once around the cyclic index set. -/
private theorem block_backward {n p : ℕ} [NeZero n]
    (q r a : ℕ) (hqr : q ≤ r) (hle : p * (r - q) ≤ n + a)
    (i : Fin n) (hi : i.val = p * q + a) :
    i - Fin.ofNat n (p * r) = Fin.ofNat n (n + a - p * (r - q)) := by
  have hcast : i = Fin.ofNat n (p * q + a) := by
    apply Fin.ext
    simp [Fin.ofNat, ← hi, Nat.mod_eq_of_lt i.isLt]
  have hmul : p * (r - q) = p * r - p * q := Nat.mul_sub_left_distrib p r q
  have hnat : p * r = p * q + p * (r - q) := by
    have hle' : p * q ≤ p * r := Nat.mul_le_mul_left p hqr
    omega
  rw [hcast, hnat, finOfNat_add, finOfNat_add]
  rw [finOfNat_sub _ _ hle, finOfNat_period]
  abel

/-- A periodically generated matrix is skew once the seed block and every
nonzero block separation have the required sign reversal. -/
private theorem periodic_pair_of_le {n p : ℕ} [NeZero n] (hp : 0 < p)
    (row : ℕ → Fin n → ℂ)
    (hstep : ∀ i, row (i + p) = cyclicRightShift p (row i))
    (hbase : ∀ a b, a < p → b < p →
      row a (Fin.ofNat n b) = -row b (Fin.ofNat n a))
    (hcross : ∀ a b d, a < p → b < p → 0 < d → p * d < n →
      row a (Fin.ofNat n (p * d + b)) =
        -row b (Fin.ofNat n (n + a - p * d)))
    (i j : Fin n) (hij : i ≤ j) :
    row i.val j = -row j.val i := by
  let q := i.val / p
  let r := j.val / p
  let a := i.val % p
  let b := j.val % p
  have ha : a < p := Nat.mod_lt _ hp
  have hb : b < p := Nat.mod_lt _ hp
  have hi : i.val = p * q + a := by
    simpa [q, a, Nat.add_comm] using (Nat.mod_add_div i.val p).symm
  have hj : j.val = p * r + b := by
    simpa [r, b, Nat.add_comm] using (Nat.mod_add_div j.val p).symm
  have hqr : q ≤ r := Nat.div_le_div_right hij
  by_cases heq : q = r
  · rw [← heq] at hj
    have hleft : row i.val j = row a (Fin.ofNat n b) := by
      rw [hi, periodic_row_entry row hstep q a j]
      simpa using congrArg (row a) (block_forward q q b le_rfl j hj)
    have hright : row j.val i = row b (Fin.ofNat n a) := by
      rw [hj, periodic_row_entry row hstep q b i]
      simpa using congrArg (row b) (block_forward q q a le_rfl i hi)
    rw [hleft, hright]
    exact hbase a b ha hb
  · have hlt : q < r := lt_of_le_of_ne hqr heq
    let d := r - q
    have hd : 0 < d := by dsimp [d]; omega
    have hpd : p * d < n := by
      have hle : p * d ≤ p * r := Nat.mul_le_mul_left p (Nat.sub_le r q)
      have hpr : p * r ≤ j.val := by rw [hj]; omega
      exact lt_of_le_of_lt (hle.trans hpr) j.isLt
    have hback : p * d ≤ n + a := by omega
    have hleft : row i.val j = row a (Fin.ofNat n (p * d + b)) := by
      rw [hi, periodic_row_entry row hstep q a j]
      exact congrArg (row a) (block_forward q r b hqr j hj)
    have hright : row j.val i = row b (Fin.ofNat n (n + a - p * d)) := by
      rw [hj, periodic_row_entry row hstep r b i]
      exact congrArg (row b) (block_backward q r a hqr hback i hi)
    rw [hleft, hright]
    exact hcross a b d ha hb hd hpd

private theorem periodic_matrix_skew {n p : ℕ} [NeZero n] (hp : 0 < p)
    (row : ℕ → Fin n → ℂ)
    (hstep : ∀ i, row (i + p) = cyclicRightShift p (row i))
    (hbase : ∀ a b, a < p → b < p →
      row a (Fin.ofNat n b) = -row b (Fin.ofNat n a))
    (hcross : ∀ a b d, a < p → b < p → 0 < d → p * d < n →
      row a (Fin.ofNat n (p * d + b)) =
        -row b (Fin.ofNat n (n + a - p * d))) :
    IsSkewSymmetric (fun i : Fin n => row i.val) := by
  apply Matrix.ext
  intro i j
  change row j.val i = -row i.val j
  by_cases hji : j ≤ i
  · exact periodic_pair_of_le hp row hstep hbase hcross j i hji
  · have hij : i ≤ j := le_of_lt (lt_of_not_ge hji)
    have h := periodic_pair_of_le hp row hstep hbase hcross i j hij
    linear_combination h

/-- The two Y seed rows form a skew block at separation zero. -/
private theorem y_seed_base (k : ℕ) [NeZero (2 * (2 * k + 1))]
    (a b : ℕ) (ha : a < 2) (hb : b < 2) :
    yRow k a (Fin.ofNat (2 * (2 * k + 1)) b) =
      -yRow k b (Fin.ofNat (2 * (2 * k + 1)) a) := by
  have hn : 2 ≤ 2 * (2 * k + 1) := by omega
  interval_cases a <;> interval_cases b <;>
    norm_num [yRow, yRow0, yRow1, Fin.ofNat, Nat.mod_eq_of_lt (by omega : 1 < 2 * (2 * k + 1))]

/-- Opposite Y seed entries at a nonzero two-row block separation. -/
private theorem y_seed_cross (k : ℕ) [NeZero (2 * (2 * k + 1))] (a b d : ℕ)
    (ha : a < 2) (hb : b < 2) (hd : 0 < d)
    (hpd : 2 * d < 2 * (2 * k + 1)) :
    yRow k a (Fin.ofNat (2 * (2 * k + 1)) (2 * d + b)) =
      -yRow k b (Fin.ofNat (2 * (2 * k + 1))
        (2 * (2 * k + 1) + a - 2 * d)) := by
  have hx : 2 * d + b < 2 * (2 * k + 1) := by omega
  have hy : 2 * (2 * k + 1) + a - 2 * d < 2 * (2 * k + 1) := by omega
  have hxval : (Fin.ofNat (2 * (2 * k + 1)) (2 * d + b)).val = 2 * d + b := by
    simp [Fin.ofNat, Nat.mod_eq_of_lt hx]
  have hyval :
      (Fin.ofNat (2 * (2 * k + 1)) (2 * (2 * k + 1) + a - 2 * d)).val =
        2 * (2 * k + 1) + a - 2 * d := by
    simp [Fin.ofNat, Nat.mod_eq_of_lt hy]
  interval_cases a <;> interval_cases b <;>
    simp only [yRow, yRow0, yRow1] <;>
    rw [hxval, hyval] <;>
    split_ifs <;> (try contradiction) <;> (try omega) <;> norm_num

/-- The Y-family is skew-symmetric for every natural parameter, including zero. -/
theorem yMatrix_skewSymmetric (k : ℕ) :
    IsSkewSymmetric (yMatrix k) := by
  haveI : NeZero (2 * (2 * k + 1)) := ⟨by omega⟩
  exact periodic_matrix_skew (by omega : 0 < 2) (yRow k)
    (yRow_add_two k) (y_seed_base k) (y_seed_cross k)

/-- At `k ≥ 1`, the five Z seeds form a skew initial block. -/
private theorem z_seed_base (k : ℕ) [NeZero (5 * (2 * k + 1))]
    (hk : 1 ≤ k) (a b : ℕ) (ha : a < 5) (hb : b < 5) :
    zRow k a (Fin.ofNat (5 * (2 * k + 1)) b) =
      -zRow k b (Fin.ofNat (5 * (2 * k + 1)) a) := by
  have hn : 5 ≤ 5 * (2 * k + 1) := by omega
  have hhalf : (5 * (2 * k + 1) - 1) / 2 = 5 * k + 2 := by omega
  have hav : (Fin.ofNat (5 * (2 * k + 1)) a).val = a := by
    simp [Fin.ofNat, Nat.mod_eq_of_lt (by omega : a < 5 * (2 * k + 1))]
  have hbv : (Fin.ofNat (5 * (2 * k + 1)) b).val = b := by
    simp [Fin.ofNat, Nat.mod_eq_of_lt (by omega : b < 5 * (2 * k + 1))]
  interval_cases a <;> interval_cases b <;>
    simp only [zRow, zRow0, zRow1, zRow2, zRow3, zRow4] <;>
    simp only [hav, hbv] <;>
    simp only [hhalf] <;>
    split_ifs <;> (try contradiction) <;> (try omega) <;> norm_num

/-- The five Z seeds have three cutoff positions beyond their special first block. -/
private def zSeedCutoff (k a : ℕ) : ℕ :=
  if a < 2 then 5 * k + 3 else if a = 2 then 5 * k + 5 else 5 * k + 7

private theorem zRow_large (k a : ℕ) (ha : a < 5)
    (j : Fin (5 * (2 * k + 1))) (hj : 5 ≤ j.val) :
    zRow k a j = if j.val < zSeedCutoff k a then 1 else -1 := by
  have hhalf : (5 * (2 * k + 1) - 1) / 2 = 5 * k + 2 := by omega
  have h0 : j.val ≠ 0 := by omega
  have h1 : j.val ≠ 1 := by omega
  have h2 : j.val ≠ 2 := by omega
  have h3 : j.val ≠ 3 := by omega
  have h4 : j.val ≠ 4 := by omega
  interval_cases a <;>
    simp only [zRow_zero, zRow_one, zRow_two, zRow_three, zRow_four,
      zRow0, zRow1, zRow2, zRow3, zRow4,
      zSeedCutoff, hhalf, h0, h1, h2, h3, h4] <;>
    split_ifs <;> (try omega) <;> norm_num <;> contradiction

/-- Beyond the initial block, Z seed entries reverse sign across complementary
five-row block separations. -/
private theorem z_seed_cross (k : ℕ) [NeZero (5 * (2 * k + 1))]
    (a b d : ℕ) (ha : a < 5) (hb : b < 5)
    (hd : 0 < d) (hpd : 5 * d < 5 * (2 * k + 1)) :
    zRow k a (Fin.ofNat (5 * (2 * k + 1)) (5 * d + b)) =
      -zRow k b (Fin.ofNat (5 * (2 * k + 1))
        (5 * (2 * k + 1) + a - 5 * d)) := by
  have hx : 5 * d + b < 5 * (2 * k + 1) := by omega
  have hy : 5 * (2 * k + 1) + a - 5 * d < 5 * (2 * k + 1) := by omega
  have hxval : (Fin.ofNat (5 * (2 * k + 1)) (5 * d + b)).val = 5 * d + b := by
    simp [Fin.ofNat, Nat.mod_eq_of_lt hx]
  have hyval :
      (Fin.ofNat (5 * (2 * k + 1)) (5 * (2 * k + 1) + a - 5 * d)).val =
        5 * (2 * k + 1) + a - 5 * d := by
    simp [Fin.ofNat, Nat.mod_eq_of_lt hy]
  have hxl : 5 ≤ (Fin.ofNat (5 * (2 * k + 1)) (5 * d + b)).val := by
    rw [hxval]
    omega
  have hyl :
      5 ≤ (Fin.ofNat (5 * (2 * k + 1))
        (5 * (2 * k + 1) + a - 5 * d)).val := by
    rw [hyval]
    omega
  have hcuts :
      (5 * d + b < zSeedCutoff k a) ↔
        ¬(5 * (2 * k + 1) + a - 5 * d < zSeedCutoff k b) := by
    interval_cases a <;> interval_cases b <;>
      simp [zSeedCutoff] <;> omega
  rw [zRow_large k a ha _ hxl, zRow_large k b hb _ hyl, hxval, hyval]
  by_cases hpos : 5 * d + b < zSeedCutoff k a
  · have hneg := hcuts.mp hpos
    simp [hpos, hneg]
  · have hneg : 5 * (2 * k + 1) + a - 5 * d < zSeedCutoff k b := by
      by_contra hh
      exact hpos (hcuts.mpr hh)
    simp [hpos, hneg]

/-- The Z-family is skew-symmetric on its source parameter range `k ≥ 1`. -/
theorem zMatrix_skewSymmetric (k : ℕ) (hk : 1 ≤ k) :
    IsSkewSymmetric (zMatrix k) := by
  haveI : NeZero (5 * (2 * k + 1)) := ⟨by omega⟩
  exact periodic_matrix_skew (by omega : 0 < 5) (zRow k)
    (zRow_add_five k) (z_seed_base k hk) (z_seed_cross k)

/-- The total extension at `k = 0` fails at entry `(0,4)`. -/
theorem zMatrix_zero_not_skewSymmetric : ¬ IsSkewSymmetric (zMatrix 0) := by
  intro h
  have hentry := congrFun (congrFun h 0) 4
  norm_num [IsSkewSymmetric, Matrix.transpose_apply, zMatrix,
    zRow, zRow0, zRow4] at hentry

end SkewMatrixGraph
