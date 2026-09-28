import LeanProject.SkewMatrixGraph
/-!
# Classification families

Rows use Fin n → α; matrices use Mathlib's Matrix.
cyclicRightShift m is T^m, where T sends the entry at column j to
column j + 1 (modulo n). All five classification components C, X₄, X₅, Y, Z expose matrices over ℂ.

The source formulas are preserved for every natural parameter, including
parameters outside ValidC. These definitions alone do not assert
skew-symmetry or smoothability.
-/

namespace SkewMatrixGraph

/-- T^m: cyclic right shift by m positions, for any row length and coefficient type.
The inverse rotation acts on column indices. This also works for the empty row. -/
def cyclicRightShift {n : ℕ} {α : Type*}
    (m : ℕ) (r : Fin n → α) : Fin n → α :=
  fun j => r (((finRotate n).symm^[m]) j)

@[simp]
theorem cyclicRightShift_zero {n : ℕ} {α : Type*} (r : Fin n → α) :
    cyclicRightShift 0 r = r := rfl

/-- The entry at column j is read from column j - 1: this is a RIGHT shift. -/
theorem cyclicRightShift_one_apply {n : ℕ} [NeZero n] {α : Type*}
    (r : Fin n → α) (j : Fin n) :
    cyclicRightShift 1 r j = r (j - 1) := by
  simp only [cyclicRightShift, Function.iterate_one, finRotate_symm_apply]

/-- Successive right shifts compose by adding their shift counts. -/
theorem cyclicRightShift_add {n : ℕ} {α : Type*}
    (a b : ℕ) (r : Fin n → α) :
    cyclicRightShift (a + b) r = cyclicRightShift b (cyclicRightShift a r) := by
  funext j
  simp only [cyclicRightShift, Function.iterate_add_apply]


/-- Parameter range from the C-family source; it is not imposed on the raw definitions. -/
def ValidC (n k : ℕ) : Prop :=
  1 ≤ k ∧ 3 ≤ n ∧ 2 * k < n

/-- The C seed row r(k), with the source's ordered case distinction. -/
def cFirstRow (n k : ℕ) : Fin n → ℂ :=
  fun j =>
    if j.val = 0 then 0
    else if j.val ≤ k then 1
    else if n - k ≤ j.val then -1
    else 0

/-- The unmodified circulant C matrix: row i is T^i r(k). -/
def cMatrix (n k : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i => cyclicRightShift i.val (cFirstRow n k)

/-Define the C row in ℤ to print result-/
def cFirstRow_Z (n k : ℕ) : Fin n → ℤ :=
  fun j =>
    if j.val = 0 then 0
    else if j.val ≤ k then 1
    else if n - k ≤ j.val then -1
    else 0

/-Also define the Family C in ℤ to print the result-/
def cMatrix_Z (n k : ℕ) : Matrix (Fin n) (Fin n) ℤ  :=
  fun i => cyclicRightShift i.val (cFirstRow n k)

#eval (cMatrix_Z 5 1)

/-- C_{n,k,I}: row i is T^i r(k - I_{i mod gcd(n,k)}).
Boolean entries are converted using Bool.toNat; subtraction is in ℕ.
The positivity witness is only needed to construct the periodic index. -/
def cMatrixI (n k : ℕ) (hd : 0 < Nat.gcd n k)
    (I : Fin (Nat.gcd n k) → Bool) : Matrix (Fin n) (Fin n) ℂ :=
  fun i =>
    let idx : Fin (Nat.gcd n k) := ⟨i.val % Nat.gcd n k, Nat.mod_lt _ hd⟩
    cyclicRightShift i.val (cFirstRow n (k - (I idx).toNat))

/-Also construct the C_i family in ℤ in order to visualize the result-/
def cMatrixI_Z (n k : ℕ) (hd : 0 < Nat.gcd n k)
    (I : Fin (Nat.gcd n k) → Bool) : Matrix (Fin n) (Fin n) ℤ :=
  fun i =>
    let idx : Fin (Nat.gcd n k) := ⟨i.val % Nat.gcd n k, Nat.mod_lt _ hd⟩
    cyclicRightShift i.val (cFirstRow_Z n (k - (I idx).toNat))

#eval cMatrixI_Z 9 3 {0 0 1}

/-- The exceptional X₄ matrix, with indices 0,1,2,3 in the displayed source order.
Source: Matviichuk, arXiv:2310.05284v1, Example 2.1.
https://arxiv.org/html/2310.05284v1 -/
def x4Matrix : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 2, -1, -1;
     -2, 0, 3, -1;
     1, -3, 0, 2;
     1, 1, -2, 0]

/-- The exceptional X₅ matrix, with indices 0,1,2,3,4 in the displayed source order.
Source: Matviichuk, Elliptic log symplectic brackets on projective bundles, §3.1.
https://doi.org/10.1007/s00029-024-01014-5 -/
def x5Matrix : Matrix (Fin 5) (Fin 5) ℂ :=
  !![0, 1, 1, -1, -1;
     -1, 0, 2, 0, -1;
     -1, -2, 0, 2, 1;
     1, 0, -2, 0, 1;
     1, 1, -1, -1, 0]

/-- Y seed row r₀, embedded from the original integer entries into ℂ. -/
def yRow0 (k : ℕ) : Fin (2 * (2 * k + 1)) → ℂ :=
  fun j =>
    let n := 2 * (2 * k + 1)
    if j.val = 0 then 0
    else if j.val = 1 then 2
    else if j.val < n / 2 then 1
    else -1

/-- Y seed row r₁; in particular, the source cutoff is N / 2 + 2. -/
def yRow1 (k : ℕ) : Fin (2 * (2 * k + 1)) → ℂ :=
  fun j =>
    let n := 2 * (2 * k + 1)
    if j.val = 0 then -2
    else if j.val = 1 then 0
    else if j.val < n / 2 + 2 then 1
    else -1

/-- Y rows, retaining r₀ = Row0, r₁ = Row1, r_{i+2} = T² r_i. -/
def yRow (k : ℕ) : ℕ → Fin (2 * (2 * k + 1)) → ℂ
  | 0 => yRow0 k
  | 1 => yRow1 k
  | i + 2 => cyclicRightShift 2 (yRow k i)

@[simp]
theorem yRow_zero (k : ℕ) : yRow k 0 = yRow0 k := rfl

@[simp]
theorem yRow_one (k : ℕ) : yRow k 1 = yRow1 k := rfl

theorem yRow_add_two (k i : ℕ) :
    yRow k (i + 2) = cyclicRightShift 2 (yRow k i) := rfl

/-- The Y-family Mathlib matrix over ℂ, of dimension N = 2(2k+1). -/
def yMatrix (k : ℕ) :
    Matrix (Fin (2 * (2 * k + 1))) (Fin (2 * (2 * k + 1))) ℂ :=
  fun i => yRow k i.val








/-Below is the ℤ Version for Family Y-/

/-- Y seed row r₀, embedded from the original integer entries into ℂ. -/
def yRow0_Z (k : ℕ) : Fin (2 * (2 * k + 1)) → ℤ  :=
  fun j =>
    let n := 2 * (2 * k + 1)
    if j.val = 0 then 0
    else if j.val = 1 then 2
    else if j.val < n / 2 then 1
    else -1

/-- Y seed row r₁; in particular, the source cutoff is N / 2 + 2. -/
def yRow1_Z (k : ℕ) : Fin (2 * (2 * k + 1)) → ℤ  :=
  fun j =>
    let n := 2 * (2 * k + 1)
    if j.val = 0 then -2
    else if j.val = 1 then 0
    else if j.val < n / 2 + 2 then 1
    else -1

/-- Y rows, retaining r₀ = Row0, r₁ = Row1, r_{i+2} = T² r_i. -/
def yRow_Z (k : ℕ) : ℕ → Fin (2 * (2 * k + 1)) → ℤ
  | 0 => yRow0_Z k
  | 1 => yRow1_Z k
  | i + 2 => cyclicRightShift 2 (yRow_Z k i)

@[simp]
theorem yRow_zero_Z (k : ℕ) : yRow_Z k 0 = yRow0_Z k := rfl

@[simp]
theorem yRow_one_Z (k : ℕ) : yRow_Z k 1 = yRow1_Z k := rfl

theorem yRow_add_two_Z (k i : ℕ) :
    yRow_Z k (i + 2) = cyclicRightShift 2 (yRow_Z k i) := rfl

/-- The Y-family in ℤ Mathlib matrix over ℂ, of dimension N = 2(2k+1). -/
def yMatrix_Z (k : ℕ) :
    Matrix (Fin (2 * (2 * k + 1))) (Fin (2 * (2 * k + 1))) ℤ :=
  fun i => yRow_Z k i.val

#eval (yMatrix_Z 1)












/-- Z seed row r₀, preserving the source cutoff (N - 1) / 2 + 1. -/
def zRow0 (k : ℕ) : Fin (5 * (2 * k + 1)) → ℂ :=
  fun j =>
    let n := 5 * (2 * k + 1)
    if j.val = 0 then 0
    else if j.val < (n - 1) / 2 + 1 then 1
    else -1

/-- Z seed row r₁, including the two exceptional entries equal to 2. -/
def zRow1 (k : ℕ) : Fin (5 * (2 * k + 1)) → ℂ :=
  fun j =>
    let n := 5 * (2 * k + 1)
    if j.val = 0 then -1
    else if j.val = 1 then 0
    else if j.val = 2 then 2
    else if j.val = 3 then 2
    else if j.val < (n - 1) / 2 + 1 then 1
    else -1

/-- Z seed row r₂, with source cutoff (N - 1) / 2 + 3. -/
def zRow2 (k : ℕ) : Fin (5 * (2 * k + 1)) → ℂ :=
  fun j =>
    let n := 5 * (2 * k + 1)
    if j.val = 0 then -1
    else if j.val = 1 then -2
    else if j.val = 2 then 0
    else if j.val = 3 then 2
    else if j.val < (n - 1) / 2 + 3 then 1
    else -1

/-- Z seed row r₃, with source cutoff (N - 1) / 2 + 5. -/
def zRow3 (k : ℕ) : Fin (5 * (2 * k + 1)) → ℂ :=
  fun j =>
    let n := 5 * (2 * k + 1)
    if j.val = 0 then -1
    else if j.val = 1 then -2
    else if j.val = 2 then -2
    else if j.val = 3 then 0
    else if j.val < (n - 1) / 2 + 5 then 1
    else -1

/-- Z seed row r₄. The first four -1 entries take precedence over the cutoff. -/
def zRow4 (k : ℕ) : Fin (5 * (2 * k + 1)) → ℂ :=
  fun j =>
    let n := 5 * (2 * k + 1)
    if j.val = 0 then -1
    else if j.val = 1 then -1
    else if j.val = 2 then -1
    else if j.val = 3 then -1
    else if j.val = 4 then 0
    else if j.val < (n - 1) / 2 + 5 then 1
    else -1

/-- Z rows retain all five source seeds and r_{i+5} = T⁵ r_i.
The source parameter domain is all ℕ, including k = 0. -/
def zRow (k : ℕ) : ℕ → Fin (5 * (2 * k + 1)) → ℂ
  | 0 => zRow0 k
  | 1 => zRow1 k
  | 2 => zRow2 k
  | 3 => zRow3 k
  | 4 => zRow4 k
  | i + 5 => cyclicRightShift 5 (zRow k i)

@[simp]
theorem zRow_zero (k : ℕ) : zRow k 0 = zRow0 k := rfl

@[simp]
theorem zRow_one (k : ℕ) : zRow k 1 = zRow1 k := rfl

@[simp]
theorem zRow_two (k : ℕ) : zRow k 2 = zRow2 k := rfl

@[simp]
theorem zRow_three (k : ℕ) : zRow k 3 = zRow3 k := rfl

@[simp]
theorem zRow_four (k : ℕ) : zRow k 4 = zRow4 k := rfl

theorem zRow_add_five (k i : ℕ) :
    zRow k (i + 5) = cyclicRightShift 5 (zRow k i) := rfl

/-- The Z-family Mathlib matrix over ℂ, of dimension N = 5(2k+1). -/
def zMatrix (k : ℕ) :
    Matrix (Fin (5 * (2 * k + 1))) (Fin (5 * (2 * k + 1))) ℂ :=
  fun i => zRow k i.val



/-Below is the Z family in ℤ -/


/-- Z seed row r₀, preserving the source cutoff (N - 1) / 2 + 1. -/
def zRow0_Z (k : ℕ) : Fin (5 * (2 * k + 1)) → ℤ  :=
  fun j =>
    let n := 5 * (2 * k + 1)
    if j.val = 0 then 0
    else if j.val < (n - 1) / 2 + 1 then 1
    else -1

/-- Z seed row r₁, including the two exceptional entries equal to 2. -/
def zRow1_Z (k : ℕ) : Fin (5 * (2 * k + 1)) → ℤ  :=
  fun j =>
    let n := 5 * (2 * k + 1)
    if j.val = 0 then -1
    else if j.val = 1 then 0
    else if j.val = 2 then 2
    else if j.val = 3 then 2
    else if j.val < (n - 1) / 2 + 1 then 1
    else -1

/-- Z seed row r₂, with source cutoff (N - 1) / 2 + 3. -/
def zRow2_Z (k : ℕ) : Fin (5 * (2 * k + 1)) → ℤ :=
  fun j =>
    let n := 5 * (2 * k + 1)
    if j.val = 0 then -1
    else if j.val = 1 then -2
    else if j.val = 2 then 0
    else if j.val = 3 then 2
    else if j.val < (n - 1) / 2 + 3 then 1
    else -1

/-- Z seed row r₃, with source cutoff (N - 1) / 2 + 5. -/
def zRow3_Z (k : ℕ) : Fin (5 * (2 * k + 1)) → ℤ  :=
  fun j =>
    let n := 5 * (2 * k + 1)
    if j.val = 0 then -1
    else if j.val = 1 then -2
    else if j.val = 2 then -2
    else if j.val = 3 then 0
    else if j.val < (n - 1) / 2 + 5 then 1
    else -1

/-- Z seed row r₄. The first four -1 entries take precedence over the cutoff. -/
def zRow4_Z (k : ℕ) : Fin (5 * (2 * k + 1)) → ℤ  :=
  fun j =>
    let n := 5 * (2 * k + 1)
    if j.val = 0 then -1
    else if j.val = 1 then -1
    else if j.val = 2 then -1
    else if j.val = 3 then -1
    else if j.val = 4 then 0
    else if j.val < (n - 1) / 2 + 5 then 1
    else -1

/-- Z rows retain all five source seeds and r_{i+5} = T⁵ r_i.
The source parameter domain is all ℕ, including k = 0. -/
def zRow_Z (k : ℕ) : ℕ → Fin (5 * (2 * k + 1)) → ℤ
  | 0 => zRow0_Z k
  | 1 => zRow1_Z k
  | 2 => zRow2_Z k
  | 3 => zRow3_Z k
  | 4 => zRow4_Z k
  | i + 5 => cyclicRightShift 5 (zRow_Z k i)

@[simp]
theorem zRow_zero_Z (k : ℕ) : zRow_Z k 0 = zRow0_Z k := rfl

@[simp]
theorem zRow_one_Z (k : ℕ) : zRow_Z k 1 = zRow1_Z k := rfl

@[simp]
theorem zRow_two_Z (k : ℕ) : zRow_Z k 2 = zRow2_Z k := rfl

@[simp]
theorem zRow_three_Z (k : ℕ) : zRow_Z k 3 = zRow3_Z k := rfl

@[simp]
theorem zRow_four_Z (k : ℕ) : zRow_Z k 4 = zRow4_Z k := rfl

theorem zRow_add_five_Z (k i : ℕ) :
    zRow k_Z (i + 5) = cyclicRightShift 5 (zRow_Z k i) := rfl

/-- The Z-family Mathlib matrix over ℤ , of dimension N = 5(2k+1). -/
def zMatrix_Z (k : ℕ) :
    Matrix (Fin (5 * (2 * k + 1))) (Fin (5 * (2 * k + 1))) ℤ  :=
  fun i => zRow_Z k i.val



#eval (zMatrix_Z 1)

end SkewMatrixGraph
