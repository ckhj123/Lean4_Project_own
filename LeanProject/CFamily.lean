import LeanProject.SkewMatrixGraph

/-!
Define C-family
-/

namespace SkewMatrixGraph

def ValidC (n k : ℕ) : Prop :=
  1 ≤ k ∧ 3 ≤ n ∧ 2 * k < n

def cFirstRow (n k : ℕ) : Fin n → ℂ :=
  fun j =>
    if j.val = 0 then
      0
    else if j.val ≤ k then
      1
    else if n - k ≤ j.val then
      -1
    else
      0

def cyclicShift {n : ℕ}
    (m : ℕ) (r : Fin n → ℂ) : Fin n → ℂ :=
  fun j =>
    r (((fun x => (finRotate n).symm x)^[m]) j)
/-ready-made commands to implement the function of shifting backward-/

def cMatrix (n k : ℕ) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    cyclicShift i.val (cFirstRow n k) j

def bitValue (b : Bool) : ℕ :=
  if b then 1 else 0
/-implement true/false to 1/0-/
def cMatrixI
    (n k : ℕ)
    (hd : 0 < Nat.gcd n k)
    (I : Fin (Nat.gcd n k) → Bool) :
    Matrix (Fin n) (Fin n) ℂ :=
  fun i j =>
    let d := Nat.gcd n k
    let idx : Fin d :=
      ⟨i.val % d, Nat.mod_lt _ hd⟩
    let ε : ℕ := bitValue (I idx)
    cyclicShift i.val (cFirstRow n (k - ε)) j

/-
Let d=gcd(n,k). The sequence I has length d, so for the
i-th row we first take idx = i mod d, which extends I periodically
to all rows. bitValue (I idx) converts the Boolean entry of I into ε ∈ {0,1}.

The i-th row is then obtained by taking the basic row r(k - ε) and
cyclically shifting it to the right by i positions. Thus

row_i(C_{n,k,I}) = T^i r(k - I_{i mod d}).

The argument hd : 0 < gcd(n,k) is to justify that
i mod d is a valid element of fin d.
-/

end SkewMatrixGraph
