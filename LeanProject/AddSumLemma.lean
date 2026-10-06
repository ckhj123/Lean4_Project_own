import Mathlib
import LeanProject.Families
open SkewMatrixGraph
open BigOperators

#print ValidC
#print cyclicRightShift
#check cMatrix
#print cMatrix
#check cFirstRow_Z
#print cMatrix_Z
#print SkewMatrixGraph.cFirstRow_Z



--Recall
/--
def cFirstRow_Z (n k : ℕ) : Fin n → ℤ :=
  fun j =>
    if j.val = 0 then 0
    else if j.val ≤ k then 1
    else if n - k ≤ j.val then -1
    else 0

Also define the Family C in ℤ to print the result

def cMatrix_Z (n k : ℕ) : Matrix (Fin n) (Fin n) ℤ  :=
  fun i => cyclicRightShift i.val (cFirstRow_Z n k)

def cMatrix_Z (n k : ℕ) : Matrix (Fin n) (Fin n) ℤ  :=
  fun i => cyclicRightShift i.val (cFirstRow_Z n k)

-/






def rowSumC {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) (i : Fin n) : ℂ :=
  ∑ j : Fin n, A i j


def rowSumZ {n : ℕ} (A : Matrix (Fin n) (Fin n) ℤ) (i : Fin n) : ℤ  :=
  ∑ j : Fin n, A i j

#eval rowSumZ (cMatrix_Z 5 1) 1



def AllRowSum_Z (B : Matrix (Fin n) (Fin n) ℤ) : Prop :=
  ∀ i : Fin n, rowSumZ B i = 0


lemma Sum_cyclic_0 (k : ℕ) (v : Fin n → ℤ) (hv : ∑ j : Fin n, v j = 0) :
  ∑ j : Fin n, cyclicRightShift k v j = 0 := by
  dsimp [cyclicRightShift]
  change (∑ j : Fin n, v (((finRotate n).symm ^ k) j)) = 0
  calc
    _ = ∑ j : Fin n, v j :=
      Equiv.sum_comp ((finRotate n).symm ^ k) v
    _ = 0 := hv


theorem cFirstRow_Z_sum_zero (n k : ℕ) (hk : 2 * k < n) :
    ∑ j : Fin n, cFirstRow_Z n k j = 0 := by
  sorry


theorem cMatrix_Z_all_row_sums_zero (n k : ℕ) (hk : 2 * k < n) :
    AllRowSum_Z (cMatrix_Z n k) := by
  intro i
  dsimp [AllRowSum_Z, rowSumZ, cMatrix_Z]
  exact Sum_cyclic_0 i.val _ (cFirstRow_Z_sum_zero n k hk)
