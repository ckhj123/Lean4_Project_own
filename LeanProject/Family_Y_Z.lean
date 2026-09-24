import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic

namespace Family_C_n_k
variable {n : ℕ}

def T (r : Fin n → ℤ) : Fin n → ℤ :=
  fun i => r (i - 1)

def Rec_T (r0 : Fin n → ℤ) : ℕ → (Fin n → ℤ)
  | 0 => r0
  | k+1 => T (Rec_T r0 k)


end Family_C_n_k
