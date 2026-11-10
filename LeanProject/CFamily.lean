import LeanProject.Families

/-! Compatibility definitions for the original C-family module. -/

namespace SkewMatrixGraph

def cyclicShift {n : ℕ} (m : ℕ) (r : Fin n → ℂ) : Fin n → ℂ :=
  cyclicRightShift m r

def bitValue (b : Bool) : ℕ :=
  if b then 1 else 0

end SkewMatrixGraph
