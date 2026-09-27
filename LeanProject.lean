import Mathlib
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import LeanProject.Families

-- Suppose B is an n × n matrix of rational numbers
variable {n : Type*} (B : n → n → ℚ)

--Definition: B is skew-symmetric
def SkewSymmetric : Prop:= ∀ i j, B i j = -B j i


-- Lemma statement
theorem ratio_neg_of_triangle_cond
  (h_skew : SkewSymmetric B)
  (i j1 j2 : n)
  (hc_nonneg : c ≥ 0)
  (hd_nonneg : d ≥ 0)
  (h_neq1 : B i j1 ≠ 0)
  (h_neq2 : B i j2 ≠ 0)
  (eq1 : B j1 j2 - B i j2 = (c : ℚ) * B i j1)
  (eq2 : -B j1 j2 - B i j1 = (d : ℚ) * B i j2) :
  (B i j1) / (B i j2) < 0 := by

--Step 1: state the definition of i-j1, and take k=j2
  sorry
