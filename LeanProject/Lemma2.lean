import Mathlib
import LeanProject.SkewMatrixGraph

namespace SkewMatrixGraph

variable {n : ℕ}

theorem lemma2
  (B : Matrix (Fin n) (Fin n) ℂ)
  (hB : IsSkewSymmetric B)
  (i j₁ j₂ j₃ : Fin n)
  (hj12 : j₁ ≠ j₂)
  (hj23 : j₂ ≠ j₃)
  (hj13 : j₁ ≠ j₃)
  (h₁ : IsSmoothableEdge B i j₁)
  (h₂ : IsSmoothableEdge B i j₂)
  (h₃ : IsSmoothableEdge B i j₃) :
  False := by
  rcases lemma1 B hB i j₁ j₂ hj12 h₁ h₂ with ⟨q₁, hq₁_neg, hB12⟩
  rcases lemma1 B hB i j₂ j₃ hj23 h₂ h₃ with ⟨q₂, hq₂_neg, hB23⟩
  rcases lemma1 B hB i j₁ j₃ hj13 h₁ h₃ with ⟨q₃, hq₃_neg, hB13⟩
  have hB_nz : B i j₃ ≠ 0 := h₃.2.1
  have h_comb : (q₃ : ℂ) * B i j₃ = ((q₁ * q₂ : ℚ) : ℂ) * B i j₃ := by
    calc
      (q₃ : ℂ) * B i j₃ = B i j₁ := hB13.symm
      _= (q₁ : ℂ) * B i j₂ := hB12
      _= (q₁ : ℂ) * ((q₂ : ℂ)* B i j₃) := by rw [hB23]
      _= ((q₁ * q₂ : ℚ) : ℂ ) * B i j₃ := by push_cast ; ring
  have hq_eq_complex : (q₃ : ℂ) = ((q₁ * q₂ : ℚ) : ℂ) :=
    mul_right_cancel₀ hB_nz h_comb
  have hq_eq : q₃ = q₁ * q₂ := by
    exact_mod_cast hq_eq_complex
  have h_prod_pos : 0 < q₁ * q₂ :=               mul_pos_of_neg_of_neg hq₁_neg hq₂_neg
  have hq₃_pos : 0 < q₃ := by
    rwa [hq_eq]
  exact  lt_asymm hq₃_neg hq₃_pos
end SkewMatrixGraph
