import Mathlib

namespace SkewMatrixGraph

variable {n : ℕ}

def IsSkewSymmetric
    (B : Matrix (Fin n) (Fin n) ℂ) : Prop :=
  B.transpose = -B

def IsSmoothableEdge
    (B : Matrix (Fin n) (Fin n) ℂ)
    (i j : Fin n) : Prop :=
  i ≠ j ∧
  B i j ≠ 0 ∧
  ∀ k : Fin n, k ≠ i → k ≠ j →
    ∃ m : ℕ, B j k + B k i = (m : ℂ) * B i j

theorem lemma1
    (B : Matrix (Fin n) (Fin n) ℂ)
    (hB : IsSkewSymmetric B)
    (i j₁ j₂ : Fin n)
    (hj : j₁ ≠ j₂)
    (h₁ : IsSmoothableEdge B i j₁)
    (h₂ : IsSmoothableEdge B i j₂) :
    ∃ q : ℚ, q < 0 ∧ B i j₁ = (q : ℂ) * B i j₂ := by
  rcases h₁ with ⟨hi₁, hne₁, hcol₁⟩
  rcases h₂ with ⟨hi₂, hne₂, hcol₂⟩

  rcases hcol₁ j₂ (Ne.symm hi₂) (Ne.symm hj) with ⟨a, ha⟩
  rcases hcol₂ j₁ (Ne.symm hi₁) hj with ⟨b, hb⟩

  have hBT : B.transpose = -B := by
   simpa [IsSkewSymmetric] using hB

  have hskew (r c : Fin n) : B c r = -B r c := by
   have h := congrFun (congrFun hBT r) c
   simpa using h

  have ha' :
      B j₁ j₂ - B i j₂ = (a : ℂ) * B i j₁ := by
    rw [hskew i j₂] at ha
    simpa [sub_eq_add_neg] using ha

  have hb' :
      -B j₁ j₂ - B i j₁ = (b : ℂ) * B i j₂ := by
    rw [hskew j₁ j₂, hskew i j₁] at hb
    simpa [sub_eq_add_neg] using hb

  have hrel :
    ((a : ℂ) + 1) * B i j₁ +
    ((b : ℂ) + 1) * B i j₂ = 0 := by
    linear_combination -ha' - hb'

  refine ⟨-(((b : ℚ) + 1) / ((a : ℚ) + 1)), ?_, ?_⟩
  · have hqpos :
        0 < (((b : ℚ) + 1) / ((a : ℚ) + 1)) := by
      positivity
    exact neg_lt_zero.mpr hqpos
  · push_cast
    have hden : (a : ℂ) + 1 ≠ 0 := by
     exact_mod_cast Nat.succ_ne_zero a
    field_simp [hden]
    linear_combination hrel

end SkewMatrixGraph
