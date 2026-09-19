import Mathlib

namespace MyRing

variable {R : Type*} [Ring R]
theorem zero_mul (a : R) : 0 * a = 0 := by
    have h : 0 * a + 0 * a = 0 * a + 0 := by
        rw [← add_mul 0 0 a]
        rw [add_zero]
        rw[ add_zero]
    rw [add_left_cancel h]
end MyRing



example (a b c d e : ℝ) (h₀ : a ≤ b) (h₁ : b ≤ c) (h₂ : c ≤ d) (h₃ : d ≤ e) : a ≤ e := by
    linarith

#check ∀ x y ε : ℝ , 0 < ε → ε  ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

namespace Hello

def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
    ∀ x , f x ≤ a

def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
    ∀ x , a ≤ f x

example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
    intro x
    dsimp
    apply add_le_add
    · apply hfa
    · apply hgb


def Monotone (f : ℝ → ℝ) (a b : ℝ) : Prop :=
    a ≤ b →  f a ≤ f b
example (f : ℝ → ℝ) {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
    intro a b aleb
    dsimp
    apply mul_le_mul_of_nonneg_left
    · apply mf aleb
    · apply nnc
