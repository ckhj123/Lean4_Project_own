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


def Monotone (f : ℝ → ℝ)  : Prop :=
    ∀ {a b : ℝ}, a ≤ b →  f a ≤ f b
example (f : ℝ → ℝ) {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by
    intro a b aleb
    dsimp
    apply mul_le_mul_of_nonneg_left
    · apply mf aleb
    · apply nnc


def Injective {α β : Type*} (f : α → β) : Prop :=
    ∀ {a b : α} , f a = f b → a = b


example {α β γ : Type*} {f : α → β} {g : β → γ} (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
    intro a b h
    dsimp at h
    have h' : f a = f b := injg h
    exact injf h'

def FnHasUb (f : ℝ → ℝ) :=
    ∃ a , FnUb f a

def FnHasLb (f : ℝ → ℝ):=
    ∃ a , FnLb f a

example {f g : ℝ → ℝ} (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
    rcases ubf with ⟨a , ubfa⟩
    rcases ubg with ⟨b , ubgb⟩
    use a+b
    intro x
    dsimp
    apply add_le_add
    · apply ubfa
    · apply ubgb

example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
    rcases ubf with ⟨a , ubfa⟩
    use c*a
    intro x
    dsimp
    apply mul_le_mul_of_nonneg_left
    · apply ubfa
    · apply h

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
    rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
    exact ⟨a+b, by
        intro x
        dsimp
        apply add_le_add
        · apply ubfa
        · apply ubgb⟩

example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
    rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
    use a+b
    intro x
    dsimp
    apply add_le_add
    · apply ubfa
    · apply ubgb



end Hello

example : ∃ x : ℝ , 2 < x ∧ x < 3 :=
    have h1 : 2 < (5/2 : ℝ) := by norm_num
    have h2 : (5/2 : ℝ) < 3 := by norm_num
    ⟨ 5/2 , ⟨h1 , h2⟩⟩

namespace SquareSum

variable {α : Type*} [CommRing α]
def SumSq (x : α) : Prop :=
    ∃ a b , x = a^2 + b^2
theorem SumSq_Mul {x y : α} (sosx : SumSq x) (sosy : SumSq y) : SumSq (x * y) := by
--    obtain ⟨a, b, xeq⟩ := sosx
--    obtain ⟨c, d, yeq⟩ := sosy
--    rw[xeq, yeq]
--    exact ⟨ a * c - b * d , a * d + b * c
--    , by ring⟩
    match sosx, sosy with
    | ⟨a, b, xeq⟩ , ⟨c, d, yeq⟩ =>
    rw [xeq, yeq]
    exact ⟨a * c - b * d , a * d + b * c
    , by ring⟩
