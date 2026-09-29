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

example (h : ∀ a, ∃ x, f x ≥ a) : ¬ FnHasUb f := by
    intro h'
    rcases h' with ⟨a, ubf⟩
    rcases h (a+1) with ⟨x , hx⟩
    have : f x ≤ a := ubf x
    linarith
--   have ll : a+1 ≤ f x := hx
--    have kk : f x ≤ a := ubf x
--    have imp : a+1 ≤ a := le_trans ll kk
--    apply lt_irrefl a
--    linarith


example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
    intro a
    by_contra h'
    apply h
    use a
    show FnUb f a
    intro x
    by_contra h''
    have h''_str : f x > a := lt_of_not_ge h''
    exact h' ⟨x, h''_str⟩

example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
--    dsimp only [FnHasUb, FnUb] at h
 --   push_neg at h
 --   exact h
    dsimp only [FnHasUb, FnUb] at h
    contrapose! h
    exact h
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

end SquareSum

namespace negation
variable {α : Type*} [LinearOrder α]
example {a b : α} (h : a < b) : ¬ b < a := by
    intro (h' : b < a)
    have : a < a := lt_trans h h'
    apply lt_irrefl a
    exact this

end negation

namespace prop
variable {α : Type*} (P : α → Prop) (Q : Prop)

example (h : ¬ ∃ x , P x) : ∀ x , ¬ P x := by
    intro x
    by_contra h'
    exact h ⟨x, h'⟩

--    intro x
--    intro hP
--    have h_ex : ∃ x , P x := ⟨x, hP⟩
--    exact h h_ex
example (h : ∀ x, ¬ P x) : ¬ ∃ x , P x := by
    by_contra h'
    rcases h' with ⟨x, h'' ⟩
    have hP_neg : ¬ P x := h x
    exact hP_neg h''
--   intro h'
--    rcases h' with ⟨x , h'P⟩
--    have h_neg : ¬ P x := h x
--    exact h_neg h'P


example (h :¬ ∀ x,  P x) :  ∃ x ,¬ P x := by
    by_contra h'
    apply h
    intro x
    show P x
    by_contra h''
    have h'_neg : ∃ x , ¬ P x := ⟨x, h''⟩
    exact h' h'_neg





example (h : ∃ x,¬ P x) : ¬ ∀  x , P x := by
    by_contra h'
    rcases h with ⟨x, h_neg⟩
    have : P x := h' x
    exact h_neg this
--    intro h'
--    rcases h with ⟨x, hP_neg⟩
 --   have hP : P x := h' x
 --   exact hP_neg hP
end prop


namespace Chapter_3_4
example {x y : ℝ} (h_0 : x ≤ y) (h_1 : ¬ y ≤ x) : x ≤ y ∧ x ≠ y :=
    have h : x ≠ y := by
        contrapose! h_1
        rw [h_1]
    ⟨h_0, h⟩
    --    constructor
 --   · assumption
  --  intro h
   -- apply h_1
--    rw[h]

example {x y : ℝ} : x ≤ y ∧  x ≠ y → ¬ y ≤ x := by
    rintro ⟨h_0, h_1⟩ h'
    exact h_1 (le_antisymm h_0 h')

example {x y : ℝ} (h : x ≤ y) : ¬ y ≤ x ↔ x ≠ y := by
    constructor
    · contrapose!
      rintro rfl
      rfl
    contrapose!
    apply le_antisymm h

variable {α : Type*} [PartialOrder α]
variable (a b : α)

example : a < b ↔ a ≤ b ∧ a ≠ b := by
    rw [lt_iff_le_not_ge]
    constructor
    rintro ⟨h₀,h₁⟩
    constructor
    assumption
    intro h_eq
    subst h_eq
    exact h₁ (le_refl a)
    rintro ⟨ h₂,h₃⟩
    constructor
    assumption
    intro h₄
    exact h₃ (le_antisymm h₂ h₄)


end Chapter_3_4

namespace Chapter_3_5

example (P : Prop) : ¬¬P → P := by
    intro h
    cases em P
    · assumption
    · contradiction


example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
    constructor
    intro h
    by_cases hP : P
    · right
      exact h hP
    · left
      exact hP
    intro h
    intro hP
    rcases h with h1 | h2
    exfalso
    exact h1 hP
    exact h2




end Chapter_3_5

namespace Chapter_4_2
variable { α β : Type*}
variable {f : α → β}
variable (s t : Set α)
variable (u v : Set β)

#check α 

end Chapter_4_2
