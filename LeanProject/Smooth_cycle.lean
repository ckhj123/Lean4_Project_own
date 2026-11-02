import Mathlib

import LeanProject.SkewMatrixGraph
import LeanProject.Families

/-!-/
namespace SkewMatrixGraph

theorem IsSmoothableEdge_equiv {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ)
    (e : Fin n ≃ Fin n) (hB : ∀ i j, B (e i) (e j) = B i j) (i j : Fin n) :
    IsSmoothableEdge B (e i) (e j) ↔ IsSmoothableEdge B i j := by
  unfold IsSmoothableEdge
  -- Simplifies the bijection inequalities and the base matrix entry
  simp only [e.injective.ne_iff, hB, ne_eq]
  -- We now just need to show the `∀ k` condition is invariant
  apply and_congr_right'
  apply and_congr_right'
  constructor
  · intro h k hki hkj
    -- To prove for `k`, apply the hypothesis to `e k`
    have hki_e : e k ≠ e i := fun hc => hki (e.injective hc)
    have hkj_e : e k ≠ e j := fun hc => hkj (e.injective hc)
    obtain ⟨m, hm⟩ := h (e k) hki_e hkj_e
    rw [hB, hB] at hm
    exact ⟨m, hm⟩
  · intro h k hki hkj
    -- To prove for `k` in the shifted context, pull back using `e.symm k`
    have hki_symm : e.symm k ≠ i := by intro contra; apply hki; rw [← contra, e.apply_symm_apply]
    have hkj_symm : e.symm k ≠ j := by intro contra; apply hkj; rw [← contra, e.apply_symm_apply]
    obtain ⟨m, hm⟩ := h (e.symm k) hki_symm hkj_symm
    use m
    -- Push `e` back onto the indices to match `hB`
    have e_symm_j : B (e j) k = B j (e.symm k) := by
      have := hB j (e.symm k); rwa [e.apply_symm_apply] at this
    have e_symm_i : B k (e i) = B (e.symm k) i := by
      have := hB (e.symm k) i; rwa [e.apply_symm_apply] at this
    rw [e_symm_j, e_symm_i]
    exact hm



/-- Helper definition for cyclic shifts as an Equiv. -/
def cyclicShiftEquiv {n : ℕ} (d : ℕ) : Fin n ≃ Fin n :=
  (finRotate n).symm ^ d


/-- Theorem stating that if a matrix is formed by shifting rows by d,
    the smoothable edge condition commutes with a step of d. -/
theorem IsSmoothableEdge_cyclic_shift {n : ℕ} (B : Matrix (Fin n) (Fin n) ℂ) (d : ℕ)
  (h_circ : ∀ i j, B (cyclicShiftEquiv d i) (cyclicShiftEquiv d j) = B i j) (i j : Fin n) :
  IsSmoothableEdge B (cyclicShiftEquiv d i) (cyclicShiftEquiv d j) ↔ IsSmoothableEdge B i j :=
IsSmoothableEdge_equiv B (cyclicShiftEquiv d) h_circ i j

theorem cMatrix_shift_invariant (n k : ℕ) (i j : Fin n) :
    cMatrix n k (cyclicShiftEquiv 1 i) (cyclicShiftEquiv 1 j) = cMatrix n k i j := by
    sorry


theorem IsSmoothableEdge_cMatrix_shift (n k : ℕ) (i j : Fin n) :
    IsSmoothableEdge (cMatrix n k) (cyclicShiftEquiv 1 i) (cyclicShiftEquiv 1 j) ↔
    IsSmoothableEdge (cMatrix n k) i j := by
  apply IsSmoothableEdge_cyclic_shift
  exact cMatrix_shift_invariant n k

theorem cMatrix_base_edge (n k : ℕ) (h_valid : ValidC n k) :
    IsSmoothableEdge (cMatrix n k) 0 1 := by
  unfold IsSmoothableEdge
  sorry

theorem cMatrix_all_edges (n k : ℕ) (h_valid : ValidC n k) (i : Fin n) :
    IsSmoothableEdge (cMatrix n k) i (i + 1) := by
    sorry
end SkewMatrixGraph
