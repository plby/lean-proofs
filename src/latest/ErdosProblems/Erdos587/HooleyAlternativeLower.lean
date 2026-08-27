import ErdosProblems.Erdos587.AlternativeLower
import ErdosProblems.Erdos587.HooleyCompleteRootDensity

/-! # Alternative-main lower bounds with one log-log loss -/

open MeasureTheory
open scoped BigOperators SchwartzMap

namespace Erdos587

theorem exists_delta_alternativeMain_density :
    ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, 0 < C ∧
      ∀ (f g : 𝓢(ℝ, ℂ)) (a u b v H t Y M : ℕ) (L I : ℝ),
        0 < u → 0 < v → 0 < H → a * u = b * v + 1 → v.Coprime u →
        0 < L → 0 ≤ I → A * Real.sqrt u ≤ M →
        (∀ x : ℝ, (f x).im = 0) →
        (∀ x : ℝ, 0 ≤ (f x).re) → (∀ x : ℝ, 0 ≤ (g x).re) →
        (∀ y ∈ Finset.Ico Y (Y + M), I ≤ ∫ z : ℝ, (f (L⁻¹ * z)).re *
          (g ((z ^ 2 - t - (v : ℝ) * y) / (u * H))).re) →
        I * M / (u * C * max 1 (Real.log (Real.log (u : ℝ)))) ≤
          (alternativeSquareMain f g a u b v t L (((v : ℝ) / H)⁻¹)).re := by
  obtain ⟨A, hA, C, hC, hden⟩ := exists_delta_complete_root_density
  refine ⟨A, hA, C, hC, ?_⟩
  intro f g a u b v H t Y M L I hu hv hH hab hvu hL hI hM hf hfpos hgpos hfiber
  have hroot := hden u (t + v * Y) v M u hu hvu hM le_rfl
  rw [← sum_complete_roots_Ico] at hroot
  have hmain := alternativeMain_lower_of_fiber_integrals f g hu hv hH hab t
    (Finset.Ico Y (Y + M)) hL hf hfpos hgpos hfiber
  calc
    _ = ((u : ℝ)⁻¹ * I) * ((M : ℝ) / (C * max 1 (Real.log (Real.log (u : ℝ))))) := by ring
    _ ≤ ((u : ℝ)⁻¹ * I) * ∑ y ∈ Finset.Ico Y (Y + M),
        (squareRootCount u (t + v * y) : ℝ) :=
      mul_le_mul_of_nonneg_left hroot (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg u)) hI)
    _ ≤ _ := hmain

end Erdos587
