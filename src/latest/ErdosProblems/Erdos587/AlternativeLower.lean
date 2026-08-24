import ErdosProblems.Erdos587.FiberIntegral
import ErdosProblems.Erdos587.CompleteRootDensity

/-! Quantitative alternative-main lower bounds from complete-root density. -/

open MeasureTheory
open scoped BigOperators SchwartzMap

namespace Erdos587

lemma sum_complete_roots_Ico (u v t Y M : ℕ) :
    (∑ y ∈ Finset.Ico Y (Y + M), (squareRootCount u (t + v * y) : ℝ)) =
      ∑ i ∈ Finset.range M, (squareRootCount u ((t + v * Y) + v * i) : ℝ) := by
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  apply Finset.sum_congr rfl
  intro i hi
  congr 2
  ring

theorem alternativeMain_lower_of_fiber_integrals (f g : 𝓢(ℝ, ℂ))
    {a u b v H : ℕ} (hu : 0 < u) (hv : 0 < v) (hH : 0 < H)
    (hab : a * u = b * v + 1) (t : ℕ) (Y : Finset ℕ) {L I : ℝ} (hL : 0 < L)
    (hf : ∀ x : ℝ, (f x).im = 0)
    (hfpos : ∀ x : ℝ, 0 ≤ (f x).re) (hgpos : ∀ x : ℝ, 0 ≤ (g x).re)
    (hI : ∀ y ∈ Y, I ≤ ∫ z : ℝ, (f (L⁻¹ * z)).re *
      (g ((z ^ 2 - t - (v : ℝ) * y) / (u * H))).re) :
    (u : ℝ)⁻¹ * I * (∑ y ∈ Y, (squareRootCount u (t + v * y) : ℝ)) ≤
      (alternativeSquareMain f g a u b v t L (((v : ℝ) / H)⁻¹)).re := by
  calc
    _ = (u : ℝ)⁻¹ * ∑ y ∈ Y, (squareRootCount u (t + v * y) : ℝ) * I := by
      rw [← Finset.sum_mul]
      ring
    _ ≤ (u : ℝ)⁻¹ * ∑ y ∈ Y, (squareRootCount u (t + v * y) : ℝ) *
        ∫ z : ℝ, (f (L⁻¹ * z)).re *
          (g ((z ^ 2 - t - (v : ℝ) * y) / (u * H))).re := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg u))
      exact Finset.sum_le_sum (fun y hy =>
        mul_le_mul_of_nonneg_left (hI y hy) (Nat.cast_nonneg _))
    _ ≤ _ := complete_root_integrals_le_alternativeMain f g hu hv hH hab t Y hL hf hfpos hgpos

/-- The constants here are independent of both weights; the weight hypotheses
are the explicit lower bound on every selected fiber. -/
theorem exists_alternativeMain_density_bound :
    ∃ A : ℝ, 0 < A ∧ ∃ C : ℝ, 0 < C ∧ ∃ O : ℕ, 0 < O ∧
      ∀ (f g : 𝓢(ℝ, ℂ)) (a u b v H t Y M : ℕ) (L I : ℝ),
        0 < u → 0 < v → 0 < H → a * u = b * v + 1 → v.Coprime u →
        0 < L → 0 ≤ I → A * Real.sqrt u ≤ M →
        (∀ x : ℝ, (f x).im = 0) →
        (∀ x : ℝ, 0 ≤ (f x).re) → (∀ x : ℝ, 0 ≤ (g x).re) →
        (∀ y ∈ Finset.Ico Y (Y + M), I ≤ ∫ z : ℝ, (f (L⁻¹ * z)).re *
          (g ((z ^ 2 - t - (v : ℝ) * y) / (u * H))).re) →
        I * M / (u * C * (1 + Real.log u) ^ O) ≤
          (alternativeSquareMain f g a u b v t L (((v : ℝ) / H)⁻¹)).re := by
  obtain ⟨A, hA, C, hC, O, hO, hden⟩ := exists_complete_root_density_bound
  refine ⟨A, hA, C, hC, O, hO, ?_⟩
  intro f g a u b v H t Y M L I hu hv hH hab hvu hL hI hM hf hfpos hgpos hfiber
  have hroot := hden u (t + v * Y) v M hu hvu hM
  rw [← sum_complete_roots_Ico] at hroot
  have hmain := alternativeMain_lower_of_fiber_integrals f g hu hv hH hab t
    (Finset.Ico Y (Y + M)) hL hf hfpos hgpos hfiber
  calc
    _ = ((u : ℝ)⁻¹ * I) * ((M : ℝ) / (C * (1 + Real.log u) ^ O)) := by ring
    _ ≤ ((u : ℝ)⁻¹ * I) * ∑ y ∈ Finset.Ico Y (Y + M),
        (squareRootCount u (t + v * y) : ℝ) :=
      mul_le_mul_of_nonneg_left hroot (mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg u)) hI)
    _ ≤ _ := hmain

end Erdos587
