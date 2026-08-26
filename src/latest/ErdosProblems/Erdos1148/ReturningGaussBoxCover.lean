import ErdosProblems.Erdos1148.ReturningGaussLiftCover

/-! # An exp(S/2) cover of returning Gauss parameters by measurable forward boxes -/

namespace Erdos1148.DukeArithmetic

open MeasureTheory
open scoped MatrixGroups

noncomputable def modularReturningGaussRegion (g : SL(2, ℝ)) (S c : ℝ) : Set ModularOrbitSpace :=
  (fun p : BoundedGaussParameters => modularMk (gaussParameterFrame g p)) ''
    ReturningGaussParameters g S c

theorem exists_returningGauss_forward_cover {A c δ : ℝ} (hA : 0 ≤ A) (hc : 0 < c) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (g : SL(2, ℝ)), (∀ i j : Fin 2, |g i j| ≤ A) →
      ∀ S : ℝ, 0 ≤ S → 96 * Real.exp (-S) ≤ c →
        ∃ (N : ℕ) (B : Fin N → Set ModularOrbitSpace),
          (N : ℝ) ≤ K * Real.exp (S / 2) ∧ (∀ i, MeasurableSet (B i)) ∧
          modularReturningGaussRegion g S c ⊆ ⋃ i, B i ∧
          ∀ i, B i ×ˢ B i ⊆ modularForwardBowenPairs (8 * δ) S := by
  obtain ⟨K, hK, hcover⟩ := exists_returningGauss_lift_cover hA hc hδ
  refine ⟨K, hK, ?_⟩
  intro g hg S hS hsmall
  obtain ⟨N, B, hN, hcompact, hcov, hclose⟩ := hcover g hg S hS hsmall
  refine ⟨N, fun i => modularMk '' B i, hN, ?_, ?_, ?_⟩
  · intro i
    exact ((hcompact i).image continuous_modularMk).measurableSet
  · rintro x ⟨p, hp, rfl⟩
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcov ⟨p, hp, rfl⟩)
    exact Set.mem_iUnion.mpr ⟨i, gaussParameterFrame g p, hi, rfl⟩
  · intro i
    exact (hclose i).modular_image hS

end Erdos1148.DukeArithmetic
