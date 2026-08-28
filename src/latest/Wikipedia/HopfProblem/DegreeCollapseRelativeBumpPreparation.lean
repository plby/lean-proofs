import Wikipedia.HopfProblem.DegreeCollapseSinglePassageClassAddition
import Wikipedia.SmoothSixDPoincare.GlobalAmbientTransversality
import Wikipedia.SmoothSixDPoincare.SupportedRelativeIsotopy

/-!
# Retain the whole relative isotopy of a small ambient bump

The native bump construction already fixes the complement of its actual
chart support at every real time. Retain that family and its exact endpoint,
so relative general position can preserve the other attaching spheres
throughout preparation, not just at the terminal diffeomorphism.
-/

noncomputable section

open Set Function
open scoped ContDiff Manifold Topology
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

variable {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace H] {J : ModelWithCorners ℝ F H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

theorem exists_radius_supported_bump_preparation
    (Φ : PartialDiffeomorph 𝓘(ℝ, E) J E M ∞) {β : E → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcompact : HasCompactSupport β)
    (hsupport : tsupport β ⊆ Φ.source) {C : Set M}
    (hC : ∀ y ∈ C, y ∉ Φ '' tsupport β) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ a : E, ‖a‖ < ε →
      ∀ e : Diffeomorph J J M M ∞, (∀ y, e y = bumpFamily Φ β (a, y)) →
        Nonempty (SupportedRelativeIsotopy e (Φ '' tsupport β) C) := by
  obtain ⟨ε, hε, hsmall⟩ := exists_small_supported_bump_isotopy Φ hβ hcompact hsupport
  refine ⟨ε, hε, ?_⟩
  intro a ha e he
  obtain ⟨A, hA, hzero, hdiff, hfix, hterminal⟩ := hsmall a ha
  have hone : ∀ y, A (1, y) = e y := by
    intro y
    rw [he]
    by_cases hy : y ∈ Φ.target
    · have hh := hterminal (Φ.symm y) (Φ.map_target' hy)
      have hpoint : Φ (Φ.symm y) = y := Φ.right_inv' hy
      rw [hpoint] at hh
      change A (1, y) = extendMap Φ (fun x => x + β x • a) y
      rw [extendMap_of_mem Φ _ hy]
      exact hh
    · have hnot : y ∉ Φ '' tsupport β := by
        rintro ⟨x, hx, rfl⟩
        exact hy (Φ.map_source' (hsupport hx))
      rw [hfix 1 y hnot, bumpFamily_fixed_outside Φ β a hnot]
  refine ⟨{
    family := A
    smooth := hA
    zero := hzero
    one := hone
    slices := ?_
    fixedOutside := hfix
    fixedOn := fun t y hy => hfix t y (hC y hy) }⟩
  intro t
  obtain ⟨d, hd⟩ := hdiff t
  exact ⟨d, fun y => (hd y).symm⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
