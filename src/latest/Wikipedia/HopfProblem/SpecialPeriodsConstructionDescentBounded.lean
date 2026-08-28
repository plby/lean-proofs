import Wikipedia.HopfProblem.SpecialPeriodsConstructionDescent
import Mathlib.Topology.Order.Compact

/-!
# Global bounds from the actual triangle cusp

The complement of a cusp image in the actual triangle orbit quotient is
compact.  A continuous function bounded above on that cusp image is
therefore bounded above everywhere.  Applying this to the actual descent
of an invariant function yields a global bound from an eventual upper
bound high in the original upper half-plane.  No limit at the cusp, or
continuity at the added compactification point, is required.
-/

noncomputable section

open Set Filter Topology UpperHalfPlane

namespace Wikipedia.HopfProblem.SpecialPeriods.Construction

/-- A continuous real function on the actual triangle orbit space has a
global upper bound as soon as it is bounded above on one cusp image. -/
theorem orbit_bddAbove_range_of_cusp_le (F : TriangleOrbitSpace → ℝ)
    (hF : Continuous F) (Y C : ℝ)
    (hbound : ∀ q ∈ Triangle.cuspImage Y, F q ≤ C) : BddAbove (range F) := by
  obtain ⟨B, hB⟩ := (Triangle.cuspImage_compl_compact Y).bddAbove_image hF.continuousOn
  refine ⟨max B C, ?_⟩
  rintro _ ⟨q, rfl⟩
  by_cases hq : q ∈ Triangle.cuspImage Y
  · exact (hbound q hq).trans (le_max_right B C)
  · exact (hB (mem_image_of_mem F hq)).trans (le_max_left B C)

/-- An explicit height cutoff suffices for a global upper bound on a
continuous function invariant under the actual triangle group action. -/
theorem bddAbove_range_of_triangle_invariant_le_of_im_gt (f : ℍ → ℝ)
    (hf : Continuous f)
    (hinv : ∀ (g : TriangleGroup) (z : ℍ),
      f (triangleGeometricRepresentation g z) = f z)
    (Y C : ℝ) (hbound : ∀ z : ℍ, Y < z.im → f z ≤ C) : BddAbove (range f) := by
  have hdesc : BddAbove (range (orbitDescend f hinv)) := by
    apply orbit_bddAbove_range_of_cusp_le (orbitDescend f hinv)
      (orbitDescend_continuous f hinv hf) Y C
    intro q hq
    obtain ⟨z, hz, rfl⟩ := (Triangle.mem_cuspImage Y q).mp hq
    rw [orbitDescend_projection]
    exact hbound z hz
  apply hdesc.mono
  rintro _ ⟨z, rfl⟩
  exact ⟨triangleOrbitProjection z, orbitDescend_projection f hinv z⟩

/-- Every continuous triangle-invariant real function which is eventually
bounded above at the upper-half-plane cusp is globally bounded above. -/
theorem bddAbove_range_of_triangle_invariant_eventually_le (f : ℍ → ℝ)
    (hf : Continuous f)
    (hinv : ∀ (g : TriangleGroup) (z : ℍ),
      f (triangleGeometricRepresentation g z) = f z)
    (hbound : ∃ C : ℝ, ∀ᶠ z in atImInfty, f z ≤ C) : BddAbove (range f) := by
  obtain ⟨C, hC⟩ := hbound
  obtain ⟨Y, hY⟩ := (UpperHalfPlane.atImInfty_mem _).mp hC
  exact bddAbove_range_of_triangle_invariant_le_of_im_gt f hf hinv Y C
    (fun z hz => hY z hz.le)

end Wikipedia.HopfProblem.SpecialPeriods.Construction
