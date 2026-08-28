import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicFibres
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldMeromorphicFibreConstancy
import Wikipedia.HopfProblem.HolomorphicMeromorphicAdmissiblePullbackValues

/-!
# Constant native torus restrictions give genuine constant fibres

Admissible restriction supplies an ambient-regular point of the actual
fibre and preserves every ambient-regular value. Thus a native constant
meromorphic section on the original period torus gives the genuine
fibre-constancy predicate used by the regular-cover descent argument.
-/

open Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicFibres

open HolomorphicForms.RegularCover HolomorphicMeromorphic

local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

/-- The admissibility proved outside the countable exceptional set gives
an actual ambient-regular point on the literal sphere fibre. -/
theorem exists_regular_point_on_fibre (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (z : TriangleRegularPoint) (hz : regularSphereValue z ∉ exceptionalValues g) :
    ∃ x : Threefold.Space, projectionSphere x = regularSphereValue z ∧
      RegularAt IF Threefold.Space g ⟨x, by trivial⟩ := by
  obtain ⟨t, ht⟩ := exists_regular_image_of_admissible_pullback I₂ IF
    (regularTorusInclusionMap z) g (regularTorus_admissible g z hz) ⟨0, by trivial⟩
  exact ⟨regularTorusInclusion z t.val, projectionSphere_regularTorusInclusion z t.val, ht⟩

/-- At every ambient-regular point of the original torus inclusion,
the actual restriction has exactly the original ordinary value. -/
theorem regularTorusRestriction_value_of_regularAt
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (z : TriangleRegularPoint) (hz : regularSphereValue z ∉ exceptionalValues g)
    (t : RegularTorus z)
    (ht : RegularAt IF Threefold.Space g ⟨regularTorusInclusion z t, by trivial⟩) :
    value I₂ (RegularTorus z) (regularTorusRestriction g z hz) ⟨t, by trivial⟩ =
      value IF Threefold.Space g ⟨regularTorusInclusion z t, by trivial⟩ :=
  value_admissiblePullbackSection_of_regularAt I₂ IF (regularTorusInclusionMap z) g
    (regularTorus_admissible g z hz) ⟨t, by trivial⟩ ht

/-- Equality of the genuine torus restriction with a native complex
constant implies constancy at all ambient-regular points of the entire
literal fibre, and includes existence of an ambient-regular fibre point. -/
theorem constantOnFibre_of_regularTorusRestriction_eq
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (z : TriangleRegularPoint) (hz : regularSphereValue z ∉ exceptionalValues g)
    (c : ℂ) (hconst : regularTorusRestriction g z hz =
      algebraMap ℂ (HolomorphicMeromorphic.Function I₂ (RegularTorus z)) c) :
    MeromorphicRegularCover.ConstantOnFibre g (regularSphereValue z) := by
  refine ⟨c, exists_regular_point_on_fibre g z hz, ?_⟩
  intro x hxb hxg
  have hxrange : x ∈ range (regularTorusInclusion z) := by
    rw [regularTorusInclusion_range]
    exact hxb
  obtain ⟨t, rfl⟩ := hxrange
  have hc : value I₂ (RegularTorus z) (regularTorusRestriction g z hz) ⟨t, by trivial⟩ = c := by
    rw [hconst, algebraMap_section, value_ofHolomorphic]
    rfl
  exact (regularTorusRestriction_value_of_regularAt g z hz t hxg).symm.trans hc

/-- The same conclusion as membership in the actual regular sphere-value
set used by the uncountable-fibre descent theorem. -/
theorem mem_constantRegularFibres_of_regularTorusRestriction_eq
    (g : HolomorphicMeromorphic.Function IF Threefold.Space)
    (z : TriangleRegularPoint) (hz : regularSphereValue z ∉ exceptionalValues g)
    (c : ℂ) (hconst : regularTorusRestriction g z hz =
      algebraMap ℂ (HolomorphicMeromorphic.Function I₂ (RegularTorus z)) c) :
    regularSphereValue z ∈ MeromorphicRegularCover.constantRegularFibres g := by
  refine ⟨?_, constantOnFibre_of_regularTorusRestriction_eq g z hz c hconst⟩
  rw [← sourceBase_eq_regularSphereValue z]
  exact MeromorphicRegularCover.sourceBase_mem_sphereRegularPatch z

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.MeromorphicFibres
