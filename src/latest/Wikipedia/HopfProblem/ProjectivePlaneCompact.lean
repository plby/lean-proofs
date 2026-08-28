import Wikipedia.HopfProblem.ProjectivePlane
import Mathlib.Analysis.Normed.Module.RCLike.Basic

/-!
# Compactness of the complex projective plane

Every complex line in `ℂ³` has a unit representative.  Restricting the
canonical scalar-quotient map to the compact unit sphere therefore gives
a continuous surjection onto the complex projective plane.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.ProjectivePlane

/-- The unit sphere in the standard finite-product norm on `ℂ³`. -/
abbrev UnitSphere := Metric.sphere (0 : Homogeneous) 1

/-- Unit homogeneous vectors are nonzero homogeneous vectors. -/
def unitSphereToNonzero (v : UnitSphere) : NonzeroVector :=
  ⟨v.1, Metric.ne_of_mem_sphere v.2 one_ne_zero⟩

theorem unitSphereToNonzero_continuous : Continuous unitSphereToNonzero :=
  continuous_subtype_val.subtype_mk _

/-- Sending a unit vector to the complex line it spans. -/
def unitSphereMap : UnitSphere → Space := quotientMap ∘ unitSphereToNonzero

theorem unitSphereMap_continuous : Continuous unitSphereMap :=
  quotientMap_continuous.comp unitSphereToNonzero_continuous

/-- Every projective point admits a unit homogeneous representative. -/
theorem unitSphereMap_surjective : Function.Surjective unitSphereMap := by
  intro q
  obtain ⟨v, rfl⟩ := quotientMap_surjective q
  let w : UnitSphere :=
    ⟨(‖(v : Homogeneous)‖⁻¹ : ℂ) • (v : Homogeneous),
      mem_sphere_zero_iff_norm.mpr (norm_smul_inv_norm v.2)⟩
  refine ⟨w, ?_⟩
  apply (quotientMap_eq_iff_scalar (unitSphereToNonzero w) v).mpr
  exact ⟨(‖(v : Homogeneous)‖⁻¹ : ℂ), rfl⟩

/-- The scalar-quotient topology makes the complex projective plane compact. -/
instance spaceCompactSpace : CompactSpace Space :=
  unitSphereMap_surjective.compactSpace unitSphereMap_continuous

end Wikipedia.HopfProblem.ProjectivePlane
