import Wikipedia.HopfProblem.ToricComponentTopology
import Mathlib.Geometry.Manifold.Immersion

/-!+# The ray surfaces are embedded complex hypersurfaces

In the already constructed source and target charts, inclusion of a ray
surface inserts a zero coordinate. This gives the local normal form required
by Mathlib's immersion definition, not merely injectivity of a differential.
-/

noncomputable section

open Set Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.ToricComponent

open ToricCharts ToricSpace

def coordinateJoinLinear (j : Fin 3) :
    (CoordinateSpace 2 × ℂ) ≃ₗ[ℂ] CoordinateSpace 3 :=
  { (Equiv.prodComm (CoordinateSpace 2) ℂ).trans
      (Fin.insertNthEquiv (fun _ : Fin 3 => ℂ) j) with
    map_add' := by
      intro z w
      ext k
      obtain rfl | ⟨l, rfl⟩ := Fin.eq_self_or_eq_succAbove j k <;>
        simp [Fin.insertNthEquiv]
    map_smul' := by
      intro a z
      ext k
      obtain rfl | ⟨l, rfl⟩ := Fin.eq_self_or_eq_succAbove j k <;>
        simp [Fin.insertNthEquiv] }

def coordinateJoin (j : Fin 3) : (CoordinateSpace 2 × ℂ) ≃L[ℂ] CoordinateSpace 3 :=
  (coordinateJoinLinear j).toContinuousLinearEquiv

@[simp] theorem coordinateJoin_apply_zero (j : Fin 3) (z : CoordinateSpace 2) :
    coordinateJoin j (z, 0) = insertZero j z := rfl

theorem inclusion_isImmersionOfComplement (v : Fin 2 → ℤ) :
    Manifold.IsImmersionOfComplement ℂ (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (Subtype.val : rayDivisor v → Space) := by
  intro x
  let c := preferredIndex v x
  refine Manifold.IsImmersionAtOfComplement.mk_of_continuousAt
    continuous_subtype_val.continuousAt (coordinateJoin c.coordinate)
    (parametrization c).symm (ToricSpace.parametrization c.triangle).symm
    ?_ ?_ ?_ ?_ ?_
  · change x ∈ (parametrization c).target
    rw [parametrization_target]
    exact preferred_mem v x
  · change (x : Space) ∈ (ToricSpace.parametrization c.triangle).target
    rw [ToricSpace.parametrization_target]
    exact (affineInclusion_mem_range_iff c x).mp (preferred_mem v x)
  · exact IsManifold.subset_maximalAtlas (mem_range_self c)
  · exact IsManifold.subset_maximalAtlas (mem_range_self c.triangle)
  · intro z _
    change (ToricSpace.parametrization c.triangle).symm
      (inclusion c.triangle (insertZero c.coordinate z)) = insertZero c.coordinate z
    exact (ToricSpace.parametrization c.triangle).left_inv (mem_univ _)

theorem inclusion_isImmersion (v : Fin 2 → ℤ) :
    Manifold.IsImmersion (modelWithCornersSelf ℂ (CoordinateSpace 2))
      (modelWithCornersSelf ℂ (CoordinateSpace 3)) ω (Subtype.val : rayDivisor v → Space) :=
  (inclusion_isImmersionOfComplement v).isImmersion

end Wikipedia.HopfProblem.ToricComponent
