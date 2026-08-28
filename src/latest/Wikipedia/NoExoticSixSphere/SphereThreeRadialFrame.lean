import Wikipedia.NoExoticSixSphere.SphereThreeTangentFrame
import Wikipedia.NoExoticSixSphere.ComplementaryOperatorCoordinates

/-!
# The fixed tangent frame and radial direction give sphere-dependent coordinates

These genuine linear equivalences are defined on the three-sphere and have
continuous inverses there. No extension over the four-ball is asserted.
The radial direction is placed after the three tangent coordinates.
-/

noncomputable section

namespace NoExoticSixSphere.SphereThreeTangentFrame

open GLOrthonormalization Function

def radialOperator (s : Sphere 3) : Vector 1 →L[ℝ] Vector 4 :=
  ((ContinuousLinearMap.id ℝ ℝ).smulRight s.val).comp
    EuclideanTailCoordinates.scalar.symm.toContinuousLinearMap

theorem radialOperator_apply (s : Sphere 3) (v : Vector 1) :
    radialOperator s v = EuclideanTailCoordinates.scalar.symm v • s.val := rfl

theorem radialOperator_injective (s : Sphere 3) : Injective (radialOperator s) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro v hv
  have he : EuclideanTailCoordinates.scalar.symm v = 0 :=
    (smul_eq_zero.mp hv).resolve_right (ne_zero_of_mem_unit_sphere s)
  apply EuclideanTailCoordinates.scalar.symm.injective
  simpa only [map_zero] using he

theorem radialOperator_range (s : Sphere 3) : (radialOperator s).range = ℝ ∙ s.val := by
  apply le_antisymm
  · rintro _ ⟨v, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self s.val)
  · intro v hv
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hv
    refine ⟨EuclideanTailCoordinates.scalar t, ?_⟩
    change radialOperator s (EuclideanTailCoordinates.scalar t) = t • s.val
    rw [radialOperator_apply, LinearIsometryEquiv.symm_apply_apply]

theorem continuous_radialOperator : Continuous radialOperator := by
  apply continuous_clm_apply.mpr
  intro v
  exact continuous_const.smul continuous_subtype_val

theorem tangent_radial_disjoint (s : Sphere 3) :
    Disjoint (operator s.val).range (radialOperator s).range := by
  rw [range_operator, radialOperator_range]
  exact (ℝ ∙ s.val).orthogonal_disjoint.symm

def radialCoordinates (s : Sphere 3) : Vector 4 ≃L[ℝ] Vector 4 :=
  OperatorSum.coordinates (operator s.val) (radialOperator s)
    (Stiefel.injective (frame s)) (radialOperator_injective s) (tangent_radial_disjoint s) rfl

theorem radialCoordinates_apply (s : Sphere 3) (v : Vector 4) :
    radialCoordinates s v = operator s.val (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).1 +
      EuclideanTailCoordinates.scalar.symm
        (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) v).2 • s.val := rfl

theorem radialCoordinates_tangent (s : Sphere 3) (v : Vector 3) :
    radialCoordinates s (EuclideanSpace.finAddEquivProd (n := 3) (m := 1) |>.symm (v, 0)) =
      operator s.val v := by
  rw [radialCoordinates_apply, ContinuousLinearEquiv.apply_symm_apply,
    map_zero, zero_smul, add_zero]

theorem radialCoordinates_radial (s : Sphere 3) (t : ℝ) :
    radialCoordinates s ((EuclideanSpace.finAddEquivProd (n := 3) (m := 1)).symm
      (0, EuclideanTailCoordinates.scalar t)) = t • s.val := by
  rw [radialCoordinates_apply, ContinuousLinearEquiv.apply_symm_apply,
    map_zero, zero_add, LinearIsometryEquiv.symm_apply_apply]

theorem continuous_radialCoordinates :
    Continuous (fun s ↦ (radialCoordinates s).toContinuousLinearMap) :=
  OperatorSum.continuous_operator _ _
    (continuous_subtype_val.comp continuous_frame) continuous_radialOperator

theorem continuous_inverse_radialCoordinates :
    Continuous (fun s ↦ (radialCoordinates s).symm.toContinuousLinearMap) :=
  OperatorSum.continuous_inverse_coordinates _ _
    (continuous_subtype_val.comp continuous_frame) continuous_radialOperator
    (fun s ↦ Stiefel.injective (frame s)) radialOperator_injective tangent_radial_disjoint rfl

end NoExoticSixSphere.SphereThreeTangentFrame
