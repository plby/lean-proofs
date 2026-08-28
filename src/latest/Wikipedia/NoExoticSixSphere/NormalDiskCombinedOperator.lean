import Wikipedia.NoExoticSixSphere.NormalDiskObstruction
import Wikipedia.NoExoticSixSphere.ComplementaryOperatorCoordinates
import Wikipedia.NoExoticSixSphere.InjectiveOperatorBlockExtension

/-!
# The actual normal-disk obstruction as a combined boundary operator

Combine the prescribed normal columns with all four actual derivative
columns. A constructed full normal trivialization and the derivative give
coordinates on the entire disk. Exact extension of the combined operator
is therefore equivalent to vanishing of the original normal-disk parity.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.DiskNormal

open GLOrthonormalization DiskBoundary Function
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable (r : ℕ)
  (D : C(Disk (E := Vector 4), Vector 4 →L[ℝ] Vector (r + 9)))
  (hi : ∀ x, Injective (D x))

def fullNormalFrame : C(Disk (E := Vector 4), Space (r + 9) (3 + (r + 2))) :=
  ProjectionObstruction.chosenFrame r (projectionMap D hi)
    (projectionMap_idempotent D hi) (obstruction_rank r D hi)

theorem fullNormalFrame_range (x : Disk (E := Vector 4)) :
    (fullNormalFrame r D hi x).val.range = (D x).rangeᗮ :=
  (ProjectionObstruction.chosenFrame_range r (projectionMap D hi)
    (projectionMap_idempotent D hi) (obstruction_rank r D hi) x).trans
      (projectionMap_range D hi x)

theorem fullNormalFrame_disjoint (x : Disk (E := Vector 4)) :
    Disjoint (fullNormalFrame r D hi x).val.range (D x).range := by
  rw [fullNormalFrame_range]
  exact (D x).range.orthogonal_disjoint.symm

def fullCoordinates (x : Disk (E := Vector 4)) :
    Vector ((3 + (r + 2)) + 4) ≃L[ℝ] Vector (r + 9) :=
  OperatorSum.coordinates (fullNormalFrame r D hi x).val (D x)
    (Stiefel.injective _) (hi x) (fullNormalFrame_disjoint r D hi x) (by omega)

theorem fullCoordinates_toContinuousLinearMap (x : Disk (E := Vector 4)) :
    (fullCoordinates r D hi x).toContinuousLinearMap =
      OperatorSum.operator (fullNormalFrame r D hi x).val (D x) := rfl

theorem continuous_fullCoordinates :
    Continuous (fun x ↦ (fullCoordinates r D hi x).toContinuousLinearMap) :=
  OperatorSum.continuous_operator _ _
    (continuous_subtype_val.comp (fullNormalFrame r D hi).continuous) D.continuous

theorem continuous_inverse_fullCoordinates :
    Continuous (fun x ↦ (fullCoordinates r D hi x).symm.toContinuousLinearMap) :=
  OperatorSum.continuous_inverse_coordinates _ _
    (continuous_subtype_val.comp (fullNormalFrame r D hi).continuous) D.continuous
    (fun x ↦ Stiefel.injective _) hi (fullNormalFrame_disjoint r D hi) (by omega)

variable (a : C(NoExoticSixSphere.Sphere 3, Space (r + 9) (r + 2)))
  (ha : ∀ s, (a s).val.range ≤ (D (boundaryToDisk s)).rangeᗮ)

include ha in
theorem boundary_fullNormalFrame_range (s : NoExoticSixSphere.Sphere 3) :
    (a s).val.range ≤ (fullNormalFrame r D hi (boundaryToDisk s)).val.range :=
  (ha s).trans_eq (fullNormalFrame_range r D hi (boundaryToDisk s)).symm

def normalBoundaryCoordinates :
    C(NoExoticSixSphere.Sphere 3, Space (3 + (r + 2)) (r + 2)) :=
  RangeObstruction.boundaryCoordinates r (fullNormalFrame r D hi) a
    (boundary_fullNormalFrame_range r D hi a ha)

theorem parity_eq_normalBoundaryCoordinates :
    parity r D hi a ha = sphereThirdObstruction r (normalBoundaryCoordinates r D hi a ha) := rfl

include hi ha in
theorem injective_combinedOperator (s : NoExoticSixSphere.Sphere 3) :
    Injective (OperatorSum.operator (a s).val (D (boundaryToDisk s))) :=
  OperatorSum.injective_operator _ _ (Stiefel.injective _) (hi _)
    ((D (boundaryToDisk s)).range.orthogonal_disjoint.symm.mono_left (ha s))

def combinedMap :
    C(NoExoticSixSphere.Sphere 3, Monomorphism.Space (r + 9) ((r + 2) + 4)) where
  toFun s := ⟨OperatorSum.operator (a s).val (D (boundaryToDisk s)),
    injective_combinedOperator r D hi a ha s⟩
  continuous_toFun := (OperatorSum.continuous_operator _ _
    (continuous_subtype_val.comp a.continuous)
    (D.continuous.comp boundaryToDisk.continuous)).subtype_mk _

theorem combinedMap_value (s : NoExoticSixSphere.Sphere 3) :
    (combinedMap r D hi a ha s).val = OperatorSum.operator (a s).val (D (boundaryToDisk s)) := rfl

theorem combinedMap_coordinates (s : NoExoticSixSphere.Sphere 3) :
    combinedMap r D hi a ha s =
      Monomorphism.recoordinate (fullCoordinates r D hi (boundaryToDisk s))
        (ContinuousLinearEquiv.refl ℝ (Vector ((r + 2) + 4)))
        (Monomorphism.blockMap 4 (Monomorphism.inclusion _ _
          (normalBoundaryCoordinates r D hi a ha s))) := by
  have he : (fullNormalFrame r D hi (boundaryToDisk s)).val.comp
      (normalBoundaryCoordinates r D hi a ha s).val = (a s).val :=
    congrArg Subtype.val (RangeCoordinates.comp_extract _ _
      (boundary_fullNormalFrame_range r D hi a ha s))
  apply Subtype.ext
  change OperatorSum.operator (a s).val (D (boundaryToDisk s)) =
    (OperatorSum.operator (fullNormalFrame r D hi (boundaryToDisk s)).val
      (D (boundaryToDisk s))).comp
        ((BlockSum.operator 4 (normalBoundaryCoordinates r D hi a ha s).val).comp
          (ContinuousLinearMap.id ℝ _))
  rw [ContinuousLinearMap.comp_id, OperatorSum.operator_comp_block, he]

theorem extends_combinedMap_iff_coordinates :
    Extends (combinedMap r D hi a ha) ↔ Extends (normalBoundaryCoordinates r D hi a ha) := by
  let f := (Monomorphism.inclusion (3 + (r + 2)) (r + 2)).comp
    (normalBoundaryCoordinates r D hi a ha)
  have he : Extends (combinedMap r D hi a ha) ↔ Extends ((Monomorphism.blockMap 4).comp f) :=
    Monomorphism.extends_recoordinate_iff (fullCoordinates r D hi)
      (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector ((r + 2) + 4)))
      (continuous_fullCoordinates r D hi) (continuous_inverse_fullCoordinates r D hi)
      continuous_const continuous_const ((Monomorphism.blockMap 4).comp f)
      (combinedMap r D hi a ha) (combinedMap_coordinates r D hi a ha)
  exact he.trans ((Monomorphism.extends_blockMap_iff (by omega) rfl 4 f).trans
    (extends_inclusion_iff _))

theorem parity_zero_iff_combined_extension :
    parity r D hi a ha = 0 ↔ Extends (combinedMap r D hi a ha) := by
  rw [parity_eq_normalBoundaryCoordinates]
  exact (sphereThirdObstruction_zero_iff_extension r _).trans
    (extends_combinedMap_iff_coordinates r D hi a ha).symm

end NoExoticSixSphere.Stiefel.DiskNormal
