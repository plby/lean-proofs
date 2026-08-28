import Wikipedia.NoExoticSixSphere.OutwardGraphFrameHomotopy
import Wikipedia.NoExoticSixSphere.CollaredBoundaryOperatorCoordinates
import Wikipedia.NoExoticSixSphere.OrthogonalFrameAppendStabilization

/-!
# The height-axis endpoint is a genuine stabilization of the original operator

The new height column is inserted between the old normal and derivative
blocks by an explicit fixed source permutation. The graph-coordinate
stabilization then appends exactly five further axes. Both operations
preserve exact disk extendability in the original codimension-three range.
-/

noncomputable section

namespace NoExoticSixSphere.OutwardGraphFrame

open GLOrthonormalization Stiefel CollaredDiskFrame OrthogonalFrameAppend DiskBoundary

variable {N k : ℕ}

def heightCoordinates (N : ℕ) : Vector (N + 1) ≃L[ℝ] (Vector N × ℝ) :=
  EuclideanSpace.finAddEquivProd.trans
    ((ContinuousLinearEquiv.refl ℝ (Vector N)).prodCongr
      EuclideanTailCoordinates.scalar.symm.toContinuousLinearEquiv)

theorem heightCoordinates_apply (v : Vector (N + 1)) :
    heightCoordinates N v = ((EuclideanSpace.finAddEquivProd v).1,
      EuclideanTailCoordinates.scalar.symm (EuclideanSpace.finAddEquivProd v).2) := rfl

theorem oneAxis_operator (A : Vector k →L[ℝ] Vector N) (D : Vector 4 →L[ℝ] Vector N) :
    (BlockSum.operator 1 (OperatorSum.operator A D)).comp
        (appendBlockPermutation k 4).symm.toContinuousLinearMap =
      OperatorSum.operator (BlockSum.operator 1 A) ((appendZeroMap N 1).comp D) := by
  apply ContinuousLinearMap.ext
  intro z
  obtain ⟨w, rfl⟩ := (appendBlockPermutation k 4).surjective z
  change BlockSum.operator 1 (OperatorSum.operator A D)
      ((appendBlockPermutation k 4).symm (appendBlockPermutation k 4 w)) = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  simp only [BlockSum.operator_apply, OperatorSum.operator_apply,
    appendBlockPermutation_apply, appendBlockCoordinates_apply,
    ContinuousLinearEquiv.apply_symm_apply, ContinuousLinearMap.comp_apply]
  change EuclideanSpace.finAddEquivProd.symm (_, _) =
    EuclideanSpace.finAddEquivProd.symm (_, _) + EuclideanSpace.finAddEquivProd.symm (_, 0)
  rw [← map_add]
  simp only [Prod.mk_add_mk, add_zero]
  rfl

theorem heightCoordinates_normal (A : Vector k →L[ℝ] Vector N) (ν : Vector N) :
    (heightCoordinates N).toContinuousLinearMap.comp (BlockSum.operator 1 A) = normal 0 A ν := by
  apply ContinuousLinearMap.ext
  intro u
  change heightCoordinates N (BlockSum.operator 1 A u) = normal 0 A ν u
  rw [heightCoordinates_apply, BlockSum.operator_apply,
    ContinuousLinearEquiv.apply_symm_apply, normal_apply]
  simp only [zero_smul, smul_zero, add_zero, sub_zero, mul_one]

theorem heightCoordinates_derivative (D : Vector 4 →L[ℝ] Vector N) :
    (heightCoordinates N).toContinuousLinearMap.comp ((appendZeroMap N 1).comp D) =
      graph D 0 := by
  apply ContinuousLinearMap.ext
  intro v
  change heightCoordinates N (EuclideanSpace.finAddEquivProd.symm (D v, 0)) = (D v, 0)
  rw [heightCoordinates_apply, ContinuousLinearEquiv.apply_symm_apply, map_zero]

def normalStabilization : C(Monomorphism.Space N (k + 4),
    Monomorphism.Space (N + 1) ((k + 1) + 4)) :=
  (Monomorphism.recoordinateHomeomorph
    (ContinuousLinearEquiv.refl ℝ (Vector (N + 1)))
    (appendBlockPermutation k 4).symm.toContinuousLinearEquiv :
      C(Monomorphism.Space (N + 1) ((k + 4) + 1),
        Monomorphism.Space (N + 1) ((k + 1) + 4))).comp (Monomorphism.blockMap 1)

theorem normalStabilization_operator (P : Monomorphism.Space N (k + 4))
    (A : Vector k →L[ℝ] Vector N) (D : Vector 4 →L[ℝ] Vector N)
    (hP : P.val = OperatorSum.operator A D) :
    (normalStabilization P).val =
      OperatorSum.operator (BlockSum.operator 1 A) ((appendZeroMap N 1).comp D) := by
  change (BlockSum.operator 1 P.val).comp
    (appendBlockPermutation k 4).symm.toContinuousLinearMap = _
  rw [hP, oneAxis_operator]

def plainStabilization : C(Monomorphism.Space N (k + 4),
    Monomorphism.Space (N + 6) (((k + 1) + 5) + 4)) :=
  (stabilizationMap (heightCoordinates N)).comp normalStabilization

theorem plainStabilization_operator (P : Monomorphism.Space N (k + 4))
    (A : Vector k →L[ℝ] Vector N) (D : Vector 4 →L[ℝ] Vector N) (ν : Vector N)
    (hP : P.val = OperatorSum.operator A D) :
    (plainStabilization P).val = combined (normal 0 A ν) (graph D 0) := by
  have h := stabilizationMap_operator (heightCoordinates N) (normalStabilization P)
    (BlockSum.operator 1 A) ((appendZeroMap N 1).comp D)
    (normalStabilization_operator P A D hP)
  rw [heightCoordinates_normal A ν, heightCoordinates_derivative] at h
  exact h

theorem extends_normalStabilization_iff (hN : N = 3 + (k + 4))
    (P : C(Sphere 3, Monomorphism.Space N (k + 4))) :
    Extends (normalStabilization.comp P) ↔ Extends P := by
  have h : Extends (normalStabilization.comp P) ↔
      Extends ((Monomorphism.blockMap 1).comp P) :=
    Monomorphism.extends_recoordinate_iff
      (fun _ ↦ ContinuousLinearEquiv.refl ℝ (Vector (N + 1)))
      (fun _ ↦ (appendBlockPermutation k 4).symm.toContinuousLinearEquiv)
      continuous_const continuous_const continuous_const continuous_const
      ((Monomorphism.blockMap 1).comp P) (normalStabilization.comp P) (fun _ ↦ rfl)
  exact h.trans (Monomorphism.extends_blockMap_iff (by omega) hN 1 P)

theorem extends_plainStabilization_iff (hN : N = 3 + (k + 4))
    (P : C(Sphere 3, Monomorphism.Space N (k + 4))) :
    Extends (plainStabilization.comp P) ↔ Extends P :=
  (extends_stabilizationMap_iff (by omega) (heightCoordinates N)
    (normalStabilization.comp P)).trans (extends_normalStabilization_iff hN P)

end NoExoticSixSphere.OutwardGraphFrame
