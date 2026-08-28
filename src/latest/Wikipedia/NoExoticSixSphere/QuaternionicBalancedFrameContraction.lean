import Wikipedia.NoExoticSixSphere.QuaternionicHopfSouthNormalFrame
import Wikipedia.NoExoticSixSphere.QuaternionCommutatorRotation

/-!
# An explicit contraction of the balanced quaternionic frame rotation

The actual pair of right and left quaternion multiplications is conjugate
to the two inverse diagonal blocks. A real quarter-turn moves the second
block to the first, cancelling them. Every intermediate real operator is
injective; this concerns the untwisted frame, not its geometric parity.
-/

noncomputable section

open Function unitInterval
open scoped Quaternion Matrix

namespace NoExoticSixSphere.QuaternionicHopf

open Wikipedia.HopfProblem.UnitQuaternionSphere
open Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFibration
open QuaternionCommutatorRotation

attribute [local irreducible] realRotation conjugatedFiber

def quaternionPairAction (A : SpTwo) : (ℍ × ℍ) →L[ℝ] ℍ × ℍ :=
  (((ContinuousLinearMap.mul ℝ ℍ (A.val 0 0)).comp (ContinuousLinearMap.fst ℝ ℍ ℍ) +
    (ContinuousLinearMap.mul ℝ ℍ (A.val 0 1)).comp (ContinuousLinearMap.snd ℝ ℍ ℍ)).prod
    ((ContinuousLinearMap.mul ℝ ℍ (A.val 1 0)).comp (ContinuousLinearMap.fst ℝ ℍ ℍ) +
      (ContinuousLinearMap.mul ℝ ℍ (A.val 1 1)).comp (ContinuousLinearMap.snd ℝ ℍ ℍ)))

theorem quaternionPairAction_apply (A : SpTwo) (v : ℍ × ℍ) :
    quaternionPairAction A v =
      (A.val 0 0 * v.1 + A.val 0 1 * v.2, A.val 1 0 * v.1 + A.val 1 1 * v.2) := rfl

theorem quaternionPairAction_injective (A : SpTwo) : Injective (quaternionPairAction A) := by
  intro v w h
  have hm : A.val *ᵥ ![v.1, v.2] = A.val *ᵥ ![w.1, w.2] := by
    funext i
    fin_cases i
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      change (quaternionPairAction A v).1 = (quaternionPairAction A w).1
      exact congrArg Prod.fst h
    · simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      change (quaternionPairAction A v).2 = (quaternionPairAction A w).2
      exact congrArg Prod.snd h
  have hv := Matrix.mulVec_injective_of_isUnit (Unitary.isUnit_coe (U := A)) hm
  exact Prod.ext (congrFun hv 0) (congrFun hv 1)

theorem continuous_quaternionPairAction : Continuous quaternionPairAction := by
  apply continuous_clm_apply.mpr
  intro v
  simp only [quaternionPairAction_apply]
  exact (((continuous_subtype_val.matrix_elem 0 0).mul continuous_const).add
    ((continuous_subtype_val.matrix_elem 0 1).mul continuous_const)).prodMk
      (((continuous_subtype_val.matrix_elem 1 0).mul continuous_const).add
        ((continuous_subtype_val.matrix_elem 1 1).mul continuous_const))

theorem quaternionPairAction_one (v : ℍ × ℍ) : quaternionPairAction 1 v = v := by
  simp [quaternionPairAction_apply]

local instance : StarModule ℝ ℍ where
  star_smul r q := by simp [Quaternion.star_smul]

def conjugatedPairCoordinates : (ℍ × ℍ) ≃L[ℝ] V 8 :=
  ((starL' ℝ : ℍ ≃L[ℝ] ℍ).prodCongr (ContinuousLinearEquiv.refl ℝ ℍ)).trans pairCoordinates

theorem conjugatedPairCoordinates_apply (v : ℍ × ℍ) :
    conjugatedPairCoordinates v = pairCoordinates (star v.1, v.2) := rfl

theorem conjugatedPairCoordinates_symm_apply (v : V 8) :
    conjugatedPairCoordinates.symm v = (star (first v), second v) := rfl

def conjugatedQuaternionAction (A : SpTwo) : V 8 →L[ℝ] V 8 :=
  conjugatedPairCoordinates.toContinuousLinearMap.comp
    ((quaternionPairAction A).comp conjugatedPairCoordinates.symm.toContinuousLinearMap)

theorem conjugatedQuaternionAction_injective (A : SpTwo) :
    Injective (conjugatedQuaternionAction A) :=
  conjugatedPairCoordinates.injective.comp
    ((quaternionPairAction_injective A).comp conjugatedPairCoordinates.symm.injective)

theorem continuous_conjugatedQuaternionAction : Continuous conjugatedQuaternionAction :=
  continuous_const.clm_comp (continuous_quaternionPairAction.clm_comp continuous_const)

theorem conjugatedQuaternionAction_one (v : V 8) : conjugatedQuaternionAction 1 v = v := by
  change conjugatedPairCoordinates
    (quaternionPairAction 1 (conjugatedPairCoordinates.symm v)) = v
  rw [quaternionPairAction_one, ContinuousLinearEquiv.apply_symm_apply]

def inverseDiagonalContraction (t : I) (q : UnitQuaternions) : SpTwo :=
  (firstDiagonal q)⁻¹ * conjugatedFiber ((t : ℝ) * (Real.pi / 2)) q

theorem continuous_inverseDiagonalContraction :
    Continuous (fun p : I × UnitQuaternions ↦ inverseDiagonalContraction p.1 p.2) := by
  have hq : Continuous (fun p : I × UnitQuaternions ↦ firstDiagonal p.2) :=
    continuous_firstDiagonal.comp continuous_snd
  have ht : Continuous (fun p : I × UnitQuaternions ↦ (p.1 : ℝ) * (Real.pi / 2)) :=
    (continuous_subtype_val.comp continuous_fst).mul_const _
  have hc : Continuous (fun p : I × UnitQuaternions ↦
      conjugatedFiber ((p.1 : ℝ) * (Real.pi / 2)) p.2) :=
    continuous_conjugatedFiber.comp (ht.prodMk continuous_snd)
  exact hq.inv.mul hc

theorem inverseDiagonalContraction_zero (q : UnitQuaternions) :
    inverseDiagonalContraction 0 q = (firstDiagonal q)⁻¹ * fiberInclusion q := by
  change (firstDiagonal q)⁻¹ * conjugatedFiber (0 * (Real.pi / 2)) q = _
  simp only [zero_mul,
    conjugatedFiber, realRotation_zero, one_mul, inv_one, mul_one]

theorem inverseDiagonalContraction_one (q : UnitQuaternions) :
    inverseDiagonalContraction 1 q = 1 := by
  change (firstDiagonal q)⁻¹ * conjugatedFiber (1 * (Real.pi / 2)) q = 1
  simp only [one_mul,
    conjugatedFiber, quarter_turn_conjugate, inv_mul_cancel]

theorem inverseDiagonalContraction_zero_matrix (q : UnitQuaternions) :
    (inverseDiagonalContraction 0 q).val = !![star q.val, 0; 0, q.val] := by
  rw [inverseDiagonalContraction_zero]
  change star (firstDiagonal q).val * (fiberInclusion q).val = _
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [firstDiagonal, fiberInclusion, fiberMatrix, Matrix.mul_apply,
      Fin.sum_univ_two, Matrix.star_apply]

attribute [local irreducible] inverseDiagonalContraction

def balancedFrameContraction (p : I × Sphere 3) : V 8 →L[ℝ] V 8 :=
  conjugatedQuaternionAction
    (inverseDiagonalContraction p.1
      (Wikipedia.HopfProblem.UnitQuaternionSphere.sphereHomeomorph.symm p.2))

theorem continuous_balancedFrameContraction : Continuous balancedFrameContraction := by
  have hs : Continuous (fun p : I × Sphere 3 ↦
      (p.1, Wikipedia.HopfProblem.UnitQuaternionSphere.sphereHomeomorph.symm p.2)) :=
    continuous_fst.prodMk
      (Wikipedia.HopfProblem.UnitQuaternionSphere.sphereHomeomorph.symm.continuous.comp
        continuous_snd)
  exact continuous_conjugatedQuaternionAction.comp
    (continuous_inverseDiagonalContraction.comp hs)

theorem balancedFrameContraction_injective (p : I × Sphere 3) :
    Injective (balancedFrameContraction p) := conjugatedQuaternionAction_injective _

theorem balancedFrameContraction_one (s : Sphere 3) (v : V 8) :
    balancedFrameContraction (1, s) v = v := by
  change conjugatedQuaternionAction (inverseDiagonalContraction 1 _) v = v
  rw [inverseDiagonalContraction_one, conjugatedQuaternionAction_one]

theorem balancedFrameContraction_zero_first (s : Sphere 3) (v : V 8) :
    first (balancedFrameContraction (0, s) v) =
      first v * Quaternion.linearIsometryEquivTuple.symm s.val := by
  change first (conjugatedPairCoordinates
    (quaternionPairAction (inverseDiagonalContraction 0 _)
      (conjugatedPairCoordinates.symm v))) = _
  rw [quaternionPairAction_apply, inverseDiagonalContraction_zero_matrix,
    conjugatedPairCoordinates_symm_apply, conjugatedPairCoordinates_apply]
  change (planeCoordinates.symm (planeCoordinates
    (WithLp.toLp 2 (star (star _ * star (first v) + 0 * second v),
      0 * star (first v) + _ * second v)))).fst = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  simp only [zero_mul, add_zero, star_mul, star_star]
  rfl

theorem balancedFrameContraction_zero_second (s : Sphere 3) (v : V 8) :
    second (balancedFrameContraction (0, s) v) =
      Quaternion.linearIsometryEquivTuple.symm s.val * second v := by
  change second (conjugatedPairCoordinates
    (quaternionPairAction (inverseDiagonalContraction 0 _)
      (conjugatedPairCoordinates.symm v))) = _
  rw [quaternionPairAction_apply, inverseDiagonalContraction_zero_matrix,
    conjugatedPairCoordinates_symm_apply, conjugatedPairCoordinates_apply]
  change (planeCoordinates.symm (planeCoordinates
    (WithLp.toLp 2 (star (star _ * star (first v) + 0 * second v),
      0 * star (first v) + _ * second v)))).snd = _
  rw [LinearIsometryEquiv.symm_apply_apply]
  simp only [zero_mul, zero_add]
  rfl

end NoExoticSixSphere.QuaternionicHopf
