import Wikipedia.HomotopyGroupsOfSpheres.CoordinateFrames
import Wikipedia.HomotopyGroupsOfSpheres.CliffordPoleProjection

/-! # The fixed positive frame at the raw Clifford pole -/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open BalancedRealInvolutions

def polePositiveIndex : Fin 6 ↪ Fin 12 := ⟨![1, 2, 3, 7, 8, 9], by decide⟩

def canonicalPoleFrame : Stiefel.Space 12 6 := CoordinateFrames.frame polePositiveIndex

theorem canonicalPoleFrame_basis (j : Fin 6) :
    canonicalPoleFrame.val (EuclideanSpace.basisFun (Fin 6) ℝ j) =
      EuclideanSpace.basisFun (Fin 12) ℝ (polePositiveIndex j) :=
  CoordinateFrames.frame_basis polePositiveIndex j

theorem canonicalPoleFrame_adjoint_apply (x : Vector 12) (j : Fin 6) :
    (canonicalPoleFrame.val.adjoint x) j = x (polePositiveIndex j) :=
  CoordinateFrames.frame_adjoint_apply polePositiveIndex x j

theorem canonicalPoleFrame_projector_apply (x : Vector 12) (i : Fin 12) :
    FrameProjection.operator canonicalPoleFrame x i = polePositiveMask i * x i := by
  change ((CoordinateFrames.frame polePositiveIndex).val.comp
    (CoordinateFrames.frame polePositiveIndex).val.adjoint) x i = _
  rw [CoordinateFrames.frame_projector_apply]
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
  change (if i = 1 then x 1 else 0) + ((if i = 2 then x 2 else 0) +
    ((if i = 3 then x 3 else 0) + ((if i = 7 then x 7 else 0) +
      ((if i = 8 then x 8 else 0) + (if i = 9 then x 9 else 0))))) = _
  rw [polePositiveMask_eq]
  fin_cases i <;> norm_num [Fin.ext_iff] <;> rfl

theorem canonicalPoleFrame_project : FrameProjection.toBalanced canonicalPoleFrame =
    rawBalanced pole := by
  apply positiveProjection_injective 6
  rw [FrameProjection.positiveProjection_toBalanced]
  apply ContinuousLinearMap.ext
  intro x
  apply PiLp.ext
  intro i
  exact (canonicalPoleFrame_projector_apply x i).trans
    (positiveProjection_raw_pole_apply x i).symm

end Wikipedia.HomotopyGroupsOfSpheres.CliffordFiveHermitian
