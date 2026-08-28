import Wikipedia.NoExoticSixSphere.WhitneyCuspResidualCoordinates
import Wikipedia.NoExoticSixSphere.PartialFrameFiberParity
import Wikipedia.NoExoticSixSphere.EuclideanBlockCoordinates

/-!
# The actual cusp derivative has local frame parity one

The simple endpoint of the explicit derivative deformation is reconstructed
twice from the signed-permutation sphere parameterization. The first
reconstruction is nonzero by its actual singular homology map; the second
preserves parity by the checked column stability theorem.
-/

noncomputable section

namespace NoExoticSixSphere.WhitneyCusp

open GLOrthonormalization Stiefel

theorem headSplit_fst (n : ℕ) (w : Vector (1 + n)) :
    (headSplit n w).fst = w 0 := rfl

theorem headSplit_snd (n : ℕ) (w : Vector (1 + n)) (i : Fin n) :
    (headSplit n w).snd i = w (i.natAdd 1) := rfl

theorem headSplit_symm_zero (n : ℕ) (z : WithLp 2 (ℝ × Vector n)) :
    (headSplit n).symm z 0 = z.fst := by
  rw [headSplit_symm_apply]
  change EuclideanSpace.finAddEquivProd.symm
    (EuclideanTailCoordinates.scalar z.fst, z.snd) ((0 : Fin 1).castAdd n) = _
  rw [EuclideanBlocks.symm_castAdd]
  rfl

theorem headSplit_symm_natAdd (n : ℕ) (z : WithLp 2 (ℝ × Vector n)) (i : Fin n) :
    (headSplit n).symm z (i.natAdd 1) = z.snd i := by
  rw [headSplit_symm_apply, EuclideanBlocks.symm_natAdd]

def residualTwoFrameMap : C(Sphere 3, Space 5 2) :=
  (SplitReconstruction.map (headSplit 1) (headSplit 4)).comp
    (residualFrameHomeomorph : C(Sphere 3, Space 4 1))

theorem residualTwoFrameMap_apply (q : Sphere 3) (w : Vector 2) (i : Fin 5) :
    (residualTwoFrameMap q).val w i =
      ![w 0, w 1 * q.val 3, w 1 * q.val 1, w 1 * q.val 2, -(w 1 * q.val 0)] i := by
  change (SplitReconstruction.reconstruct (headSplit 1) (headSplit 4)
    (residualFrameHomeomorph q)).val w i = _
  rw [SplitReconstruction.reconstruct_apply]
  refine Fin.addCases (m := 1) (n := 4) (fun j ↦ ?_) (fun j ↦ ?_) i
  · fin_cases j
    change (headSplit 4).symm
      (RectangularColumnBlock.block (toIsometry (residualFrameHomeomorph q))
        (headSplit 1 w)) 0 = w 0
    rw [headSplit_symm_zero]
    rfl
  · rw [headSplit_symm_natAdd]
    change (residualFrameHomeomorph q).val (headSplit 1 w).snd j = _
    rw [residualFrameHomeomorph_apply]
    have hw : (headSplit 1 w).snd 0 = w 1 := rfl
    fin_cases j <;> simp [hw]

theorem simpleFrameMap_eq_reconstruction :
    simpleFrameMap = (SplitReconstruction.map (headSplit 2) (headSplit 5)).comp
      residualTwoFrameMap := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro w
  ext i
  change deformation 0 q.val w i =
    (SplitReconstruction.reconstruct (headSplit 2) (headSplit 5)
      (residualTwoFrameMap q)).val w i
  rw [SplitReconstruction.reconstruct_apply]
  refine Fin.addCases (m := 1) (n := 5) (fun j ↦ ?_) (fun j ↦ ?_) i
  · fin_cases j
    change deformation 0 q.val w 0 = (headSplit 5).symm
      (RectangularColumnBlock.block (toIsometry (residualTwoFrameMap q))
        (headSplit 2 w)) 0
    rw [headSplit_symm_zero, deformation_apply]
    rfl
  · rw [headSplit_symm_natAdd]
    change deformation 0 q.val w (j.natAdd 1) =
      (residualTwoFrameMap q).val (headSplit 2 w).snd j
    rw [residualTwoFrameMap_apply, deformation_apply]
    have hw₀ : (headSplit 2 w).snd 0 = w 1 := rfl
    have hw₁ : (headSplit 2 w).snd 1 = w 2 := rfl
    fin_cases j <;> simp [hw₀, hw₁, mul_comm]

theorem residualTwoFrame_parity : sphereThirdObstruction 0 residualTwoFrameMap = 1 :=
  SplitReconstruction.oneColumn_sphere_parity (headSplit 1) (headSplit 4)
    residualFrameHomeomorph

theorem simpleFrame_parity : sphereThirdObstruction 1 simpleFrameMap = 1 := by
  rw [simpleFrameMap_eq_reconstruction, SplitReconstruction.sphere_parity,
    residualTwoFrame_parity]

theorem gauss_parity : sphereThirdObstruction 1 gaussMap = 1 := by
  rw [gauss_parity_eq_simple, simpleFrame_parity]

end NoExoticSixSphere.WhitneyCusp
