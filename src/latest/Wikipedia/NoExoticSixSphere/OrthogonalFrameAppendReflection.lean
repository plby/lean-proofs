import Wikipedia.NoExoticSixSphere.OrthogonalFrameAppend

/-!
# The exact last-column reflection in an appended orthogonal frame

The reflection is an isometry of the actual Euclidean coordinate space.
Changing the sign of the appended column is precomposition by this fixed
reflection; the original columns and their order do not change.
-/

noncomputable section

namespace NoExoticSixSphere.OrthogonalFrameAppend

open GLOrthonormalization

def lastReflection (k : ℕ) : Vector (k + 1) ≃ₗᵢ[ℝ] Vector (k + 1) :=
  ((EuclideanTailCoordinates.finAdd k 1).trans
    (LinearIsometryEquiv.withLpProdCongr 2
      (LinearIsometryEquiv.refl ℝ (Vector k)) (LinearIsometryEquiv.neg ℝ))).trans
        (EuclideanTailCoordinates.finAdd k 1).symm

theorem lastReflection_split (k : ℕ) (w : Vector (k + 1)) :
    EuclideanSpace.finAddEquivProd (lastReflection k w) =
      ((EuclideanSpace.finAddEquivProd w).1, -(EuclideanSpace.finAddEquivProd w).2) := by
  change WithLp.ofLp
    (EuclideanTailCoordinates.finAdd k 1
      ((EuclideanTailCoordinates.finAdd k 1).symm _)) = _
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem operator_neg {N k : ℕ} (B : Vector k →L[ℝ] Vector N) (ν : Vector N) :
    operator B (-ν) = (operator B ν).comp (lastReflection k).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro w
  change operator B (-ν) w = operator B ν (lastReflection k w)
  rw [operator_apply, operator_apply, lastReflection_split]
  simp only [map_neg, neg_smul, smul_neg]

end NoExoticSixSphere.OrthogonalFrameAppend
