import Wikipedia.NoExoticSixSphere.CircleCylinderEuclideanEquations
import Wikipedia.HopfProblem.DegreeCollapseEuclideanProductCoordinates

/-!
# The original equation frame supplies the circle double's Euclidean normal framing

The actual Euclidean embedding is framed using the canonical orthogonal
right inverse of its transported equations. Ordered, fixed normal-model
coordinates turn that frame into the required Euclidean normal framing.
-/

noncomputable section

open Function Module
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

def normalCoordinates (k : ℕ) (hd : m = n + k) :
    EuclideanSpace ℝ (Fin (2 + (m + 1) - (k + 1))) ≃L[ℝ] NormalModel n := by
  have he : 2 + (m + 1) - (k + 1) = (n + 1) + 1 := by omega
  rw [he]
  exact ((Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct.headIsometry (n + 1)).symm.trans
    (LinearIsometryEquiv.withLpProdCongr 2 (LinearIsometryEquiv.refl ℝ ℝ)
      (Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct.headIsometry n).symm)
        ).toContinuousLinearEquiv

def euclideanModelFrame (a : Sphere 1 × Sphere m) (k : ℕ) (hd : m = n + k) :
    letI := fiberAtlas d k hd;
    SmoothRangeFrame (𝓡 (k + 1)) (embedding d k hd).normalProjection (NormalModel n) := by
  let := fiberAtlas d k hd
  apply NormalFrameOfEquations.inducedFrame
    (contMDiff_euclideanInclusion d k hd) (contDiffAt_euclideanEquations d a)
    (euclideanEquations_zero d a) (surjective_fderiv_euclideanEquations d a)
    (injective_mfderiv_euclideanInclusion d k hd)
  rw [finrank_normalModel, finrank_euclideanSpace_fin, finrank_euclideanSpace_fin]
  omega

def euclideanNormalFrame (a : Sphere 1 × Sphere m) (k : ℕ) (hd : m = n + k) :
    letI := fiberAtlas d k hd;
    SmoothRangeFrame (𝓡 (k + 1)) (embedding d k hd).normalProjection
      (embedding d k hd).NormalModel := by
  let := fiberAtlas d k hd
  let A := euclideanModelFrame d a k hd
  let Q : (embedding d k hd).NormalModel ≃L[ℝ] NormalModel n := normalCoordinates k hd
  refine ⟨fun p ↦ Q.trans (A.equiv p), ?_⟩
  change ContMDiff (𝓡 (k + 1))
    𝓘(ℝ, (embedding d k hd).NormalModel →L[ℝ]
      EuclideanSpace ℝ (Fin (embedding d k hd).ambientDimension)) ∞
    (fun p ↦ (A.ambient p).comp Q.toContinuousLinearMap)
  exact A.contMDiff_ambient.clm_comp contMDiff_const

theorem euclideanNormalFrame_ambient (a : Sphere 1 × Sphere m)
    (k : ℕ) (hd : m = n + k) (p : Fiber d) :
    letI := fiberAtlas d k hd;
    (euclideanNormalFrame d a k hd).ambient p =
      (orthogonalRightInverse
        (fderiv ℝ (euclideanEquations d a) (euclideanInclusion d p))).comp
          (normalCoordinates k hd).toContinuousLinearMap := by
  let := fiberAtlas d k hd
  apply ContinuousLinearMap.ext
  intro v
  rfl

end NoExoticSixSphere.CircleCylinder
