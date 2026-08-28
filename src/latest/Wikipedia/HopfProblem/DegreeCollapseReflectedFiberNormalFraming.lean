import Wikipedia.HopfProblem.DegreeCollapseReflectedFiberEuclideanEmbedding
import Wikipedia.NoExoticSixSphere.SmoothFrameCoordinates

/-!
# The reflected double's framing in its own Euclidean normal model

Both the ambient and model coordinates are actual fixed linear isometries.
The full normal-range equality is transported from the native cylinder
frame, and the whole seam-collar formula retains the original frame values.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere GLOrthonormalization

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hmiss : ∀ x, d.rightMap x ≠ b) (k : ℕ) (hd : m = n + k)

include hd in
theorem normalModel_dimension : (m + 2) - (k + 1) = n + 1 := by omega

def normalModelCoordinates : letI := fiberAtlas d k hd;
    (embedding d hmiss k hd).NormalModel ≃ₗᵢ[ℝ] WithLp 2 (ℝ × Vector n) := by
  let := fiberAtlas d k hd
  exact (LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ (finCongr (normalModel_dimension k hd))).trans
    (EuclideanTailCoordinates.split n)

def frameColumns (a : Sphere m) (p : Fiber d) : letI := fiberAtlas d k hd;
    (embedding d hmiss k hd).NormalModel →L[ℝ] Vector (m + 2) := by
  let := fiberAtlas d k hd
  exact (ambientCoordinates m).toContinuousLinearMap.comp
    (((normalFrame d k hd a).ambient p).comp
      (normalModelCoordinates d hmiss k hd).toContinuousLinearMap)

theorem injective_frameColumns (a : Sphere m) (p : Fiber d) : letI := fiberAtlas d k hd;
    Injective (frameColumns d hmiss k hd a p) := by
  let := fiberAtlas d k hd
  exact (ambientCoordinates m).injective.comp (((normalFrame d k hd a).ambient_injective p).comp
    (normalModelCoordinates d hmiss k hd).injective)

theorem contMDiff_frameColumns (a : Sphere m) : letI := fiberAtlas d k hd;
    ContMDiff (𝓡 (k + 1)) 𝓘(ℝ, (embedding d hmiss k hd).NormalModel →L[ℝ]
      Vector (m + 2)) ∞ (frameColumns d hmiss k hd a) := by
  let := fiberAtlas d k hd
  exact contMDiff_const.clm_comp ((normalFrame d k hd a).smooth.clm_comp contMDiff_const)

theorem frameColumns_range (a : Sphere m) (p : Fiber d) : letI := fiberAtlas d k hd;
    (frameColumns d hmiss k hd a p).range =
      ((embedding d hmiss k hd).normalProjection p).range := by
  let := fiberAtlas d k hd
  have hr : (((normalFrame d k hd a).ambient p).comp
      (normalModelCoordinates d hmiss k hd).toContinuousLinearMap).range =
        ((normalFrame d k hd a).ambient p).range :=
    LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (normalModelCoordinates d hmiss k hd).surjective)
  have hc : (frameColumns d hmiss k hd a p).range =
      ((((normalFrame d k hd a).ambient p).comp
        (normalModelCoordinates d hmiss k hd).toContinuousLinearMap).range).map
          (ambientCoordinates m).toLinearEquiv.toLinearMap :=
    LinearMap.range_comp _ _
  have hm := congrArg
    (fun S : Submodule ℝ (WithLp 2 (ℝ × Vector (m + 1))) ↦
      S.map (ambientCoordinates m).toLinearEquiv.toLinearMap)
    (hr.trans (normalFrame_range d k hd a p))
  exact hc.trans (hm.trans (normalProjection_range d hmiss k hd p).symm)

def euclideanNormalFraming (a : Sphere m) : letI := fiberAtlas d k hd;
    SmoothRangeFrame (𝓡 (k + 1)) (embedding d hmiss k hd).normalProjection
      (embedding d hmiss k hd).NormalModel := by
  let := fiberAtlas d k hd
  let F := frameColumns d hmiss k hd a
  let P : Fiber d → Vector (m + 2) →L[ℝ] Vector (m + 2) :=
    (embedding d hmiss k hd).normalProjection
  have hr (p : Fiber d) : (F p).range = (P p).range :=
    frameColumns_range d hmiss k hd a p
  let q (p : Fiber d) : (embedding d hmiss k hd).NormalModel ≃L[ℝ] (P p).range :=
    (LinearEquiv.ofInjective (F p).toLinearMap
      (injective_frameColumns d hmiss k hd a p)).toContinuousLinearEquiv.trans
        (ContinuousLinearEquiv.ofEq _ _ (hr p))
  refine ⟨q, ?_⟩
  have he : (fun p : Fiber d ↦ (P p).range.subtypeL.comp
      (q p).toContinuousLinearMap) = F := by
    funext p
    apply ContinuousLinearMap.ext
    intro v
    rfl
  have hs : ContMDiff (𝓡 (k + 1))
      𝓘(ℝ, (embedding d hmiss k hd).NormalModel →L[ℝ] Vector (m + 2)) ∞
      (fun p : Fiber d ↦ (P p).range.subtypeL.comp (q p).toContinuousLinearMap) :=
    he.symm ▸ contMDiff_frameColumns d hmiss k hd a
  exact hs

theorem euclideanNormalFraming_ambient (a : Sphere m) (p : Fiber d) :
    letI := fiberAtlas d k hd;
    (euclideanNormalFraming d hmiss k hd a).ambient p = frameColumns d hmiss k hd a p := rfl

theorem euclideanNormalFraming_seamCollar (a : Sphere m) (t : ℝ)
    (ht : t ∈ seamCollarTimes d) (x : {x : Sphere m // d.leftMap x = b}) :
    letI := fiberAtlas d k hd;
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd);
    (euclideanNormalFraming d hmiss k hd a).ambient (seamCollarPoint d t ht x) =
      (ambientCoordinates m).toContinuousLinearMap.comp
        ((CylinderNormalFrame.liftFrame
          ((SphereFiberNormalFrame.normalFrame d.leftMap d.smooth_left b
            d.regular_left k hd a).ambient x)).comp
              (normalModelCoordinates d hmiss k hd).toContinuousLinearMap) := by
  let := fiberAtlas d k hd
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left k (by simpa using hd)
  rw [euclideanNormalFraming_ambient, frameColumns, normalFrame_seamCollar]

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
