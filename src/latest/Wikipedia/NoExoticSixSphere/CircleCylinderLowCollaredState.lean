import Wikipedia.NoExoticSixSphere.CircleCylinderEuclideanNormalFrame
import Wikipedia.NoExoticSixSphere.CircleCylinderTimeCollar
import Wikipedia.NoExoticSixSphere.CircleCylinderZeroDiffeomorph
import Wikipedia.NoExoticSixSphere.CircleCylinderPositiveComponent
import Wikipedia.HopfProblem.DegreeCollapseLowCollaredSevenBoundary

/-!
# The actual two-ended cylinder supplies a native framed collared seven-state

The compact circle double now supplies its original regular-fiber atlas,
closed Euclidean embedding, full equation-induced normal frame, regular
seam time, and explicit collar over the original endpoint disjoint union.
Neither endpoint is omitted; no connectivity or Arf comparison is assumed.
-/

noncomputable section

open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

open Wikipedia.HopfProblem.DegreeCollapse

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)
  (hd : m = n + 6) (a : Sphere 1 × Sphere m)

def lowCollaredState : LowCollaredSevenState (Endpoints d) := by
  let := fiberAtlas d 6 hd
  let := fiber_isManifold d 6 hd
  let := compactSpace_fiber d
  exact LowCollaredSevenState.ofCollar (embedding d 6 hd)
    (euclideanNormalFrame d a 6 hd) (time d) (contMDiff_time d 6 hd)
    (regular_time_zero d 6 hd) (timeCollar d)

def lowStateZeroDiffeomorph :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd);
    letI := (lowCollaredState d hd a).zeroAtlas;
    Endpoints d ≃ₘ⟮𝓡 6, 𝓡 6⟯ (lowCollaredState d hd a).Zero := by
  let := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd)
  let := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd)
  let := timeZeroAtlas d 6 hd
  exact endpointsDiffeomorph d 6 hd

theorem lowStateZeroDiffeomorph_val (p : Endpoints d) :
    letI := regularFiberAtlas d.leftMap d.smooth_left b d.regular_left 6 (by simpa using hd);
    letI := regularFiberAtlas d.rightMap d.smooth_right b d.regular_right 6 (by simpa using hd);
    letI := (lowCollaredState d hd a).zeroAtlas;
    (lowStateZeroDiffeomorph d hd a p).val = endpointsMap d p := rfl

theorem lowCollaredState_zeroPoint (p : Endpoints d) :
    ((lowCollaredState d hd a).collar.zeroPoint p).val = endpointsMap d p :=
  timeCollar_zeroPoint d p

end NoExoticSixSphere.CircleCylinder
