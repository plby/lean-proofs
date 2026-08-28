import Wikipedia.HopfProblem.DegreeCollapseLowRoundedCollarLevel
import Wikipedia.NoExoticSixSphere.RoundedCornerBranchDifferential

/-! # Actual defining differentials on the unchanged branches of the eight-dimensional collar -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowRoundedHandleCorner

open NoExoticSixSphere GLOrthonormalization

variable {d q : ℕ}

def collarDifferential (χ : ContDiffBump (0 : ℝ)) (r : ℝ) (p : (Collar d q)) :
    ((Vector d × Vector q) × ℝ) →L[ℝ] ℝ :=
  mfderiv (collarModel d q) 𝓘(ℝ, ℝ) (collarLevel χ r) p

theorem collarDifferential_apply (χ : ContDiffBump (0 : ℝ)) (r : ℝ) (p : (Collar d q))
    (w : (Vector d × Vector q) × ℝ) :
    collarDifferential χ r p w = fderiv ℝ (SmoothCornerRounding.level χ)
      (GeneralRoundedHandleCorner.coordinates r (collarProjection p))
        (w.2, -2 * inner ℝ p.1.2 w.1.2) := by
  have hc : collarDifferential χ r p =
      (fderiv ℝ (GeneralRoundedHandleCorner.level χ r) (collarProjection p)).comp
        (mfderiv (collarModel d q) 𝓘(ℝ, Vector q × ℝ) collarProjection p) := by
    rw [collarDifferential, collarLevel, mfderiv_comp p
      ((GeneralRoundedHandleCorner.contDiff_level χ r).contMDiff.mdifferentiableAt (by simp))
      ((contMDiff_collarProjection (d := d) (q := q)).mdifferentiableAt (by simp)),
      mfderiv_eq_fderiv]
    rfl
  rw [hc]
  change fderiv ℝ (GeneralRoundedHandleCorner.level χ r) (collarProjection p)
    (mfderiv (collarModel d q) 𝓘(ℝ, Vector q × ℝ) collarProjection p w) = _
  rw [mfderiv_collarProjection_apply]
  have hd : fderiv ℝ (GeneralRoundedHandleCorner.level χ r) (collarProjection p) =
      (fderiv ℝ (SmoothCornerRounding.level χ)
        (GeneralRoundedHandleCorner.coordinates r (collarProjection p))).comp
        (fderiv ℝ (GeneralRoundedHandleCorner.coordinates r) (collarProjection p)) :=
    fderiv_comp _ ((SmoothCornerRounding.contDiff_level χ).differentiable (by simp) _)
      ((GeneralRoundedHandleCorner.contDiff_coordinates r).differentiable (by simp) _)
  rw [hd]
  change fderiv ℝ (SmoothCornerRounding.level χ)
    (GeneralRoundedHandleCorner.coordinates r (collarProjection p))
    (fderiv ℝ (GeneralRoundedHandleCorner.coordinates r) (collarProjection p) (w.1.2, w.2)) = _
  rw [GeneralRoundedHandleCorner.fderiv_coordinates_apply]
  rfl

theorem collarDifferential_of_right (χ : ContDiffBump (0 : ℝ)) (r : ℝ) (p : (Collar d q))
    (hp : χ.rOut < p.2 - (r ^ 2 - ‖p.1.2‖ ^ 2)) (w : (Vector d × Vector q) × ℝ) :
    collarDifferential χ r p w = 2 * w.2 := by
  rw [collarDifferential_apply, SmoothCornerRounding.fderiv_level_of_right χ hp]

theorem collarDifferential_of_left (χ : ContDiffBump (0 : ℝ)) (r : ℝ) (p : (Collar d q))
    (hp : p.2 - (r ^ 2 - ‖p.1.2‖ ^ 2) < -χ.rOut) (w : (Vector d × Vector q) × ℝ) :
    collarDifferential χ r p w = -4 * inner ℝ p.1.2 w.1.2 := by
  rw [collarDifferential_apply, SmoothCornerRounding.fderiv_level_of_left χ hp]
  ring

end Wikipedia.HopfProblem.DegreeCollapse.LowRoundedHandleCorner
