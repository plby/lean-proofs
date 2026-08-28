import Wikipedia.NoExoticSixSphere.RoundedCollarLevel

/-! # Exact defining differentials on the two unchanged ends of the rounded collar -/

noncomputable section

open Set Filter
open scoped Topology Manifold ContDiff

namespace NoExoticSixSphere.SmoothCornerRounding

variable (χ : ContDiffBump (0 : ℝ))

theorem fderiv_level_of_right {p : ℝ × ℝ} (hp : χ.rOut < p.1 - p.2) (w : ℝ × ℝ) :
    fderiv ℝ (level χ) p w = 2 * w.1 := by
  have he : level χ =ᶠ[𝓝 p] (fun q : ℝ × ℝ ↦ 2 * q.1) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_fst.sub continuous_snd)).mem_nhds hp]
      with q hq
    change χ.rOut < q.1 - q.2 at hq
    rw [level_eq_two_max χ (by rw [abs_of_pos (by linarith [χ.rOut_pos])]; exact hq.le),
      max_eq_left (by linarith [χ.rOut_pos])]
  have hd : fderiv ℝ (level χ) p = (2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ :=
    he.fderiv_eq.trans ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt.fderiv
  exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ ↦ L w) hd

theorem fderiv_level_of_left {p : ℝ × ℝ} (hp : p.1 - p.2 < -χ.rOut) (w : ℝ × ℝ) :
    fderiv ℝ (level χ) p w = 2 * w.2 := by
  have he : level χ =ᶠ[𝓝 p] (fun q : ℝ × ℝ ↦ 2 * q.2) := by
    filter_upwards [(isOpen_lt (continuous_fst.sub continuous_snd) continuous_const).mem_nhds hp]
      with q hq
    change q.1 - q.2 < -χ.rOut at hq
    rw [level_eq_two_max χ (by rw [abs_of_neg (by linarith [χ.rOut_pos])]; linarith),
      max_eq_right (by linarith [χ.rOut_pos])]
  have hd : fderiv ℝ (level χ) p = (2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ :=
    he.fderiv_eq.trans ((2 : ℝ) • ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.fderiv
  exact congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ ↦ L w) hd

end NoExoticSixSphere.SmoothCornerRounding

namespace NoExoticSixSphere.RoundedHandleCorner

open GLOrthonormalization

def collarDifferential (χ : ContDiffBump (0 : ℝ)) (r : ℝ) (p : Collar) :
    ((Vector 3 × Vector 3) × ℝ) →L[ℝ] ℝ :=
  mfderiv collarModel 𝓘(ℝ, ℝ) (collarLevel χ r) p

theorem collarDifferential_apply (χ : ContDiffBump (0 : ℝ)) (r : ℝ) (p : Collar)
    (w : (Vector 3 × Vector 3) × ℝ) :
    collarDifferential χ r p w = fderiv ℝ (SmoothCornerRounding.level χ)
      (coordinates r (collarProjection p)) (w.2, -2 * inner ℝ p.1.2 w.1.2) := by
  have hc : collarDifferential χ r p =
      (fderiv ℝ (level χ r) (collarProjection p)).comp
        (mfderiv collarModel 𝓘(ℝ, Vector 3 × ℝ) collarProjection p) := by
    rw [collarDifferential, collarLevel, mfderiv_comp p
      ((contDiff_level χ r).contMDiff.mdifferentiableAt (by simp))
      (contMDiff_collarProjection.mdifferentiableAt (by simp)), mfderiv_eq_fderiv]
    rfl
  rw [hc]
  change fderiv ℝ (level χ r) (collarProjection p)
    (mfderiv collarModel 𝓘(ℝ, Vector 3 × ℝ) collarProjection p w) = _
  rw [mfderiv_collarProjection_apply]
  have hd : fderiv ℝ (level χ r) (collarProjection p) =
      (fderiv ℝ (SmoothCornerRounding.level χ) (coordinates r (collarProjection p))).comp
        (fderiv ℝ (coordinates r) (collarProjection p)) :=
    fderiv_comp _ ((SmoothCornerRounding.contDiff_level χ).differentiable (by simp) _)
      ((contDiff_coordinates r).differentiable (by simp) _)
  rw [hd]
  change fderiv ℝ (SmoothCornerRounding.level χ) (coordinates r (collarProjection p))
    (fderiv ℝ (coordinates r) (collarProjection p) (w.1.2, w.2)) = _
  rw [fderiv_coordinates_apply]
  rfl

theorem collarDifferential_of_right (χ : ContDiffBump (0 : ℝ)) (r : ℝ) (p : Collar)
    (hp : χ.rOut < p.2 - (r ^ 2 - ‖p.1.2‖ ^ 2)) (w : (Vector 3 × Vector 3) × ℝ) :
    collarDifferential χ r p w = 2 * w.2 := by
  rw [collarDifferential_apply, SmoothCornerRounding.fderiv_level_of_right χ hp]

theorem collarDifferential_of_left (χ : ContDiffBump (0 : ℝ)) (r : ℝ) (p : Collar)
    (hp : p.2 - (r ^ 2 - ‖p.1.2‖ ^ 2) < -χ.rOut) (w : (Vector 3 × Vector 3) × ℝ) :
    collarDifferential χ r p w = -4 * inner ℝ p.1.2 w.1.2 := by
  rw [collarDifferential_apply, SmoothCornerRounding.fderiv_level_of_left χ hp]
  ring

end NoExoticSixSphere.RoundedHandleCorner
