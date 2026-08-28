import Wikipedia.SmoothSixDPoincare.StripCenterImmersion
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# A normal zero-set detector for the constructed strip

Pair the arc parameter with the inner product of the prescribed normal field
and the strip's normal coordinate. The resulting planar map is immersive
along the center. Its local injectivity will show that zero normal coordinate
occurs only on the center, after shrinking the strip.
-/

noncomputable section

open Function
open scoped ContDiff InnerProductSpace

namespace Wikipedia.SmoothSixDPoincare.StripCoordinates

theorem injective_plane_of_horizontal_and_normal (L : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ))
    (hh : L (1, 0) = (1, 0)) (hn : (L (0, 1)).2 ≠ 0) : Injective L := by
  let i : (ℝ × ℝ) →L[ℝ] Space ℝ ℝ :=
    ((ContinuousLinearMap.fst ℝ ℝ ℝ).prod 0).prod (ContinuousLinearMap.snd ℝ ℝ ℝ)
  have hh' : (i.comp L) (1, 0) = center 1 := by
    change i (L (1, 0)) = center 1
    rw [hh]
    rfl
  have hi := injective_of_horizontal_and_normal (i.comp L) hh' hn
  intro p q hpq
  exact hi (congrArg i hpq)

variable {A B : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [InnerProductSpace ℝ B]

def detector (v : ℝ → B) (F : (ℝ × ℝ) → Space A B) (p : ℝ × ℝ) : ℝ × ℝ :=
  (p.1, ⟪v p.1, (F p).2⟫_ℝ)

theorem contDiff_detector {v : ℝ → B} {F : (ℝ × ℝ) → Space A B}
    (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F) : ContDiff ℝ ∞ (detector v F) :=
  contDiff_fst.prodMk ((hv.comp contDiff_fst).inner ℝ hF.snd)

omit [NormedSpace ℝ A] in
theorem detector_zero {v : ℝ → B} {F : (ℝ × ℝ) → Space A B}
    (hc : ∀ t, F (t, 0) = center t) (t : ℝ) : detector v F (t, 0) = (t, 0) := by
  simp only [detector, hc, center, inner_zero_right]

theorem detector_vertical_derivative {v : ℝ → B} {F : (ℝ × ℝ) → Space A B}
    (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    (hn : ∀ t, normalDerivative F t = v t) (t : ℝ) :
    fderiv ℝ (detector v F) (t, 0) (0, 1) = (0, ⟪v t, v t⟫_ℝ) := by
  have hd : HasDerivAt (fun s : ℝ => (F (t, s)).2) (v t) 0 := by
    have h := hasDerivAt_verticalSlice (t := t) (s := 0)
      (hF.snd.contDiffAt.differentiableAt (by simp))
    change HasDerivAt _ (normalDerivative F t) 0 at h
    rwa [hn t] at h
  have hinner : HasDerivAt (fun s : ℝ => ⟪v t, (F (t, s)).2⟫_ℝ) ⟪v t, v t⟫_ℝ 0 := by
    simpa only [inner_zero_left, add_zero] using (hasDerivAt_const (0 : ℝ) (v t)).inner ℝ hd
  have hslice : HasDerivAt (fun s : ℝ => detector v F (t, s)) (0, ⟪v t, v t⟫_ℝ) 0 :=
    (hasDerivAt_const (0 : ℝ) t).prodMk hinner
  exact (hasDerivAt_verticalSlice
    ((contDiff_detector hv hF).contDiffAt.differentiableAt (by simp))).unique hslice

/-- The actual detector is locally injective at every center point with nonzero normal field. -/
theorem injective_fderiv_detector_at_center {v : ℝ → B} {F : (ℝ × ℝ) → Space A B}
    (hv : ContDiff ℝ ∞ v) (hF : ContDiff ℝ ∞ F)
    (hc : ∀ t, F (t, 0) = center t) (hn : ∀ t, normalDerivative F t = v t)
    {t : ℝ} (ht : v t ≠ 0) : Injective (fderiv ℝ (detector v F) (t, 0)) := by
  have hQ : DifferentiableAt ℝ (detector v F) (t, 0) :=
    (contDiff_detector hv hF).contDiffAt.differentiableAt (by simp)
  have hh : fderiv ℝ (detector v F) (t, 0) (1, 0) = (1, 0) := by
    have hd := hasDerivAt_horizontalSlice hQ
    have heq : (fun s : ℝ => detector v F (s, 0)) = fun s => (s, 0) :=
      funext (detector_zero hc)
    rw [heq] at hd
    exact hd.unique ((hasDerivAt_id t).prodMk (hasDerivAt_const t (0 : ℝ)))
  apply injective_plane_of_horizontal_and_normal _ hh
  rw [detector_vertical_derivative hv hF hn t]
  exact inner_self_ne_zero.mpr ht

end Wikipedia.SmoothSixDPoincare.StripCoordinates
