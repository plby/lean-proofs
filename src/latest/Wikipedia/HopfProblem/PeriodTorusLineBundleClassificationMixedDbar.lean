import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationDbar
import Mathlib.Analysis.Calculus.FDeriv.Symmetric

/-!
# Mixed antiholomorphic derivatives on the universal-cover coordinates

The closedness of an actual antiholomorphic differential follows from the
symmetry of the second real Fréchet derivative.  This does not introduce a
formal closedness axiom for smooth forms.
-/

noncomputable section

open Complex
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

theorem fderiv_dbarFirst_apply {f : ℂ × ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (q v : ℂ × ℂ) :
    fderiv ℝ (dbarFirst f) q v =
      dbarFirstLinear (fderiv ℝ (fderiv ℝ f) q v) := by
  have he : dbarFirst f = dbarFirstLinear ∘ fderiv ℝ f :=
    funext (fun x => dbarFirst_eq_linear ((hf.differentiable (by simp)) x))
  have hd := ((contDiff_infty_iff_fderiv.mp hf).2.differentiable (by simp)) q
  rw [he, (dbarFirstLinear.hasFDerivAt.comp q hd.hasFDerivAt).fderiv]
  rfl

theorem fderiv_dbarSecond_apply {f : ℂ × ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (q v : ℂ × ℂ) :
    fderiv ℝ (dbarSecond f) q v =
      dbarSecondLinear (fderiv ℝ (fderiv ℝ f) q v) := by
  have he : dbarSecond f = dbarSecondLinear ∘ fderiv ℝ f :=
    funext (fun x => dbarSecond_eq_linear ((hf.differentiable (by simp)) x))
  have hd := ((contDiff_infty_iff_fderiv.mp hf).2.differentiable (by simp)) q
  rw [he, (dbarSecondLinear.hasFDerivAt.comp q hd.hasFDerivAt).fderiv]
  rfl

/-- The two antiholomorphic coordinate derivatives commute for actual smooth
functions, by the real Schwarz theorem. -/
theorem dbarFirst_dbarSecond {f : ℂ × ℂ → ℂ}
    (hf : ContDiff ℝ ∞ f) (q : ℂ × ℂ) :
    dbarFirst (dbarSecond f) q = dbarSecond (dbarFirst f) q := by
  rw [dbarFirst_eq_linear
      (((contDiff_dbarSecond hf).differentiable (by simp)) q),
    dbarSecond_eq_linear
      (((contDiff_dbarFirst hf).differentiable (by simp)) q)]
  simp only [dbarFirstLinear_apply, dbarSecondLinear_apply,
    fderiv_dbarFirst_apply hf, fderiv_dbarSecond_apply hf]
  have hs := (hf.contDiffAt (x := q)).isSymmSndFDerivAt (by
    simp only [minSmoothness_of_isRCLikeNormedField]
    change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top)
  rw [hs (1, 0) (0, 1), hs (1, 0) (0, I), hs (I, 0) (0, 1), hs (I, 0) (0, I)]
  ring

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
