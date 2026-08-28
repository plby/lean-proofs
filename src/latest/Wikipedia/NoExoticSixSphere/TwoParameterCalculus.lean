import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod

/-!
# Coordinate derivatives of a smooth two-parameter family

The partial derivatives here are evaluations of the actual Fréchet derivative
on the two coordinate vectors. Their mixed derivatives agree by Schwarz's
theorem; no independent formal derivative fields are introduced.
-/

open scoped ContDiff

namespace NoExoticSixSphere.TwoParameterCalculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def first (f : ℝ × ℝ → E) (p : ℝ × ℝ) : E :=
  fderiv ℝ f p (1, 0)

noncomputable def second (f : ℝ × ℝ → E) (p : ℝ × ℝ) : E :=
  fderiv ℝ f p (0, 1)

theorem hasDerivAt_first {f : ℝ × ℝ → E} {s t : ℝ}
    (hf : DifferentiableAt ℝ f (s, t)) :
    HasDerivAt (fun r ↦ f (r, t)) (first f (s, t)) s := by
  exact hf.hasFDerivAt.comp_hasDerivAt s
    ((hasDerivAt_id s).prodMk (hasDerivAt_const s t))

theorem hasDerivAt_second {f : ℝ × ℝ → E} {s t : ℝ}
    (hf : DifferentiableAt ℝ f (s, t)) :
    HasDerivAt (fun r ↦ f (s, r)) (second f (s, t)) t := by
  exact hf.hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t s).prodMk (hasDerivAt_id t))

theorem contDiff_first {f : ℝ × ℝ → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (first f) := by
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem contDiff_second {f : ℝ × ℝ → E} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (second f) := by
  exact (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

theorem first_second {f : ℝ × ℝ → E} (hf : ContDiff ℝ ∞ f) (p : ℝ × ℝ) :
    first (second f) p = second (first f) p := by
  have hd : DifferentiableAt ℝ (fderiv ℝ f) p :=
    ((hf.fderiv_right (m := ∞) (by simp)).differentiable (by simp)) p
  have hfirst := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (1, 0) p)
  have hsecond := hd.hasFDerivAt.clm_apply (hasFDerivAt_const (0, 1) p)
  unfold first second
  rw [hfirst.fderiv, hsecond.fderiv]
  have horder : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    simp only [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞)
    exact WithTop.coe_le_coe.mpr le_top
  simpa using (hf.contDiffAt.isSymmSndFDerivAt horder).eq (1, 0) (0, 1)

end NoExoticSixSphere.TwoParameterCalculus
