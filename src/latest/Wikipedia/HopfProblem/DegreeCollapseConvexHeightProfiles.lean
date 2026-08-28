import Wikipedia.HopfProblem.DegreeCollapseSupportedIntervalTranslation
import Mathlib.Geometry.Manifold.Algebra.Structures

/-!
# Smooth convex scalar profiles along invariant orbit labels

Blending two increasing height profiles by a weight in [0,1] retains
positive height derivative and every common exterior value. For a weight
stationary along an actual curve, the derivative is the positive blended
slope times the original height derivative. Native smoothness is retained.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement

def blendHeight (θ : ℝ) (P Q : ℝ → ℝ) (s : ℝ) : ℝ :=
  θ * P s + (1 - θ) * Q s

theorem blendHeight_zero (P Q : ℝ → ℝ) (s : ℝ) : blendHeight 0 P Q s = Q s := by
  simp [blendHeight]

theorem blendHeight_one (P Q : ℝ → ℝ) (s : ℝ) : blendHeight 1 P Q s = P s := by
  simp [blendHeight]

theorem blendHeight_fixed {P Q : ℝ → ℝ} {s : ℝ} (hP : P s = s) (hQ : Q s = s)
    (θ : ℝ) : blendHeight θ P Q s = s := by
  rw [blendHeight, hP, hQ]
  ring

theorem positive_blended_slope {θ a b : ℝ} (hθ : θ ∈ Icc 0 1) (ha : 0 < a) (hb : 0 < b) :
    0 < θ * a + (1 - θ) * b := by
  by_cases hzero : θ = 0
  · simpa only [hzero, zero_mul, sub_zero, one_mul, zero_add] using hb
  · exact add_pos_of_pos_of_nonneg (mul_pos (lt_of_le_of_ne hθ.1 (Ne.symm hzero)) ha)
      (mul_nonneg (sub_nonneg.mpr hθ.2) hb.le)

theorem hasDerivAt_blended_height {f θ P Q : ℝ → ℝ} {t f' p' q' : ℝ}
    (hf : HasDerivAt f f' t) (hθ : HasDerivAt θ 0 t)
    (hP : HasDerivAt P p' (f t)) (hQ : HasDerivAt Q q' (f t)) :
    HasDerivAt (fun s => blendHeight (θ s) P Q (f s))
      ((θ t * p' + (1 - θ t) * q') * f') t := by
  convert! (hθ.mul (hP.comp t hf)).add
    (((hasDerivAt_const t (1 : ℝ)).sub hθ).mul (hQ.comp t hf)) using 1
  simp only [Pi.sub_apply]
  ring

theorem blended_height_derivative_negative {f θ P Q : ℝ → ℝ} {t f' p' q' : ℝ}
    (hf : HasDerivAt f f' t) (hθ : HasDerivAt θ 0 t)
    (hP : HasDerivAt P p' (f t)) (hQ : HasDerivAt Q q' (f t))
    (hw : θ t ∈ Icc 0 1) (hp : 0 < p') (hq : 0 < q') (hdesc : f' < 0) :
    deriv (fun s => blendHeight (θ s) P Q (f s)) t < 0 := by
  rw [(hasDerivAt_blended_height hf hθ hP hQ).deriv]
  exact mul_neg_of_pos_of_neg (positive_blended_slope hw hp hq) hdesc

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

theorem contMDiff_blended_height {f θ : M → ℝ} {P Q : ℝ → ℝ}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hθ : ContMDiff I 𝓘(ℝ, ℝ) ∞ θ)
    (hP : ContDiff ℝ ∞ P) (hQ : ContDiff ℝ ∞ Q) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x => blendHeight (θ x) P Q (f x)) :=
  (hθ.mul (hP.contMDiff.comp hf)).add
    ((contMDiff_const.sub hθ).mul (hQ.contMDiff.comp hf))

end Wikipedia.HopfProblem.DegreeCollapse.MorseRearrangement
