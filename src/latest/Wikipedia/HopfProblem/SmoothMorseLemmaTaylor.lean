import Wikipedia.HopfProblem.SmoothMorseLemmaTaylorIntegral
import Mathlib.Analysis.Calculus.TaylorIntegral
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# A genuine smooth symmetric second-order Taylor factor

The factor is the weighted integral of the actual Hessian along the segment
from zero to the point. Its smoothness follows from the proved normed-space
parameter-integral theorem, its symmetry from equality of second derivatives,
and its exact factorization from Taylor's theorem with integral remainder.
-/

noncomputable section

open Set MeasureTheory
open scoped ContDiff

namespace Wikipedia.HopfProblem.SmoothMorseLemma

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual weighted Hessian, jointly smooth in point and time. -/
def taylorHessianIntegrand (f : E → ℝ) (q : E × ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  (1 - q.2) • fderiv ℝ (fderiv ℝ f) (q.2 • q.1)

/-- The normalized second-order Taylor factor, defined by a genuine integral. -/
def secondTaylorFactor (f : E → ℝ) (x : E) : E →L[ℝ] E →L[ℝ] ℝ :=
  (2 : ℝ) • ∫ t in (0 : ℝ)..1, taylorHessianIntegrand f (x, t)

theorem contDiff_taylorHessianIntegrand {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (taylorHessianIntegrand f) := by
  let : IsBoundedSMul ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
    .of_norm_smul_le (fun c B => norm_smul_le c B)
  have hdf : ContDiff ℝ ∞ (fderiv ℝ f) := (contDiff_infty_iff_fderiv.mp hf).2
  have hH : ContDiff ℝ ∞ (fderiv ℝ (fderiv ℝ f)) :=
    (contDiff_infty_iff_fderiv.mp hdf).2
  exact (contDiff_const.sub contDiff_snd).smul
    (hH.comp (contDiff_snd.smul contDiff_fst))

/-- The integral factor is globally smooth, not merely continuous at zero. -/
theorem contDiff_secondTaylorFactor {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (secondTaylorFactor f) :=
  (contDiff_parametric_intervalIntegral (taylorHessianIntegrand f)
    (contDiff_taylorHessianIntegrand hf) 0 1).const_smul (2 : ℝ)

/-- Evaluation of the bilinear integral is the actual scalar Hessian integral. -/
theorem secondTaylorFactor_apply {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x u v : E) :
    secondTaylorFactor f x u v =
      2 * ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) u v := by
  have hc : Continuous (fun t : ℝ => taylorHessianIntegrand f (x, t)) :=
    (contDiff_taylorHessianIntegrand hf).continuous.comp (continuous_const.prodMk continuous_id)
  have hi : IntervalIntegrable (fun t : ℝ => taylorHessianIntegrand f (x, t)) volume 0 1 :=
    hc.intervalIntegrable 0 1
  have hiu : IntervalIntegrable (fun t : ℝ => taylorHessianIntegrand f (x, t) u) volume 0 1 :=
    (hc.clm_apply continuous_const).intervalIntegrable 0 1
  simp only [secondTaylorFactor, smul_apply]
  rw [ContinuousLinearMap.intervalIntegral_apply hi u,
    ContinuousLinearMap.intervalIntegral_apply hiu v]
  simp only [taylorHessianIntegrand, smul_apply, smul_eq_mul]

/-- The normalized factor agrees exactly with the actual Hessian at zero. -/
theorem secondTaylorFactor_zero (f : E → ℝ) :
    secondTaylorFactor f 0 = fderiv ℝ (fderiv ℝ f) 0 := by
  have hw : (∫ t in (0 : ℝ)..1, (1 - t)) = (1 / 2 : ℝ) := by
    calc
      (∫ t in (0 : ℝ)..1, (1 - t)) =
          (∫ _t in (0 : ℝ)..1, (1 : ℝ)) - ∫ t in (0 : ℝ)..1, t :=
        intervalIntegral.integral_sub (f := fun _ : ℝ => (1 : ℝ)) (g := fun t : ℝ => t)
          intervalIntegrable_const (continuous_id.intervalIntegrable 0 1)
      _ = 1 / 2 := by norm_num [integral_id]
  have hz : (∫ t in (0 : ℝ)..1, (1 - t) • fderiv ℝ (fderiv ℝ f) 0) =
      (1 / 2 : ℝ) • fderiv ℝ (fderiv ℝ f) 0 :=
    (intervalIntegral.integral_smul_const (fun t : ℝ => 1 - t)
      (fderiv ℝ (fderiv ℝ f) 0)).trans
        (congrArg (fun c : ℝ => c • fderiv ℝ (fderiv ℝ f) 0) hw)
  simp only [secondTaylorFactor, taylorHessianIntegrand, smul_zero]
  exact (congrArg (fun B : E →L[ℝ] E →L[ℝ] ℝ => (2 : ℝ) • B) hz).trans
    (by norm_num [smul_smul])

/-- Every value of the integral factor is a genuinely symmetric bilinear map. -/
theorem secondTaylorFactor_symmetric {f : E → ℝ} (hf : ContDiff ℝ ∞ f) (x u v : E) :
    secondTaylorFactor f x u v = secondTaylorFactor f x v u := by
  rw [secondTaylorFactor_apply hf, secondTaylorFactor_apply hf]
  apply congrArg (fun r : ℝ => 2 * r)
  apply intervalIntegral.integral_congr
  intro t _
  have hs : IsSymmSndFDerivAt ℝ f (t • x) :=
    hf.contDiffAt.isSymmSndFDerivAt (by
      simp only [minSmoothness_of_isRCLikeNormedField]
      change (↑(2 : ℕ∞) : ℕ∞ω) ≤ ↑(⊤ : ℕ∞)
      exact WithTop.coe_le_coe.mpr le_top)
  exact congrArg (fun r : ℝ => (1 - t) * r) (hs u v)

/-- The exact global second-order expansion in the constructed smooth factor. -/
theorem map_eq_add_linear_add_secondTaylorFactor {f : E → ℝ}
    (hf : ContDiff ℝ ∞ f) (x : E) :
    f x = f 0 + fderiv ℝ f 0 x + (1 / 2 : ℝ) * secondTaylorFactor f x x x := by
  have ht := map_add_eq_sum_add_integral_iteratedFDeriv
    (f := f) (x := 0) (y := x) (n := 1)
    (fun t _ => hf.contDiffAt.of_le (ENat.natCast_le_of_coe_top_le_withTop le_rfl 2))
  have ht' : f x = f 0 + fderiv ℝ f 0 x +
      ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) x x := by
    simpa [Finset.sum_range_succ, iteratedFDeriv_two_apply, smul_eq_mul] using ht
  rw [secondTaylorFactor_apply hf]
  calc
    f x = f 0 + fderiv ℝ f 0 x +
        ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) x x := ht'
    _ = f 0 + fderiv ℝ f 0 x + (1 / 2 : ℝ) *
        (2 * ∫ t in (0 : ℝ)..1, (1 - t) * fderiv ℝ (fderiv ℝ f) (t • x) x x) := by ring

/-- The genuine second-order Hadamard factorization. The only analytic
hypothesis is global real smoothness of the original function. -/
theorem exists_smooth_symmetric_taylor_factor {f : E → ℝ} (hf : ContDiff ℝ ∞ f) :
    ∃ A : E → E →L[ℝ] E →L[ℝ] ℝ,
      ContDiff ℝ ∞ A ∧ A 0 = fderiv ℝ (fderiv ℝ f) 0 ∧
      (∀ x u v, A x u v = A x v u) ∧
      ∀ x, f x = f 0 + fderiv ℝ f 0 x + (1 / 2 : ℝ) * A x x x :=
  ⟨secondTaylorFactor f, contDiff_secondTaylorFactor hf, secondTaylorFactor_zero f,
    secondTaylorFactor_symmetric hf, map_eq_add_linear_add_secondTaylorFactor hf⟩

end Wikipedia.HopfProblem.SmoothMorseLemma
