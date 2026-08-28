import Wikipedia.NoExoticSixSphere.SecondDerivativeUpperBound
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Derivatives and energy bounds along affine lines

The second derivative of an affine-line restriction is the actual Hessian
evaluated twice on the fixed direction. A uniform Hessian bound therefore
gives a quantitative quadratic estimate along any segment in the smooth domain.
-/

open Set
open scoped ContDiff

namespace NoExoticSixSphere.AffineLineSecondDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem hasDerivAt_line (p v : E) (s : ℝ) : HasDerivAt (fun t : ℝ ↦ p + t • v) v s := by
  simpa only [one_smul] using! ((hasDerivAt_id s).smul_const v).const_add p

theorem hasDerivAt_comp (f : E → ℝ) (p v : E) (s : ℝ)
    (hf : DifferentiableAt ℝ f (p + s • v)) :
    HasDerivAt (fun t : ℝ ↦ f (p + t • v)) (fderiv ℝ f (p + s • v) v) s :=
  hf.hasFDerivAt.comp_hasDerivAt s (hasDerivAt_line p v s)

theorem hasDerivAt_differential (f : E → ℝ) (p v : E) (s : ℝ)
    (hf : ContDiffAt ℝ 2 f (p + s • v)) :
    HasDerivAt (fun t : ℝ ↦ fderiv ℝ f (p + t • v) v)
      (fderiv ℝ (fderiv ℝ f) (p + s • v) v v) s := by
  have hd : ContDiffAt ℝ 1 (fderiv ℝ f) (p + s • v) := hf.fderiv_right (by norm_num)
  have hh := (hd.differentiableAt one_ne_zero).hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_line p v s)
  simpa only [map_zero, add_zero] using! hh.clm_apply (hasDerivAt_const s v)

theorem quadratic_upper (f : E → ℝ) (p v : E) (U : Set E) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (A T : ℝ) (hT : 0 ≤ T)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, p + t • v ∈ U)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T,
      fderiv ℝ (fderiv ℝ f) (p + t • v) v v ≤ -A) :
    f (p + T • v) ≤ f p + fderiv ℝ f p v * T - (A / 2) * T ^ 2 := by
  have hs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ContDiffAt ℝ 2 f (p + t • v) :=
    hf.contDiffAt (hU.mem_nhds (hseg t ht))
  have hh := SecondDerivativeUpperBound.quadratic_upper hT
    (fun t ht ↦ hasDerivAt_comp f p v t ((hs t ht).differentiableAt (by norm_num)))
    (fun t ht ↦ hasDerivAt_differential f p v t (hs t ht)) hbound
  simpa only [zero_smul, add_zero] using hh

theorem quadratic_secant_upper (f : E → ℝ) (p v : E) (U : Set E) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (A T : ℝ) (hT : 0 ≤ T)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, p + t • v ∈ U)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T,
      fderiv ℝ (fderiv ℝ f) (p + t • v) v v ≤ -A)
    {s t : ℝ} (hs : s ∈ Icc (0 : ℝ) T) (ht : t ∈ Icc (0 : ℝ) T) (hst : s ≤ t) :
    f (p + t • v) ≤ f (p + s • v) + fderiv ℝ f p v * (t - s) -
      (A / 2) * (t ^ 2 - s ^ 2) := by
  have hsmooth (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ContDiffAt ℝ 2 f (p + t • v) :=
    hf.contDiffAt (hU.mem_nhds (hseg t ht))
  have hh := SecondDerivativeUpperBound.quadratic_secant_upper hT
    (fun t ht ↦ hasDerivAt_comp f p v t ((hsmooth t ht).differentiableAt (by norm_num)))
    (fun t ht ↦ hasDerivAt_differential f p v t (hsmooth t ht)) hbound hs ht hst
  simpa only [zero_smul, add_zero] using hh

theorem strictAntiOn (f : E → ℝ) (p v : E) (U : Set E) (hU : IsOpen U)
    (hf : ContDiffOn ℝ 2 f U) (A T : ℝ) (hT : 0 ≤ T) (hA : 0 < A)
    (hseg : ∀ t ∈ Icc (0 : ℝ) T, p + t • v ∈ U)
    (hbound : ∀ t ∈ Icc (0 : ℝ) T,
      fderiv ℝ (fderiv ℝ f) (p + t • v) v v ≤ -A)
    (hzero : fderiv ℝ f p v = 0) :
    StrictAntiOn (fun t : ℝ ↦ f (p + t • v)) (Icc (0 : ℝ) T) := by
  have hs (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ContDiffAt ℝ 2 f (p + t • v) :=
    hf.contDiffAt (hU.mem_nhds (hseg t ht))
  apply SecondDerivativeUpperBound.strictAntiOn_of_negative_second hT hA
    (fun t ht ↦ hasDerivAt_comp f p v t ((hs t ht).differentiableAt (by norm_num)))
    (fun t ht ↦ hasDerivAt_differential f p v t (hs t ht)) hbound
  simpa only [zero_smul, add_zero] using hzero

end NoExoticSixSphere.AffineLineSecondDerivative
