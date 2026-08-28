import Wikipedia.NoExoticSixSphere.SmoothCompactParameterIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# A smooth symmetric divided difference, including the diagonal

For `h(u,z)`, integrate its actual vertical derivative along the segment
from `m-s` to `m+s`. The resulting function is smooth at `s=0`, equals
the vertical derivative there, is even in `s`, and detects the actual
same-image equation when `s ≠ 0`.
-/

noncomputable section

open Set Function MeasureTheory
open scoped ContDiff

namespace NoExoticSixSphere.SymmetricDifference

variable {U F : Type} [NormedAddCommGroup U] [NormedSpace ℝ U]
  [FiniteDimensional ℝ U] [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

def vertical (h : U × ℝ → F) (q : U × ℝ) : F :=
  fderiv ℝ h q (0, 1)

def dividedDifference (h : U × ℝ → F) (q : (U × ℝ) × ℝ) : F :=
  (2 : ℝ)⁻¹ • ∫ v in (-1 : ℝ)..1, vertical h (q.1.1, q.1.2 + q.2 * v)

omit [FiniteDimensional ℝ U] [CompleteSpace F] in
theorem contDiff_vertical (h : U × ℝ → F) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (vertical h) :=
  (hh.fderiv_right (by simp)).clm_apply contDiff_const

omit [FiniteDimensional ℝ U] [CompleteSpace F] in
theorem hasDerivAt_vertical_slice (h : U × ℝ → F) (hh : ContDiff ℝ ∞ h)
    (u : U) (z : ℝ) :
    HasDerivAt (fun r ↦ h (u, r)) (vertical h (u, z)) z :=
  ((hh.differentiable (by simp) (u, z)).hasFDerivAt).comp_hasDerivAt z
    ((hasDerivAt_const z u).prodMk (hasDerivAt_id z))

theorem contDiff_dividedDifference (h : U × ℝ → F) (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (dividedDifference h) := by
  have hp : ContDiff ℝ ∞
      (fun r : ((U × ℝ) × ℝ) × ℝ ↦ (r.1.1.1, r.1.1.2 + r.1.2 * r.2)) :=
    contDiff_fst.fst.fst.prodMk
      (contDiff_fst.fst.snd.add (contDiff_fst.snd.mul contDiff_snd))
  have hi := CompactParameterIntegral.contDiff_intervalIntegral
    (fun r : ((U × ℝ) × ℝ) × ℝ ↦ vertical h (r.1.1.1, r.1.1.2 + r.1.2 * r.2))
    ((contDiff_vertical h hh).comp hp) (-1) 1 (by norm_num)
  exact hi.const_smul _

omit [FiniteDimensional ℝ U] in
theorem dividedDifference_zero (h : U × ℝ → F) (u : U) (m : ℝ) :
    dividedDifference h ((u, m), 0) = vertical h (u, m) := by
  simp only [dividedDifference, zero_mul, add_zero, intervalIntegral.integral_const, smul_smul]
  norm_num

omit [FiniteDimensional ℝ U] [CompleteSpace F] in
theorem dividedDifference_even (h : U × ℝ → F) (u : U) (m s : ℝ) :
    dividedDifference h ((u, m), -s) = dividedDifference h ((u, m), s) := by
  unfold dividedDifference
  congr 1
  have he : (fun v : ℝ ↦ vertical h (u, m + -s * v)) =
      fun v ↦ (fun w : ℝ ↦ vertical h (u, m + s * w)) (-v) := by
    funext v
    congr 2
    ring
  rw [he]
  simpa only [neg_neg] using
    (intervalIntegral.integral_comp_neg
      (f := fun w : ℝ ↦ vertical h (u, m + s * w)) (a := -1) (b := 1))

omit [FiniteDimensional ℝ U] in
theorem two_mul_smul_dividedDifference (h : U × ℝ → F) (hh : ContDiff ℝ ∞ h)
    (u : U) (m s : ℝ) :
    (2 * s) • dividedDifference h ((u, m), s) = h (u, m + s) - h (u, m - s) := by
  have hder (v : ℝ) : HasDerivAt (fun w : ℝ ↦ h (u, m + s * w))
      (s • vertical h (u, m + s * v)) v := by
    have hv : HasDerivAt (fun w : ℝ ↦ m + s * w) s v := by
      apply (hasDerivAt_const_add_iff m).mpr
      exact hasDerivAt_const_mul s
    exact (hasDerivAt_vertical_slice h hh u (m + s * v)).scomp v hv
  have hvcont : Continuous (fun v : ℝ ↦ vertical h (u, m + s * v)) :=
    (contDiff_vertical h hh).continuous.comp
      (continuous_const.prodMk (continuous_const.add (continuous_const.mul continuous_id)))
  have hc := hvcont.const_smul s
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun v _ ↦ hder v)
    (hc.intervalIntegrable (-1) 1)
  rw [intervalIntegral.integral_smul] at hFTC
  calc
    (2 * s) • dividedDifference h ((u, m), s) =
        s • ∫ v in (-1 : ℝ)..1, vertical h (u, m + s * v) := by
      rw [dividedDifference, smul_smul]
      congr 1
      ring
    _ = h (u, m + s) - h (u, m - s) := by
      simpa only [mul_one, mul_neg_one, sub_eq_add_neg] using hFTC

omit [FiniteDimensional ℝ U] in
theorem dividedDifference_zero_iff (h : U × ℝ → F) (hh : ContDiff ℝ ∞ h)
    (u : U) (m s : ℝ) (hs : s ≠ 0) :
    dividedDifference h ((u, m), s) = 0 ↔ h (u, m + s) = h (u, m - s) := by
  have he := two_mul_smul_dividedDifference h hh u m s
  constructor
  · intro hz
    rw [hz, smul_zero] at he
    exact sub_eq_zero.mp he.symm
  · intro hsame
    rw [hsame, sub_self] at he
    exact (smul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) hs)

omit [FiniteDimensional ℝ U] in
theorem fderiv_zero_slice (h : U × ℝ → F) (q : U × ℝ) :
    fderiv ℝ (fun p : U × ℝ ↦ dividedDifference h (p, 0)) q =
      fderiv ℝ (vertical h) q := by
  have he : (fun p : U × ℝ ↦ dividedDifference h (p, 0)) = vertical h := by
    funext p
    exact dividedDifference_zero h p.1 p.2
  rw [he]

end NoExoticSixSphere.SymmetricDifference
