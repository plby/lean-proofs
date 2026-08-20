/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos980.NaturalChebotarev.ContinuedZeta.Basic

/-!
# Horizontal bounds for the continued Dedekind zeta function

These are the three local estimates used by the `3-4-1` proof of nonvanishing on
`Re s = 1`: a simple-pole bound at `1`, first-order vanishing at a hypothetical zero
`1 + I*y`, and boundedness at `1 + 2*I*y`.
-/

namespace Erdos980.NaturalChebotarev.ContinuedZeta

open Complex Asymptotics Filter NumberField
open scoped Topology

noncomputable section

variable (K : Type*) [Field K] [NumberField K]

private lemma one_add_I_mul_ne_zero {y : ℝ} : (1 + I * y : ℂ) ≠ 0 := by
  intro h
  have hre := congrArg Complex.re h
  norm_num at hre

private lemma one_add_I_mul_ne_one {y : ℝ} (hy : y ≠ 0) :
    (1 + I * y : ℂ) ≠ 1 := by
  simpa only [ne_eq, add_eq_left, mul_eq_zero, I_ne_zero, ofReal_eq_zero, false_or]
    using hy

/-- On every horizontal ray entering the half-plane `Re s > 1`, the continued and raw
Dedekind zeta functions agree. -/
theorem continuedDedekindZeta_eq_dedekindZeta_one_add
    {x y : ℝ} (hx : 0 < x) :
    continuedDedekindZeta K (1 + x + I * y) =
      dedekindZeta K (1 + x + I * y) := by
  apply continuedDedekindZeta_eq_dedekindZeta K
  simp only [add_re, one_re, ofReal_re, mul_re, I_re, zero_mul, I_im, ofReal_im,
    mul_zero, sub_zero]
  linarith

/-- The raw Dedekind zeta function has at most simple-pole growth on the real ray entering
`s = 1`. -/
theorem dedekindZeta_isBigO_near_one_horizontal :
    (fun x : ℝ ↦ dedekindZeta K (1 + x)) =O[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      fun x ↦ (1 : ℂ) / x := by
  let R := continuedDedekindZetaOneRegularized K
  have hR : (fun x : ℝ ↦ R (1 + x)) =O[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      fun _ ↦ (1 : ℂ) := by
    have hcont :=
      (differentiableAt_continuedDedekindZetaOneRegularized
        K (s := (1 : ℂ)) one_ne_zero).continuousAt
    have hmap : ContinuousAt (fun x : ℝ ↦ (1 : ℂ) + x) 0 :=
      Complex.continuous_ofReal.continuousAt.const_add 1
    have hc := hcont.comp_of_eq hmap (by simp)
    exact (show ContinuousAt (fun x : ℝ ↦ R (1 + x)) 0 by
      simpa only [R, Function.comp_def] using hc).isBigO.mono nhdsWithin_le_nhds
  have hprod := hR.mul
    (isBigO_refl (fun x : ℝ ↦ (1 : ℂ) / x) (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
  refine hprod.congr' ?_ (Eventually.of_forall fun x ↦ by simp)
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxpos : 0 < x := hx
  have hx0 : x ≠ 0 := hx.ne'
  have hs0 : (1 + x : ℂ) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hs1 : (1 + x : ℂ) ≠ 1 := by
    exact sub_ne_zero.mp (by simpa using (ofReal_ne_zero.mpr hx0))
  rw [show R (1 + x) = ((1 + x : ℂ) - 1) * continuedDedekindZeta K (1 + x) by
    exact continuedDedekindZetaOneRegularized_eq K hs0 hs1]
  rw [show continuedDedekindZeta K (1 + x) = dedekindZeta K (1 + x) by
    simpa using continuedDedekindZeta_eq_dedekindZeta_one_add K (y := 0) hxpos]
  simp only [add_sub_cancel_left]
  rw [one_div]
  calc
    (x : ℂ) * dedekindZeta K (1 + x) * (x : ℂ)⁻¹ =
        dedekindZeta K (1 + x) * ((x : ℂ)⁻¹ * x) := by ring
    _ = dedekindZeta K (1 + x) := by
      rw [inv_mul_cancel₀ (ofReal_ne_zero.mpr hx0), mul_one]

/-- A horizontal translate of the raw Dedekind zeta function is bounded near the line
`Re s = 1`, provided its boundary point is not the pole. -/
theorem dedekindZeta_isBigO_horizontal {y : ℝ} (hy : y ≠ 0) :
    (fun x : ℝ ↦ dedekindZeta K (1 + x + I * y)) =O[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      fun _ ↦ (1 : ℂ) := by
  let s : ℂ := 1 + I * y
  have hs0 : s ≠ 0 := one_add_I_mul_ne_zero
  have hs1 : s ≠ 1 := one_add_I_mul_ne_one hy
  have hcont := (differentiableAt_continuedDedekindZeta K hs0 hs1).continuousAt
  have H : (fun x : ℝ ↦ continuedDedekindZeta K (s + x))
      =O[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      fun _ ↦ (1 : ℂ) := by
    have hmap : ContinuousAt (fun x : ℝ ↦ s + x) 0 :=
      Complex.continuous_ofReal.continuousAt.const_add s
    have hc := hcont.comp_of_eq hmap (by simp)
    exact (show ContinuousAt (fun x : ℝ ↦ continuedDedekindZeta K (s + x)) 0 by
      simpa only [Function.comp_def] using hc).isBigO.mono nhdsWithin_le_nhds
  refine H.congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxpos : 0 < x := hx
  have hre : 1 < (s + x).re := by
    simp only [s, add_re, one_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
      sub_zero, ofReal_re]
    linarith
  rw [continuedDedekindZeta_eq_dedekindZeta K hre]
  congr 1
  dsimp [s]
  ring

/-- If the continuation vanished at `1 + I*y`, its raw values on the adjacent horizontal
ray would vanish to first order. -/
theorem dedekindZeta_isBigO_horizontal_of_eq_zero
    {y : ℝ} (hy : y ≠ 0)
    (hzero : continuedDedekindZeta K (1 + I * y) = 0) :
    (fun x : ℝ ↦ dedekindZeta K (1 + x + I * y)) =O[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      fun x ↦ (x : ℂ) := by
  let s : ℂ := 1 + I * y
  have hs0 : s ≠ 0 := one_add_I_mul_ne_zero
  have hs1 : s ≠ 1 := one_add_I_mul_ne_one hy
  have hdiff := (differentiableAt_continuedDedekindZeta K hs0 hs1).hasDerivAt
  have H : (fun x : ℝ ↦ continuedDedekindZeta K (s + x))
      =O[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      fun x ↦ (x : ℂ) := by
    have hdiff' : HasDerivAt (continuedDedekindZeta K)
        (deriv (continuedDedekindZeta K) s) (s + 0) := by
      simpa using hdiff
    have H' := Complex.isBigO_comp_ofReal_nhds
      ((hdiff'.comp_const_add s 0).differentiableAt.isBigO_sub)
    simpa only [add_zero, hzero, sub_zero, s] using H'.mono nhdsWithin_le_nhds
  refine H.congr' ?_ EventuallyEq.rfl
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxpos : 0 < x := hx
  have hre : 1 < (s + x).re := by
    simp only [s, add_re, one_re, mul_re, I_re, zero_mul, I_im, ofReal_im, mul_zero,
      sub_zero, ofReal_re]
    linarith
  rw [continuedDedekindZeta_eq_dedekindZeta K hre]
  congr 1
  dsimp [s]
  ring

/-- The third factor in the `3-4-1` product is bounded on its horizontal ray. -/
theorem dedekindZeta_isBigO_two_mul_horizontal {y : ℝ} (hy : y ≠ 0) :
    (fun x : ℝ ↦ dedekindZeta K (1 + x + 2 * I * y))
      =O[nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      fun _ ↦ (1 : ℂ) := by
  have H := dedekindZeta_isBigO_horizontal K (mul_ne_zero two_ne_zero hy)
  refine H.congr' (Eventually.of_forall fun x ↦ ?_) EventuallyEq.rfl
  apply congrArg (dedekindZeta K)
  push_cast
  ring

end

end Erdos980.NaturalChebotarev.ContinuedZeta
