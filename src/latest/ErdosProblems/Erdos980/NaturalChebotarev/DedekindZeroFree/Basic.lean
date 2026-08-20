/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos980.NaturalChebotarev.DedekindNormProduct
import ErdosProblems.Erdos980.NaturalChebotarev.ContinuedZeta.Basic

/-!
# Boundary nonvanishing of the continued Dedekind zeta function

This file applies the de la Vallée Poussin `3-4-1` norm-product inequality to the
analytic continuation of the Dedekind zeta function. It proves that the continuation
has no zero on `Re s = 1` away from its pole at `1`.
-/

namespace Erdos980.NaturalChebotarev.DedekindZeroFree

open Complex Filter NumberField Topology Asymptotics
open ContinuedZeta

noncomputable section

private lemma tendsto_one_add_nhdsGT_zero :
    Tendsto (fun x : ℝ ↦ 1 + x) (𝓝[>] (0 : ℝ)) (𝓝[>] (1 : ℝ)) := by
  have hcont : Tendsto (fun x : ℝ ↦ 1 + x) (𝓝 (0 : ℝ)) (𝓝 (1 : ℝ)) := by
    simpa using (tendsto_const_nhds.add tendsto_id :
      Tendsto (fun x : ℝ ↦ 1 + x) (𝓝 (0 : ℝ)) (𝓝 ((1 : ℝ) + 0)))
  refine tendsto_nhdsWithin_iff.mpr ⟨hcont.mono_left nhdsWithin_le_nhds, ?_⟩
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  change 1 < 1 + x
  linarith

/-- The real Dedekind zeta function has at most its known simple-pole growth as
`x → 0⁺`. -/
private lemma dedekindZeta_isBigO_near_one_horizontal
    (K : Type*) [Field K] [NumberField K] :
    (fun x : ℝ ↦ NumberField.dedekindZeta K (1 + x)) =O[𝓝[>] 0]
      fun x ↦ (1 : ℂ) / x := by
  have hlim : Tendsto
      (fun x : ℝ ↦ (x : ℂ) * NumberField.dedekindZeta K (1 + x))
      (𝓝[>] 0) (𝓝 (NumberField.dedekindZeta_residue K)) := by
    convert (NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K).comp
      tendsto_one_add_nhdsGT_zero using 1
    funext x
    simp only [Function.comp_apply]
    push_cast
    ring
  refine (isBigO_mul_iff_isBigO_div (l := 𝓝[>] 0)
    (f := fun x : ℝ ↦ (x : ℂ)) (g := fun x ↦ NumberField.dedekindZeta K (1 + x))
    (h := fun _ ↦ (1 : ℂ)) ?_).mp (hlim.isBigO_one ℂ)
  filter_upwards [self_mem_nhdsWithin] with x hx
  exact ofReal_ne_zero.mpr (ne_of_gt hx)

private lemma continuedDedekindZeta_isBigO_horizontal_of_eq_zero
    (K : Type*) [Field K] [NumberField K] {y : ℝ}
    (hy : y ≠ 0) (hzero : continuedDedekindZeta K (1 + I * y) = 0) :
    (fun x : ℝ ↦ continuedDedekindZeta K (1 + x + I * y)) =O[𝓝[>] 0]
      fun x : ℝ ↦ (x : ℂ) := by
  simp_rw [add_comm (1 : ℂ), add_assoc]
  have hs0 : (1 : ℂ) + I * y ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hs1 : (1 : ℂ) + I * y ≠ 1 := by
    simpa only [ne_eq, add_eq_left, mul_eq_zero, I_ne_zero, ofReal_eq_zero, false_or]
      using hy
  have hder := (differentiableAt_continuedDedekindZeta K hs0 hs1).hasDerivAt
  rw [← zero_add (1 + I * y)] at hder
  simpa only [zero_add, hzero, sub_zero] using
    (Complex.isBigO_comp_ofReal_nhds
      (hder.comp_add_const 0 _).differentiableAt.isBigO_sub).mono nhdsWithin_le_nhds

private lemma continuedDedekindZeta_isBigO_horizontal
    (K : Type*) [Field K] [NumberField K] {y : ℝ} (hy : y ≠ 0) :
    (fun x : ℝ ↦ continuedDedekindZeta K (1 + x + I * y)) =O[𝓝[>] 0]
      fun _ ↦ (1 : ℂ) := by
  simp_rw [add_comm (1 : ℂ), add_assoc]
  have hs0 : (1 : ℂ) + I * y ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    norm_num at this
  have hs1 : (1 : ℂ) + I * y ≠ 1 := by
    simpa only [ne_eq, add_eq_left, mul_eq_zero, I_ne_zero, ofReal_eq_zero, false_or]
      using hy
  have hcont := (differentiableAt_continuedDedekindZeta K hs0 hs1).continuousAt
  rw [← zero_add (1 + I * y)] at hcont
  exact (hcont.comp (f := fun x : ℝ ↦ x + (1 + I * y)) (x := 0) (by fun_prop)).tendsto
    |>.isBigO_one ℂ |>.mono nhdsWithin_le_nhds

private lemma dedekindZeta_eventuallyEq_continued_horizontal
    (K : Type*) [Field K] [NumberField K] (y : ℝ) :
    (fun x : ℝ ↦ NumberField.dedekindZeta K (1 + x + I * y)) =ᶠ[𝓝[>] 0]
      fun x ↦ continuedDedekindZeta K (1 + x + I * y) := by
  filter_upwards [self_mem_nhdsWithin] with x hx
  rw [continuedDedekindZeta_eq_dedekindZeta K]
  simpa using hx

/-- The meromorphic continuation of `ζ_K` has no zero on the line `Re s = 1`,
away from its simple pole at `s = 1`. -/
theorem continuedDedekindZeta_ne_zero_of_re_eq_one
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs : s.re = 1) (hs1 : s ≠ 1) :
    continuedDedekindZeta K s ≠ 0 := by
  have hsrepr : s = 1 + I * s.im := by
    conv_lhs => rw [← re_add_im s, hs, ofReal_one, mul_comm]
  have hy : s.im ≠ 0 := by
    intro hy
    apply hs1
    rw [hsrepr, hy]
    norm_num
  rw [hsrepr]
  intro hzero
  have H₀ : (fun _ : ℝ ↦ (1 : ℝ)) =O[𝓝[>] 0]
      fun x ↦ NumberField.dedekindZeta K (1 + x) ^ 3
        * NumberField.dedekindZeta K (1 + x + I * s.im) ^ 4
        * NumberField.dedekindZeta K (1 + x + 2 * I * s.im) :=
    IsBigO.of_bound' <| eventually_nhdsWithin_of_forall fun _ hx ↦
      (norm_one (α := ℝ)).symm ▸
        (Erdos980.NaturalChebotarev.norm_dedekindZeta_product_ge_one K hx s.im).le
  have H₁ := dedekindZeta_isBigO_near_one_horizontal K |>.pow 3 |>.mul <|
    ((dedekindZeta_eventuallyEq_continued_horizontal K s.im).trans_isBigO
      (continuedDedekindZeta_isBigO_horizontal_of_eq_zero K hy hzero)).pow 4 |>.mul <|
    (dedekindZeta_eventuallyEq_continued_horizontal K (2 * s.im)).trans_isBigO
      (continuedDedekindZeta_isBigO_horizontal K (mul_ne_zero two_ne_zero hy))
  have help (x : ℝ) : ((1 / x) ^ 3 * x ^ 4 * 1 : ℂ) = x := by
    rcases eq_or_ne x 0 with rfl | hx
    · rw [ofReal_zero, zero_pow (by omega), mul_zero, mul_one]
    · rw [one_div, inv_pow, pow_succ _ 3, ← mul_assoc,
        inv_mul_cancel₀ <| pow_ne_zero 3 (ofReal_ne_zero.mpr hx), one_mul, mul_one]
  simp only [ofReal_mul, ofReal_ofNat, mul_left_comm I, ← mul_assoc, help] at H₁
  replace H₁ := (H₀.trans H₁).norm_right
  simp only [norm_real] at H₁
  exact isLittleO_irrefl (.of_forall (fun _ ↦ one_ne_zero)) <|
    H₁.of_norm_right.trans_isLittleO <| isLittleO_id_one.mono nhdsWithin_le_nhds

/-- The continuation is nonzero on the whole closed half-plane `Re s ≥ 1`, except
at `s = 1`, where it represents the simple pole by a junk value. -/
theorem continuedDedekindZeta_ne_zero_of_one_le_re
    (K : Type*) [Field K] [NumberField K] {s : ℂ}
    (hs1 : s ≠ 1) (hs : 1 ≤ s.re) :
    continuedDedekindZeta K s ≠ 0 :=
  hs.eq_or_lt.casesOn
    (fun h ↦ continuedDedekindZeta_ne_zero_of_re_eq_one K h.symm hs1)
    fun h ↦ continuedDedekindZeta_eq_dedekindZeta K h ▸
      DedekindResidue.dedekindZeta_ne_zero_of_one_lt_re K h

end

end Erdos980.NaturalChebotarev.DedekindZeroFree
