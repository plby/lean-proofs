/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.PowerSieveExceptionalWitness
import BoundedGaps.BombieriVinogradov.Analytic.QuadraticRealZeroGap
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The finite interface to Heath--Brown's exceptional-zero theorem

Heath--Brown's Corollary 2 in *Prime Twins and Siegel Zeros* says that a
primitive character of conductor `m` with a real zero

`beta = 1 - lambda / log m`

gives the expected twin-prime asymptotic, with error
`O(lambda * z / log(z)^2)`, uniformly for `m^300 < z <= m^500`.
Ford--Luca--Pomerance use only the consequence that, for one absolute
positive upper bound on `lambda`, there are at least
`(6/5) * z / log(z)^2` twin-prime starts up to `z`.

The analytic implication itself is not yet available in Mathlib or
BoundedGaps.  This file does not assume it.  It records its narrowest useful
finite specification and proves the surrounding unconditional pieces:

* conversion from a Page-window zero to Heath--Brown's `lambda` parameter;
* extraction of a finite set of twin-prime starts from a real cardinality
  lower bound;
* divergence of the scale `z / log(z)^2`;
* the elementary `1.3 - 0.1 = 1.2` error absorption.
-/

namespace Erdos48

open Filter
open scoped Topology

noncomputable section

/-- Twin-prime starts at most `z`. -/
def twinPrimeStartsUpTo (z : ℕ) : Finset ℕ :=
  (Finset.Icc 2 z).filter fun p ↦ p.Prime ∧ (p + 2).Prime

@[simp] theorem mem_twinPrimeStartsUpTo {z p : ℕ} :
    p ∈ twinPrimeStartsUpTo z ↔
      2 ≤ p ∧ p ≤ z ∧ p.Prime ∧ (p + 2).Prime := by
  simp [twinPrimeStartsUpTo, and_assoc]

/-- The scale occurring in the twin-prime asymptotic. -/
def heathBrownTwinScale (z : ℕ) : ℝ :=
  (z : ℝ) / Real.log (z : ℝ) ^ 2

theorem heathBrownTwinScale_nonneg (z : ℕ) :
    0 ≤ heathBrownTwinScale z := by
  unfold heathBrownTwinScale
  positivity

/-- The elementary numerical absorption used by FLP: a main-term constant
at least `1.3` and an error at most `0.1` leave the lower constant `1.2`. -/
theorem six_fifths_mul_heathBrownTwinScale_le_card_of_abs_error
    {z : ℕ} {C E : ℝ}
    (hC : (13 : ℝ) / 10 ≤ C)
    (hE : E ≤ (1 : ℝ) / 10 * heathBrownTwinScale z)
    (happrox :
      |(twinPrimeStartsUpTo z).card - C * heathBrownTwinScale z| ≤ E) :
    (6 : ℝ) / 5 * heathBrownTwinScale z ≤
      (twinPrimeStartsUpTo z).card := by
  have hscale := heathBrownTwinScale_nonneg z
  have hmain : C * heathBrownTwinScale z - E ≤
      (twinPrimeStartsUpTo z).card := by
    have hlower := (abs_le.mp happrox).1
    linarith
  have hCS : (13 : ℝ) / 10 * heathBrownTwinScale z ≤
      C * heathBrownTwinScale z :=
    mul_le_mul_of_nonneg_right hC hscale
  calc
    (6 : ℝ) / 5 * heathBrownTwinScale z =
        (13 : ℝ) / 10 * heathBrownTwinScale z -
          (1 : ℝ) / 10 * heathBrownTwinScale z := by ring
    _ ≤ C * heathBrownTwinScale z - E := sub_le_sub hCS hE
    _ ≤ (twinPrimeStartsUpTo z).card := hmain

/-- The twin-prime asymptotic scale tends to infinity. -/
theorem tendsto_heathBrownTwinScale_atTop :
    Tendsto heathBrownTwinScale atTop atTop := by
  have hzero : Tendsto
      (fun z : ℕ ↦ Real.log (z : ℝ) ^ 2 / (z : ℝ))
      atTop (nhds 0) := by
    have h :=
      (Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero).comp
        tendsto_natCast_atTop_atTop
    simpa only [Function.comp_def, one_mul, add_zero] using h
  have hpos : ∀ᶠ z : ℕ in atTop,
      0 < Real.log (z : ℝ) ^ 2 / (z : ℝ) := by
    filter_upwards [eventually_ge_atTop (2 : ℕ)] with z hz
    have hzpos : (0 : ℝ) < z := by positivity
    have hlogpos : 0 < Real.log (z : ℝ) :=
      Real.log_pos (by exact_mod_cast hz)
    positivity
  have hinv :=
    (tendsto_nhdsWithin_iff.mpr ⟨hzero, hpos⟩).inv_tendsto_nhdsGT_zero
  apply hinv.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with z hz
  change (Real.log (z : ℝ) ^ 2 / (z : ℝ))⁻¹ =
    heathBrownTwinScale z
  rw [inv_div]
  rfl

theorem eventually_natCast_le_six_fifths_mul_heathBrownTwinScale (K : ℕ) :
    ∀ᶠ z : ℕ in atTop,
      (K : ℝ) ≤ (6 : ℝ) / 5 * heathBrownTwinScale z := by
  exact (tendsto_heathBrownTwinScale_atTop.const_mul_atTop
    (by norm_num : (0 : ℝ) < 6 / 5)).eventually_ge_atTop K

theorem primitiveRealZero_pow_300_lt_pow_500 (z : PrimitiveRealZero) :
    z.modulus ^ 300 < z.modulus ^ 500 :=
  Nat.pow_lt_pow_right z.modulus_gt_one (by norm_num)

theorem tendsto_heathBrownTwinScale_pow_500_atTop :
    Tendsto (fun m : ℕ ↦ heathBrownTwinScale (m ^ 500)) atTop atTop := by
  have hpow : Tendsto (fun m : ℕ ↦ m ^ 500) atTop atTop := by
    apply tendsto_atTop.2
    intro B
    filter_upwards [eventually_ge_atTop (max 1 B)] with m hm
    exact (le_max_right 1 B).trans hm |>.trans
      (Nat.le_pow (by norm_num : 0 < (500 : ℕ)))
  exact tendsto_heathBrownTwinScale_atTop.comp hpow

/-- A real lower bound for the twin-prime counting function gives the exact
finite object consumed by the exceptional side of the FLP dichotomy. -/
theorem exists_twinPrimeFinset_of_scale_le_card
    {K z : ℕ}
    (hK : (K : ℝ) ≤ (6 : ℝ) / 5 * heathBrownTwinScale z)
    (hcard : (6 : ℝ) / 5 * heathBrownTwinScale z ≤
      (twinPrimeStartsUpTo z).card) :
    ∃ s : Finset ℕ,
      K ≤ s.card ∧ ∀ p ∈ s, p.Prime ∧ (p + 2).Prime := by
  refine ⟨twinPrimeStartsUpTo z, ?_, ?_⟩
  · exact_mod_cast hK.trans hcard
  · intro p hp
    exact (mem_twinPrimeStartsUpTo.mp hp).2.2

/-- Heath--Brown's distance parameter attached to a supplied primitive real
zero. -/
def exceptionalZeroLambda (z : PrimitiveRealZero) : ℝ :=
  (1 - z.beta) * Real.log (z.modulus : ℝ)

theorem exceptionalZeroLambda_pos (z : PrimitiveRealZero) :
    0 < exceptionalZeroLambda z := by
  unfold exceptionalZeroLambda
  exact mul_pos (sub_pos.mpr z.beta_lt_one)
    (Real.log_pos (by exact_mod_cast z.modulus_gt_one))

theorem primitiveRealZero_beta_eq_one_sub_lambda_div_log
    (z : PrimitiveRealZero) :
    z.beta = 1 - exceptionalZeroLambda z /
      Real.log (z.modulus : ℝ) := by
  have hlog : Real.log (z.modulus : ℝ) ≠ 0 :=
    ne_of_gt (Real.log_pos (by exact_mod_cast z.modulus_gt_one))
  unfold exceptionalZeroLambda
  field_simp [hlog]
  ring

/-- A zero in a Page window of width `c` has Heath--Brown parameter less
than `c`.  This is the exact bridge from the zero retained by
`PageExceptionalWitness` to the exceptional twin-prime theorem. -/
theorem exceptionalZeroLambda_lt_of_inPageWindow
    {Q : ℕ} {c : ℝ} {z : PrimitiveRealZero}
    (hc : 0 < c) (hz : InPageWindow Q c z) :
    exceptionalZeroLambda z < c := by
  have hQ : 1 < Q := z.modulus_gt_one.trans_le hz.1
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast hQ)
  have hlogm : 0 < Real.log (z.modulus : ℝ) :=
    Real.log_pos (by exact_mod_cast z.modulus_gt_one)
  have hgap : 1 - z.beta < c / Real.log (Q : ℝ) := by
    linarith [hz.2]
  have hlogle : Real.log (z.modulus : ℝ) ≤ Real.log (Q : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast Nat.zero_lt_of_lt z.modulus_gt_one
    · exact_mod_cast hz.1
  have hfirst :
      (1 - z.beta) * Real.log (z.modulus : ℝ) <
        (c / Real.log (Q : ℝ)) * Real.log (z.modulus : ℝ) :=
    mul_lt_mul_of_pos_right hgap hlogm
  have hsecond :
      (c / Real.log (Q : ℝ)) * Real.log (z.modulus : ℝ) ≤
        (c / Real.log (Q : ℝ)) * Real.log (Q : ℝ) :=
    mul_le_mul_of_nonneg_left hlogle (div_nonneg hc.le hlogQ.le)
  unfold exceptionalZeroLambda
  calc
    (1 - z.beta) * Real.log (z.modulus : ℝ) <
        (c / Real.log (Q : ℝ)) * Real.log (z.modulus : ℝ) := hfirst
    _ ≤ (c / Real.log (Q : ℝ)) * Real.log (Q : ℝ) := hsecond
    _ = c := by field_simp [hlogQ.ne']

theorem PageExceptionalWitness.exists_zero_with_small_lambda
    {Q m : ℕ} {c : ℝ} (hc : 0 < c)
    (h : PageExceptionalWitness Q m c) :
    ∃ z : PrimitiveRealZero,
      z.modulus = m ∧ exceptionalZeroLambda z < c ∧
        z.beta = 1 - exceptionalZeroLambda z /
          Real.log (z.modulus : ℝ) := by
  obtain ⟨z, hm, hz⟩ := h
  exact ⟨z, hm, exceptionalZeroLambda_lt_of_inPageWindow hc hz,
    primitiveRealZero_beta_eq_one_sub_lambda_div_log z⟩

theorem InPageWindow.mono_width
    {Q : ℕ} {c d : ℝ} {z : PrimitiveRealZero}
    (hcd : c ≤ d) (hz : InPageWindow Q c z) :
    InPageWindow Q d z := by
  refine ⟨hz.1, ?_⟩
  have hQ : 1 < Q := z.modulus_gt_one.trans_le hz.1
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast hQ)
  have hdiv : c / Real.log (Q : ℝ) ≤ d / Real.log (Q : ℝ) :=
    div_le_div_of_nonneg_right hcd hlogQ.le
  linarith [hz.2]

theorem PageExceptionalWitness.mono_width
    {Q m : ℕ} {c d : ℝ} (hcd : c ≤ d)
    (h : PageExceptionalWitness Q m c) :
    PageExceptionalWitness Q m d := by
  obtain ⟨z, hm, hz⟩ := h
  exact ⟨z, hm, InPageWindow.mono_width hcd hz⟩

/-- A Page-window witness remains a witness when the Page scale is lowered
to its own conductor.  The new window is wider. -/
theorem inPageWindow_modulus_of_inPageWindow
    {Q : ℕ} {c : ℝ} {z : PrimitiveRealZero}
    (hc : 0 ≤ c) (hz : InPageWindow Q c z) :
    InPageWindow z.modulus c z := by
  refine ⟨le_rfl, ?_⟩
  have hlogm : 0 < Real.log (z.modulus : ℝ) :=
    Real.log_pos (by exact_mod_cast z.modulus_gt_one)
  have hQ : 1 < Q := z.modulus_gt_one.trans_le hz.1
  have hlogle : Real.log (z.modulus : ℝ) ≤ Real.log (Q : ℝ) :=
    Real.log_le_log
      (by exact_mod_cast Nat.zero_lt_of_lt z.modulus_gt_one)
      (by exact_mod_cast hz.1)
  have hdiv : c / Real.log (Q : ℝ) ≤
      c / Real.log (z.modulus : ℝ) :=
    div_le_div_of_nonneg_left hc hlogm hlogle
  linarith [hz.2]

theorem PageExceptionalWitness.retarget_to_modulus
    {Q m : ℕ} {c : ℝ} (hc : 0 ≤ c)
    (h : PageExceptionalWitness Q m c) :
    PageExceptionalWitness m m c := by
  obtain ⟨z, rfl, hz⟩ := h
  exact ⟨z, rfl, inPageWindow_modulus_of_inPageWindow hc hz⟩

private theorem primitiveRealZero_isNonprincipalNontrivial
    (z : PrimitiveRealZero) :
    BoundedGaps.Maynard.IsNonprincipalNontrivialLFunctionZero
      z.character (z.beta : ℂ) := by
  apply (BoundedGaps.Maynard.isNonprincipalNontrivialLFunctionZero_iff _ _).2
  exact ⟨z.ne_one, z.isZero, by simpa using z.beta_pos,
    by simpa using z.beta_lt_one⟩

/-- There is an absolute Page-window width for which every retained real
zero belongs to a square-principal character.  This is the precise local
input needed before applying the effective quadratic real-zero gap.

The factor `2` in the width comes from
`log (2 * z.modulus) ≤ 2 * log Q` when `z.modulus ≤ Q` and `3 ≤ Q`. -/
theorem exists_pageWindow_character_sq_eq_one :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Q : ℕ), 3 ≤ Q →
        ∀ z : PrimitiveRealZero, InPageWindow Q c z →
          z.character ^ 2 = 1 := by
  obtain ⟨M, hM, hshape⟩ :=
    BoundedGaps.Maynard.exists_nat_nonprincipalNontrivialLFunctionZero_sq_eq_one_real_simple
  let c : ℝ := 1 / (2 * (M : ℝ) ^ 2)
  have hMpos : (0 : ℝ) < M := by exact_mod_cast (Nat.zero_lt_of_lt hM)
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c, hc, ?_⟩
  intro Q hQ z hz
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have htwoMle : 2 * z.modulus ≤ Q ^ 2 := by
    calc
      2 * z.modulus ≤ 2 * Q := Nat.mul_le_mul_left 2 hz.1
      _ ≤ Q * Q := Nat.mul_le_mul_right Q (by omega : 2 ≤ Q)
      _ = Q ^ 2 := by ring
  have hlogTwoM : 0 < Real.log ((z.modulus : ℝ) * 2) := by
    apply Real.log_pos
    have hmTwo : 2 ≤ z.modulus := z.modulus_gt_one
    have : (1 : ℕ) < z.modulus * 2 := by omega
    exact_mod_cast this
  have hlogCompare :
      Real.log ((z.modulus : ℝ) * 2) ≤
        2 * Real.log (Q : ℝ) := by
    calc
      Real.log ((z.modulus : ℝ) * 2) =
          Real.log ((2 * z.modulus : ℕ) : ℝ) := by
            norm_num [Nat.cast_mul, mul_comm]
      _ ≤ Real.log ((Q ^ 2 : ℕ) : ℝ) :=
        Real.log_le_log
          (by
            exact_mod_cast Nat.mul_pos (by norm_num : 0 < (2 : ℕ))
              (Nat.zero_lt_of_lt z.modulus_gt_one))
          (by exact_mod_cast htwoMle)
      _ = 2 * Real.log (Q : ℝ) := by
        rw [Nat.cast_pow, Real.log_pow]
        norm_num
  have hdenPos :
      0 < (M : ℝ) ^ 2 * Real.log ((z.modulus : ℝ) * 2) :=
    mul_pos (sq_pos_of_pos hMpos) hlogTwoM
  have hdenCompare :
      (M : ℝ) ^ 2 * Real.log ((z.modulus : ℝ) * 2) ≤
        2 * (M : ℝ) ^ 2 * Real.log (Q : ℝ) := by
    nlinarith [sq_nonneg (M : ℝ)]
  have hinv :
      1 / (2 * (M : ℝ) ^ 2 * Real.log (Q : ℝ)) ≤
        1 / ((M : ℝ) ^ 2 * Real.log ((z.modulus : ℝ) * 2)) := by
    apply one_div_le_one_div_of_le hdenPos
    nlinarith [hMpos, hlogQ]
  have hcRewrite :
      c / Real.log (Q : ℝ) =
        1 / (2 * (M : ℝ) ^ 2 * Real.log (Q : ℝ)) := by
    dsimp [c]
    field_simp [hMpos.ne', hlogQ.ne']
  have hnear :
      1 - 1 / ((M : ℝ) ^ 2 *
          Real.log ((z.modulus : ℝ) *
            (|(z.beta : ℂ).im| + 2))) ≤ z.beta := by
    have hzPage := hz.2
    rw [hcRewrite] at hzPage
    have :
        1 - 1 / ((M : ℝ) ^ 2 *
            Real.log ((z.modulus : ℝ) * 2)) < z.beta := by
      linarith
    simpa using this.le
  exact (hshape z.modulus z.character (z.beta : ℂ)
    (primitiveRealZero_isNonprincipalNontrivial z) hnear).1

/-- The explicit denominator in BoundedGaps' effective quadratic real-zero
gap.  Its logarithmic exponent `4` is weaker than the exponent `2` quoted
by FLP, but is more than sufficient to force exceptional conductors to
infinity as the Page scale tends to infinity. -/
def effectiveQuadraticGapDenom (m : ℕ) : ℝ :=
  (2 ^ 22 : ℝ) * Real.sqrt (m : ℝ) * Real.log (m : ℝ) ^ 4

theorem effectiveQuadraticGapDenom_pos {m : ℕ} (hm : 1 < m) :
    0 < effectiveQuadraticGapDenom m := by
  unfold effectiveQuadraticGapDenom
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hlog : 0 < Real.log (m : ℝ) :=
    Real.log_pos (by exact_mod_cast hm)
  positivity

theorem effectiveQuadraticGapDenom_mono
    {m n : ℕ} (hm : 1 < m) (hmn : m ≤ n) :
    effectiveQuadraticGapDenom m ≤ effectiveQuadraticGapDenom n := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (Nat.zero_lt_of_lt hm)
  have hmnR : (m : ℝ) ≤ n := by exact_mod_cast hmn
  have hsqrt : Real.sqrt (m : ℝ) ≤ Real.sqrt (n : ℝ) :=
    Real.sqrt_le_sqrt hmnR
  have hlogm : 0 ≤ Real.log (m : ℝ) :=
    (Real.log_pos (by exact_mod_cast hm)).le
  have hlog : Real.log (m : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hm0 hmnR
  have hlogpow : Real.log (m : ℝ) ^ 4 ≤
      Real.log (n : ℝ) ^ 4 :=
    pow_le_pow_left₀ hlogm hlog 4
  unfold effectiveQuadraticGapDenom
  gcongr

/-- A sufficiently narrow Page-window zero satisfies the explicit local
effective gap already proved in BoundedGaps. -/
theorem exists_pageWindow_effectiveQuadraticGap :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Q : ℕ), 3 ≤ Q →
        ∀ z : PrimitiveRealZero, InPageWindow Q c z →
          1 / effectiveQuadraticGapDenom z.modulus ≤ 1 - z.beta := by
  obtain ⟨c, hc, hsq⟩ := exists_pageWindow_character_sq_eq_one
  refine ⟨c, hc, ?_⟩
  intro Q hQ z hz
  simpa only [effectiveQuadraticGapDenom] using
    BoundedGaps.Maynard.effectiveQuadraticRealZeroGap
      z.modulus_gt_one z.character z.ne_one (hsq Q hQ z hz)
        z.beta_lt_one.le z.isZero

/-- Quantitative conductor growth at a Page scale.  This is the exact
algebraic consequence needed in the exceptional branch: a zero in the
Page window forces `log Q` below a fixed multiple of the effective
quadratic-gap denominator at its conductor. -/
theorem exists_pageWindow_log_lt_gapDenom :
    ∃ c : ℝ, 0 < c ∧
      ∀ (Q : ℕ), 3 ≤ Q →
        ∀ z : PrimitiveRealZero, InPageWindow Q c z →
          Real.log (Q : ℝ) <
            c * effectiveQuadraticGapDenom z.modulus := by
  obtain ⟨c, hc, hgap⟩ := exists_pageWindow_effectiveQuadraticGap
  refine ⟨c, hc, ?_⟩
  intro Q hQ z hz
  have hlogQ : 0 < Real.log (Q : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q by omega))
  have hD : 0 < effectiveQuadraticGapDenom z.modulus :=
    effectiveQuadraticGapDenom_pos z.modulus_gt_one
  have hpage : 1 - z.beta < c / Real.log (Q : ℝ) := by
    linarith [hz.2]
  have hquot :
      1 / effectiveQuadraticGapDenom z.modulus <
        c / Real.log (Q : ℝ) :=
    (hgap Q hQ z hz).trans_lt hpage
  rw [div_lt_div_iff₀ hD hlogQ] at hquot
  simpa only [one_mul] using hquot

/-- The conductor of a zero retained in one fixed sufficiently narrow Page
window tends uniformly to infinity with the Page scale.  This is the
finite-interface form useful for retargeting an exceptional scale: every
fixed conductor bound is eventually impossible. -/
theorem exists_pageWindow_eventually_modulus_gt :
    ∃ c : ℝ, 0 < c ∧
      ∀ B : ℕ, ∀ᶠ Q : ℕ in atTop,
        ∀ z : PrimitiveRealZero, InPageWindow Q c z →
          B < z.modulus := by
  obtain ⟨c, hc, hgrowth⟩ := exists_pageWindow_log_lt_gapDenom
  refine ⟨c, hc, ?_⟩
  intro B
  let B' : ℕ := max B 2
  have hlogTop : Tendsto (fun Q : ℕ ↦ Real.log (Q : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
      [hlogTop.eventually_gt_atTop
        (c * effectiveQuadraticGapDenom B'),
        eventually_ge_atTop (3 : ℕ)] with Q hlogQ hQ
  intro z hz
  by_contra hnot
  have hmB : z.modulus ≤ B := Nat.le_of_not_gt hnot
  have hmB' : z.modulus ≤ B' := hmB.trans (le_max_left _ _)
  have hdenomLe : effectiveQuadraticGapDenom z.modulus ≤
      effectiveQuadraticGapDenom B' :=
    effectiveQuadraticGapDenom_mono z.modulus_gt_one hmB'
  have hcdenomLe :
      c * effectiveQuadraticGapDenom z.modulus ≤
        c * effectiveQuadraticGapDenom B' :=
    mul_le_mul_of_nonneg_left hdenomLe hc.le
  have hsmall := hgrowth Q hQ z hz
  linarith

/-- Restoring one erased positive integer costs exactly the advertised
`1 / m` in a uniform prefix-density estimate.  This is the finite
combinatorial bridge needed if the exceptional conductor itself is retained
as one additional bad root. -/
theorem card_prefix_le_erase_density_add_inv
    {E : Finset ℕ} {m : ℕ} {rho : ℝ} (hm : 0 < m)
    (herase : ∀ y : ℕ,
      (((E.erase m).filter fun q ↦ q ≤ y).card : ℝ) ≤
        rho * (y : ℝ)) :
    ∀ y : ℕ,
      ((E.filter fun q ↦ q ≤ y).card : ℝ) ≤
        (rho + (m : ℝ)⁻¹) * (y : ℝ) := by
  classical
  intro y
  by_cases hmy : m ≤ y
  · have hsub : E.filter (fun q ↦ q ≤ y) ⊆
        insert m ((E.erase m).filter fun q ↦ q ≤ y) := by
      intro q hq
      have hqData := Finset.mem_filter.mp hq
      by_cases hqm : q = m
      · subst q
        exact Finset.mem_insert_self m _
      · have hqErase : q ∈ E.erase m :=
          Finset.mem_erase.mpr ⟨hqm, hqData.1⟩
        exact Finset.mem_insert_of_mem
          (Finset.mem_filter.mpr ⟨hqErase, hqData.2⟩)
    have hcardNat :
        (E.filter fun q ↦ q ≤ y).card ≤
          ((E.erase m).filter fun q ↦ q ≤ y).card + 1 :=
      (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    have hcard :
        ((E.filter fun q ↦ q ≤ y).card : ℝ) ≤
          (((E.erase m).filter fun q ↦ q ≤ y).card : ℝ) + 1 := by
      exact_mod_cast hcardNat
    have hmR : (0 : ℝ) < m := by exact_mod_cast hm
    have hunit : (1 : ℝ) ≤ (m : ℝ)⁻¹ * (y : ℝ) := by
      rw [inv_mul_eq_div, le_div_iff₀ hmR]
      have hmyR : (m : ℝ) ≤ (y : ℝ) := by exact_mod_cast hmy
      simpa only [one_mul] using hmyR
    calc
      ((E.filter fun q ↦ q ≤ y).card : ℝ) ≤
          (((E.erase m).filter fun q ↦ q ≤ y).card : ℝ) + 1 := hcard
      _ ≤ rho * (y : ℝ) + (m : ℝ)⁻¹ * (y : ℝ) :=
        add_le_add (herase y) hunit
      _ = (rho + (m : ℝ)⁻¹) * (y : ℝ) := by ring
  · have heq : E.filter (fun q ↦ q ≤ y) =
        (E.erase m).filter fun q ↦ q ≤ y := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_erase]
      constructor
      · rintro ⟨hqE, hqy⟩
        refine ⟨⟨?_, hqE⟩, hqy⟩
        intro hqm
        subst q
        exact hmy hqy
      · intro hq
        exact ⟨hq.1.2, hq.2⟩
    rw [heq]
    calc
      ((((E.erase m).filter fun q ↦ q ≤ y).card : ℕ) : ℝ) ≤
          rho * (y : ℝ) := herase y
      _ ≤ (rho + (m : ℝ)⁻¹) * (y : ℝ) := by
        have hy : (0 : ℝ) ≤ y := by positivity
        have hinv : (0 : ℝ) ≤ (m : ℝ)⁻¹ := by positivity
        nlinarith

/-- The narrow analytic input still missing from the library.  It is a
proposition, not an assumption: no theorem in this file asserts it.

This lower-bound form is exactly what FLP use from Heath--Brown's
Corollary 2 after absorbing the singular-series lower bound and the
`O(lambda)` error into the constants `1.3`, `0.1`, and `1.2`. -/
def HeathBrownExceptionalTwinLowerBound : Prop :=
  ∃ lambda0 : ℝ, 0 < lambda0 ∧
    ∀ z : PrimitiveRealZero,
      exceptionalZeroLambda z ≤ lambda0 →
      ∀ x : ℕ, z.modulus ^ 300 < x → x ≤ z.modulus ^ 500 →
        (6 : ℝ) / 5 * heathBrownTwinScale x ≤
          (twinPrimeStartsUpTo x).card

end

end Erdos48
