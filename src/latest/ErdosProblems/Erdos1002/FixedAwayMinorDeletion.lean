import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import ErdosProblems.Erdos1002.NearResonantMinorAssembly
import ErdosProblems.Erdos1002.FixedAwayPhysicalSubtraction
import ErdosProblems.Erdos1002.TransitionLayerCake
import ErdosProblems.Erdos1002.RamanujanIdentities
import ErdosProblems.Erdos1002.FixedAwayUnshiftedAbel
import ErdosProblems.Erdos1002.NaturalCutoffShotErrorSublog

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Fixed-away minor-resonance deletion

This module proves the complete fixed-away branch of the minor-shot
decomposition.  Its sole arithmetic premise is the literal Chan--Kumchev
prefix estimate with source logarithmic exponent `11`; the proof chooses
the smaller terminal cutoff `⌊K / log(K)^32⌋`.

The conditional route is retained because it mirrors the manuscript's
source estimate.  It is not used as an assumption by the public theorem:
`FixedAwayUnshiftedSubquadratic` supplies the unconditional fixed-away
deletion used by `UnconditionalFinalReduction`.

The argument records every comparison used in the manuscript: the sharp
fixed-away sum minus the upper smooth transition is exactly a fixed-away
smooth shot plus the two endpoint denominators; zero and nonzero Fourier
carriers have summable linear-in-`log N` energy; the physical Fourier
reconstruction error is sublogarithmic; and the resulting normalized
remainder vanishes in the nested `A → ∞`, then `N → ∞`, probability limit.
The final section also identifies the upper transition with its finite
strict Stieltjes layer-cake expression.
-/

open Filter MeasureTheory Set Finset
open scoped BigOperators ENNReal Topology

namespace Erdos1002

noncomputable section

theorem fixedAwaySmoothCutoff_eq_one_sub_outer
    {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) :
    fixedAwaySmoothCutoff ε (ε / 2) x =
      1 - gevreyOuterCutoff ε x := by
  rw [gevreyOuterCutoff_eq_transition_div hε]
  unfold fixedAwaySmoothCutoff
  have hhalf : ε / 2 ≠ 0 := div_ne_zero hε (by norm_num)
  have hfirst :
      (ε / 2)⁻¹ * x + (1 - (ε / 2)⁻¹ * ε) =
        (x - ε / 2) / (ε / 2) := by
    field_simp [hhalf]
    ring
  have hsecond :
      (-(ε / 2)⁻¹) * x + (1 - (ε / 2)⁻¹ * ε) =
        (-x - ε / 2) / (ε / 2) := by
    field_simp [hhalf]
    ring
  rw [hfirst, hsecond]
  ring

theorem scaledNearProfile_half_eq_outer
    {ε : ℝ} (hε : ε ≠ 0) (x : ℝ) :
    scaledNearProfile (ε / 2) x =
      (gevreyOuterCutoff ε x : ℂ) := by
  unfold scaledNearProfile nearBaseProfile
  rw [gevreyOuterCutoff_eq_transition_div (by norm_num : (2 : ℝ) ≠ 0)]
  rw [gevreyOuterCutoff_eq_transition_div hε]
  push_cast
  have hhalf : ε / 2 ≠ 0 := div_ne_zero hε (by norm_num)
  have hfirst :
      (x / (ε / 2) - 2 / 2) / (2 / 2) =
        (x - ε / 2) / (ε / 2) := by
    field_simp [hhalf]
  have hsecond :
      (-(x / (ε / 2)) - 2 / 2) / (2 / 2) =
        (-x - ε / 2) / (ε / 2) := by
    field_simp [hhalf]
  rw [hfirst, hsecond]

theorem nearRho_eq_outer_of_inner_support
    {a ε x : ℝ} (ha : 0 < a) (hε : 0 < ε)
    (hinner : 2 * a ≤ |x|) :
    nearRho a ε x = (gevreyOuterCutoff ε x : ℂ) := by
  rw [nearRho,
    scaledNearProfile_eq_zero_of_two_mul_le_abs a x ha hinner,
    scaledNearProfile_half_eq_outer hε.ne' x, sub_zero]

theorem minorFixedAwaySharp_sub_upper_eq_smooth
    (N p : ℕ) (A ε alpha : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ))
    (hε : 0 < ε)
    (hroom : A / Real.log (N : ℝ) ≤ ε / 4) :
    minorFixedAwaySharpTerm N p (ε / 4) alpha -
        nearMinorUpperTransitionTerm N A ε p alpha =
      fixedAwaySmoothShotTerm ε (ε / 2) N p alpha := by
  let x : ℝ := (p : ℝ) * resonanceDelta p alpha
  let a : ℝ := A / (2 * Real.log (N : ℝ))
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hδ : 0 < ε / 2 := by positivity
  have hδε : ε / 2 ≤ ε := by linarith
  by_cases hquarter : |x| ≤ ε / 4
  · have hhalf : |x| ≤ ε - ε / 2 := by
      dsimp [x] at hquarter ⊢
      linarith
    unfold minorFixedAwaySharpTerm nearMinorUpperTransitionTerm
      fixedAwaySmoothShotTerm
    rw [if_neg (not_lt.mpr (by simpa only [x] using! hquarter)),
      if_neg (not_lt.mpr (by simpa only [x] using! hquarter)),
      fixedAwaySmoothCutoff_eq_zero_of_abs_le_sub hδ
        (by simpa only [x] using! hhalf)]
    norm_num
  · have hquarter' : ε / 4 < |x| := lt_of_not_ge hquarter
    have hinner : 2 * a ≤ |x| := by
      have hscale : 2 * a = A / Real.log (N : ℝ) := by
        dsimp [a]
        field_simp [hL.ne']
      rw [hscale]
      exact hroom.trans hquarter'.le
    have hrho :
        nearRho (A / (2 * Real.log (N : ℝ))) ε x =
          (gevreyOuterCutoff ε x : ℂ) := by
      simpa only [a] using!
        nearRho_eq_outer_of_inner_support ha hε hinner
    unfold minorFixedAwaySharpTerm nearMinorUpperTransitionTerm
      fixedAwaySmoothShotTerm
    rw [if_pos (by simpa only [x] using! hquarter'),
      if_pos (by simpa only [x] using! hquarter'),
      smoothNearLiteralShotTerm_eq_rho_mul_primitiveShot,
      show nearRho (A / (2 * Real.log (N : ℝ))) ε
          ((p : ℝ) * resonanceDelta p alpha) =
          (gevreyOuterCutoff ε
            ((p : ℝ) * resonanceDelta p alpha) : ℂ) by
        simpa only [x] using! hrho,
      fixedAwaySmoothCutoff_eq_one_sub_outer hε.ne']
    push_cast
    ring

def fixedAwayMinorEndpointDiscrepancy
    (N : ℕ) (ε alpha : ℝ) : ℂ :=
  ∑ p ∈ Finset.Icc 1 2,
    (minorFixedAwaySharpTerm N p (ε / 4) alpha -
      fixedAwaySmoothShotTerm ε (ε / 2) N p alpha)

theorem minorFixedAwaySharp_sub_upper_eq_smooth_add_endpoints
    (N : ℕ) (A ε alpha : ℝ)
    (hN : 2 ≤ N)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ))
    (hε : 0 < ε)
    (hroom : A / Real.log (N : ℝ) ≤ ε / 4) :
    minorFixedAwaySharpSum N (ε / 4) alpha -
        nearMinorUpperTransitionSum N A ε alpha =
      fixedAwaySmoothShotSum ε (ε / 2) N N alpha +
        fixedAwayMinorEndpointDiscrepancy N ε alpha := by
  have hset : Finset.Icc 1 N =
      Finset.Icc 1 2 ∪ Finset.Ioc 2 N := by
    ext p
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisjoint : Disjoint (Finset.Icc 1 2) (Finset.Ioc 2 N) := by
    rw [Finset.disjoint_left]
    intro p hpSmall hpLarge
    have hs := Finset.mem_Icc.mp hpSmall
    have hl := Finset.mem_Ioc.mp hpLarge
    omega
  unfold minorFixedAwaySharpSum nearMinorUpperTransitionSum
    fixedAwaySmoothShotSum fixedAwayMinorEndpointDiscrepancy
  rw [hset, Finset.sum_union hdisjoint, Finset.sum_union hdisjoint]
  have htail :
      (∑ p ∈ Finset.Ioc 2 N,
          minorFixedAwaySharpTerm N p (ε / 4) alpha) -
        ∑ p ∈ Finset.Ioc 2 N,
          nearMinorUpperTransitionTerm N A ε p alpha =
        ∑ p ∈ Finset.Ioc 2 N,
          fixedAwaySmoothShotTerm ε (ε / 2) N p alpha := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro p _hp
    exact minorFixedAwaySharp_sub_upper_eq_smooth
      N p A ε alpha hA hL hε hroom
  calc
    (∑ p ∈ Finset.Icc 1 2,
          minorFixedAwaySharpTerm N p (ε / 4) alpha) +
          (∑ p ∈ Finset.Ioc 2 N,
            minorFixedAwaySharpTerm N p (ε / 4) alpha) -
        ∑ p ∈ Finset.Ioc 2 N,
          nearMinorUpperTransitionTerm N A ε p alpha =
        (∑ p ∈ Finset.Icc 1 2,
          minorFixedAwaySharpTerm N p (ε / 4) alpha) +
          ((∑ p ∈ Finset.Ioc 2 N,
              minorFixedAwaySharpTerm N p (ε / 4) alpha) -
            ∑ p ∈ Finset.Ioc 2 N,
              nearMinorUpperTransitionTerm N A ε p alpha) := by ring
    _ = (∑ p ∈ Finset.Icc 1 2,
          minorFixedAwaySharpTerm N p (ε / 4) alpha) +
        ∑ p ∈ Finset.Ioc 2 N,
          fixedAwaySmoothShotTerm ε (ε / 2) N p alpha := by
      rw [htail]
    _ = (∑ p ∈ Finset.Icc 1 2,
          fixedAwaySmoothShotTerm ε (ε / 2) N p alpha) +
        (∑ p ∈ Finset.Ioc 2 N,
          fixedAwaySmoothShotTerm ε (ε / 2) N p alpha) +
        ((∑ p ∈ Finset.Icc 1 2,
            minorFixedAwaySharpTerm N p (ε / 4) alpha) -
          ∑ p ∈ Finset.Icc 1 2,
            fixedAwaySmoothShotTerm ε (ε / 2) N p alpha) := by ring
    _ = (∑ p ∈ Finset.Icc 1 2,
          fixedAwaySmoothShotTerm ε (ε / 2) N p alpha) +
        (∑ p ∈ Finset.Ioc 2 N,
          fixedAwaySmoothShotTerm ε (ε / 2) N p alpha) +
        ∑ p ∈ Finset.Icc 1 2,
          (minorFixedAwaySharpTerm N p (ε / 4) alpha -
            fixedAwaySmoothShotTerm ε (ε / 2) N p alpha) := by
      rw [Finset.sum_sub_distrib]

theorem norm_primitiveShot_le_of_coordinate
    (N p : ℕ) (alpha a : ℝ)
    (ha : 0 < a)
    (hcoord : a ≤ |(p : ℝ) * resonanceDelta p alpha|) :
    ‖(primitiveShot N p alpha : ℂ)‖ ≤ 1 / (8 * a) := by
  by_cases hprim : IsPrimitiveResonance p alpha
  · rw [primitiveShot_of_primitive N p alpha hprim,
      Complex.norm_real, Real.norm_eq_abs, abs_div]
    have hden : 0 < |(p : ℝ) * resonanceDelta p alpha| :=
      ha.trans_le hcoord
    calc
      |bernoulliMark ((N : ℝ) * resonanceDelta p alpha)| /
          |(p : ℝ) * resonanceDelta p alpha| ≤
        (1 / 8 : ℝ) /
          |(p : ℝ) * resonanceDelta p alpha| := by
        exact div_le_div_of_nonneg_right
          (abs_bernoulliMark_le_one_eighth _) hden.le
      _ ≤ (1 / 8 : ℝ) / a := by
        exact mul_le_mul_of_nonneg_left
          (by simpa only [one_div] using!
            (one_div_le_one_div_of_le ha hcoord)) (by norm_num)
      _ = 1 / (8 * a) := by ring
  · rw [primitiveShot_of_not_primitive N p alpha hprim,
      Complex.ofReal_zero, norm_zero]
    positivity

theorem norm_minorFixedAwaySharpTerm_quarter_le
    (N p : ℕ) (ε alpha : ℝ) (hε : 0 < ε) :
    ‖minorFixedAwaySharpTerm N p (ε / 4) alpha‖ ≤ 1 / (2 * ε) := by
  unfold minorFixedAwaySharpTerm
  split_ifs with hfar
  · have hprimitive := norm_primitiveShot_le_of_coordinate
      N p alpha (ε / 4) (by positivity) hfar.le
    convert! hprimitive using 1
    field_simp [hε.ne']
    norm_num
  · rw [norm_zero]
    positivity

theorem norm_fixedAwaySmoothShotTerm_outer_le
    (N p : ℕ) (ε alpha : ℝ) (hε : 0 < ε) :
    ‖fixedAwaySmoothShotTerm ε (ε / 2) N p alpha‖ ≤
      1 / (2 * ε) := by
  let x : ℝ := (p : ℝ) * resonanceDelta p alpha
  by_cases hhalf : |x| ≤ ε / 2
  · unfold fixedAwaySmoothShotTerm
    rw [fixedAwaySmoothCutoff_eq_zero_of_abs_le_sub
      (by positivity : 0 < ε / 2) (by
        simpa only [x] using! (show |x| ≤ ε - ε / 2 by linarith)),
      Complex.ofReal_zero, zero_mul, norm_zero]
    positivity
  · have hprimitive := norm_primitiveShot_le_of_coordinate
      N p alpha (ε / 2) (by positivity)
        (by simpa only [x] using! (lt_of_not_ge hhalf).le)
    calc
      ‖fixedAwaySmoothShotTerm ε (ε / 2) N p alpha‖ ≤
          ‖(primitiveShot N p alpha : ℂ)‖ :=
        norm_fixedAwaySmoothShotTerm_le
          (by positivity : 0 < ε / 2) (by linarith) N p alpha
      _ ≤ 1 / (8 * (ε / 2)) := hprimitive
      _ ≤ 1 / (2 * ε) := by
        have hε0 : 0 ≤ ε := hε.le
        field_simp [hε.ne']
        linarith

theorem norm_fixedAwayMinorEndpointDiscrepancy_le
    (N : ℕ) (ε alpha : ℝ) (hε : 0 < ε) :
    ‖fixedAwayMinorEndpointDiscrepancy N ε alpha‖ ≤ 2 / ε := by
  unfold fixedAwayMinorEndpointDiscrepancy
  calc
    ‖∑ p ∈ Finset.Icc 1 2,
        (minorFixedAwaySharpTerm N p (ε / 4) alpha -
          fixedAwaySmoothShotTerm ε (ε / 2) N p alpha)‖ ≤
      ∑ p ∈ Finset.Icc 1 2,
        ‖minorFixedAwaySharpTerm N p (ε / 4) alpha -
          fixedAwaySmoothShotTerm ε (ε / 2) N p alpha‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _p ∈ Finset.Icc 1 2, (1 / ε : ℝ) := by
      gcongr with p hp
      calc
        ‖minorFixedAwaySharpTerm N p (ε / 4) alpha -
            fixedAwaySmoothShotTerm ε (ε / 2) N p alpha‖ ≤
          ‖minorFixedAwaySharpTerm N p (ε / 4) alpha‖ +
            ‖fixedAwaySmoothShotTerm ε (ε / 2) N p alpha‖ :=
          norm_sub_le _ _
        _ ≤ 1 / (2 * ε) + 1 / (2 * ε) :=
          add_le_add
            (norm_minorFixedAwaySharpTerm_quarter_le N p ε alpha hε)
            (norm_fixedAwaySmoothShotTerm_outer_le N p ε alpha hε)
        _ = 1 / ε := by
          field_simp [hε.ne']
          ring
    _ = 2 / ε := by
      simp only [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul]
      norm_num
      field_simp [hε.ne']

theorem ramanujanSum_one_index
    (p : ℕ) (hp : p ≠ 0) :
    ramanujanSum p (1 : ℤ) =
      (ArithmeticFunction.moebius p : ℂ) := by
  have h := ramanujanSum_nat_divisor_moebius p 1 hp
  norm_num at h
  simpa using! h

def fixedAwayInverseSquareMass : ℝ :=
  ∑' p : ℕ, 1 / (p : ℝ) ^ 2

theorem fixedAwayInverseSquareMass_nonneg :
    0 ≤ fixedAwayInverseSquareMass := by
  unfold fixedAwayInverseSquareMass
  exact tsum_nonneg fun p ↦ by positivity

theorem summable_inverseSquare_nat :
    Summable fun p : ℕ ↦ 1 / (p : ℝ) ^ 2 := by
  exact Real.summable_one_div_nat_pow.mpr (by norm_num)

theorem norm_fixedAwayUnshifted_one_term_le
    {t δ : ℝ} (N p : ℕ)
    (hδ : 0 < δ) (hδt : δ < t) (hp : 0 < p) :
    ‖fixedAwayRamanujanProfileTerm
        (fixedAwayShiftedProfile t δ N 0) p 1‖ ≤
      fixedAwayPVGlobalDecayConstant t δ / (p : ℝ) ^ 2 := by
  have hmu :
      ‖(ArithmeticFunction.moebius p : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]
    exact_mod_cast
      (ArithmeticFunction.abs_moebius_le_one (n := p))
  have hram : ‖ramanujanSum p (-(1 : ℤ))‖ ≤ 1 := by
    rw [ramanujanSum_even,
      ramanujanSum_one_index p hp.ne']
    exact hmu
  have htransform :=
    norm_fixedAwayPVTransform_smooth_le_globalDecay
      hδ hδt ((1 : ℝ) / (p : ℝ) ^ 2)
  have hC : 0 ≤ fixedAwayPVGlobalDecayConstant t δ :=
    fixedAwayPVGlobalDecayConstant_nonneg t δ
  have htransform' :
      ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t
          ((1 : ℝ) / (p : ℝ) ^ 2)‖ ≤
        fixedAwayPVGlobalDecayConstant t δ := by
    calc
      ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t
          ((1 : ℝ) / (p : ℝ) ^ 2)‖ ≤
        fixedAwayPVGlobalDecayConstant t δ *
          (1 + |(1 : ℝ) / (p : ℝ) ^ 2|)⁻¹ := htransform
      _ ≤ fixedAwayPVGlobalDecayConstant t δ * 1 := by
        gcongr
        exact inv_le_one_of_one_le₀
          (le_add_of_nonneg_right (abs_nonneg _))
      _ = fixedAwayPVGlobalDecayConstant t δ := mul_one _
  unfold fixedAwayRamanujanProfileTerm fixedAwayShiftedProfile
    fixedAwayScaledPV nearBernoulliCarrierFrequency
  norm_num only [Int.ofNat_eq_natCast, Int.cast_one, Int.cast_zero,
    zero_mul, add_zero, Nat.cast_one, one_mul]
  rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (by positivity : 0 ≤ 1 / (p : ℝ) ^ 2)]
  calc
    (1 / (p : ℝ) ^ 2) * ‖ramanujanSum p (-(1 : ℤ))‖ *
        ‖fixedAwayPVTransform (fixedAwaySmoothCorrection t δ) t
          ((1 : ℝ) / (p : ℝ) ^ 2)‖ ≤
      (1 / (p : ℝ) ^ 2) * 1 *
        fixedAwayPVGlobalDecayConstant t δ := by gcongr
    _ = fixedAwayPVGlobalDecayConstant t δ / (p : ℝ) ^ 2 := by ring

theorem norm_fixedAwayUnshiftedRest_one_le
    {t δ : ℝ} (N : ℕ)
    (hδ : 0 < δ) (hδt : δ < t) :
    ‖fixedAwayRamanujanProfileBlock (Finset.Icc 2 N)
        (fixedAwayShiftedProfile t δ N 0) 1‖ ≤
      fixedAwayPVGlobalDecayConstant t δ *
        fixedAwayInverseSquareMass := by
  unfold fixedAwayRamanujanProfileBlock
  calc
    ‖∑ p ∈ Finset.Icc 2 N,
        fixedAwayRamanujanProfileTerm
          (fixedAwayShiftedProfile t δ N 0) p 1‖ ≤
      ∑ p ∈ Finset.Icc 2 N,
        ‖fixedAwayRamanujanProfileTerm
          (fixedAwayShiftedProfile t δ N 0) p 1‖ :=
      norm_sum_le _ _
    _ ≤ ∑ p ∈ Finset.Icc 2 N,
        fixedAwayPVGlobalDecayConstant t δ / (p : ℝ) ^ 2 := by
      gcongr with p hp
      exact norm_fixedAwayUnshifted_one_term_le N p hδ hδt
        (by have hpLower := (Finset.mem_Icc.mp hp).1; omega)
    _ = fixedAwayPVGlobalDecayConstant t δ *
        (∑ p ∈ Finset.Icc 2 N, 1 / (p : ℝ) ^ 2) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p _hp
      ring
    _ ≤ fixedAwayPVGlobalDecayConstant t δ *
        fixedAwayInverseSquareMass := by
      apply mul_le_mul_of_nonneg_left _ <|
        fixedAwayPVGlobalDecayConstant_nonneg t δ
      unfold fixedAwayInverseSquareMass
      exact summable_inverseSquare_nat.sum_le_tsum
        (s := Finset.Icc 2 N) (fun p _hp ↦ by positivity)

/-- The logarithmic exponent in the cited Chan--Kumchev theorem. -/
def fixedAwayCkSourceLogExponent : ℕ := 11

/-- A deliberately larger terminal-tail exponent.  It is distinct from
the source theorem's exponent and is chosen above `30`, as in the paper's
safe truncation. -/
def fixedAwayCkTerminalLogExponent : ℕ := 32

def fixedAwayCkTerminal (K : ℕ) : ℕ :=
  ⌊(K : ℝ) /
    Real.log (K : ℝ) ^ fixedAwayCkTerminalLogExponent⌋₊

def FixedAwayChanKumchevHypothesis : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧
    ∀ᶠ K : ℕ in atTop,
      ChanKumchevInitialLongRangeEstimate
        D K (fixedAwayCkTerminal K)

/-- A uniform full initial second-moment estimate at the terminal cutoff
implies the exact fixed-away Chan--Kumchev hypothesis.  This direction is
just restriction to the genuinely long prefixes `K < X²`; in particular,
it introduces no extra arithmetic assumption. -/
theorem fixedAwayChanKumchevHypothesis_of_initialSecondMoment
    {D : ℝ} (hD : 0 ≤ D)
    (hSecond : ∀ᶠ K : ℕ in atTop,
      ChanKumchevInitialSecondMomentEstimate
        D K (fixedAwayCkTerminal K)) :
    FixedAwayChanKumchevHypothesis := by
  refine ⟨D, hD, ?_⟩
  filter_upwards [hSecond] with K hK
  refine ⟨hK.1, ?_⟩
  intro X hX _hLong
  exact hK.2 X hX

/-- Scalar finite-sum form of the preceding bridge.  This exposes the
remaining analytic estimate without Euclidean-space notation:

`initialRawRamanujanBlockCoefficient X n = ∑_{1 ≤ q ≤ X} c_q(n)`.

All quantifiers, the frequency interval `1 ≤ n ≤ 2K`, and the terminal
range are explicit. -/
theorem fixedAwayChanKumchevHypothesis_of_coefficientSecondMoment
    {D : ℝ} (hD : 0 ≤ D)
    (hCoeff : ∀ᶠ K : ℕ in atTop,
      ∀ X ∈ Finset.Icc 1 (fixedAwayCkTerminal K),
        (∑ n ∈ Finset.Icc 1 (2 * K),
          initialRawRamanujanBlockCoefficient X n ^ 2) ≤
            D * (K : ℝ) * (X : ℝ) ^ 2) :
    FixedAwayChanKumchevHypothesis := by
  apply fixedAwayChanKumchevHypothesis_of_initialSecondMoment hD
  filter_upwards [hCoeff] with K hK
  refine ⟨hD, ?_⟩
  intro X hX
  rw [norm_sq_initialRamanujanPrefixVector_eq_coefficients]
  exact hK X hX

/-- Conversely, the fixed-away long-range hypothesis and the already
proved elementary estimate for `X² ≤ K` give a uniform full initial
second-moment estimate, with the explicit harmless change `D ↦ D + 6`.

Thus the existential eventual full-moment statement below is logically
equivalent to `FixedAwayChanKumchevHypothesis`; this pins down the sole
remaining arithmetic input without hiding a range split. -/
theorem fixedAwayChanKumchevHypothesis_iff_initialSecondMoment :
    FixedAwayChanKumchevHypothesis ↔
      ∃ D : ℝ, 0 ≤ D ∧
        ∀ᶠ K : ℕ in atTop,
          ChanKumchevInitialSecondMomentEstimate
            D K (fixedAwayCkTerminal K) := by
  constructor
  · rintro ⟨D, hD, hLong⟩
    refine ⟨D + 6, by linarith, ?_⟩
    filter_upwards [hLong] with K hK
    exact hK.withElementaryRange
  · rintro ⟨D, hD, hSecond⟩
    exact fixedAwayChanKumchevHypothesis_of_initialSecondMoment hD hSecond

private theorem tendsto_log_pow_div_natCast_zero (m : ℕ) :
    Tendsto
      (fun K : ℕ ↦ Real.log (K : ℝ) ^ m / (K : ℝ))
      atTop (nhds 0) := by
  have hreal :=
    Real.tendsto_pow_log_div_mul_add_atTop 1 0 m one_ne_zero
  have hcast : Tendsto (fun K : ℕ ↦ (K : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hcomp := hreal.comp hcast
  simpa only [one_mul, add_zero, Function.comp_apply] using! hcomp

/-- Literal variable check for Chan--Kumchev Theorem 1.2(ii).

With `x_CK = X`, `y_CK = 2K`, and `B_CK = 11`, every genuinely
long prefix `K < X²` below the terminal cutoff eventually lies in
`x_CK ≤ y_CK ≤ x_CK² (log x_CK)^B_CK`.  This keeps the source exponent
`11` separate from the stronger terminal-tail exponent `32`. -/
theorem eventually_fixedAwayCkSourceVariableRange :
    ∀ᶠ K : ℕ in atTop,
      ∀ X ∈ Finset.Icc 1 (fixedAwayCkTerminal K),
        K < X ^ 2 →
          (X : ℝ) ≤ 2 * (K : ℝ) ∧
          2 * (K : ℝ) ≤
            (X : ℝ) ^ 2 *
              Real.log (X : ℝ) ^ fixedAwayCkSourceLogExponent := by
  filter_upwards [eventually_ge_atTop 64] with K hK
  have hKpos : 0 < K := by omega
  have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hKpos
  have hlogK : 0 < Real.log (K : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < K by omega))
  have hlogKOne : 1 ≤ Real.log (K : ℝ) := by
    have hthree : (3 : ℝ) ≤ (K : ℝ) := by
      exact_mod_cast (show 3 ≤ K by omega)
    have hlogThree : 1 ≤ Real.log (3 : ℝ) := by
      exact (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)).2
        Real.exp_one_lt_three.le
    exact hlogThree.trans
      (Real.strictMonoOn_log.monotoneOn
        (show (3 : ℝ) ∈ Set.Ioi 0 by norm_num)
        (show (K : ℝ) ∈ Set.Ioi 0 by exact hKR)
        hthree)
  have hterminalLe : fixedAwayCkTerminal K ≤ K := by
    have hfloor :
        (fixedAwayCkTerminal K : ℝ) ≤
          (K : ℝ) /
            Real.log (K : ℝ) ^ fixedAwayCkTerminalLogExponent := by
      exact Nat.floor_le (by positivity)
    have hquotient :
        (K : ℝ) /
            Real.log (K : ℝ) ^ fixedAwayCkTerminalLogExponent ≤
          (K : ℝ) := by
      exact div_le_self hKR.le (one_le_pow₀ hlogKOne)
    exact_mod_cast hfloor.trans hquotient
  intro X hX hLong
  have hXleK : X ≤ K :=
    (Finset.mem_Icc.mp hX).2.trans hterminalLe
  have hXnine : 9 ≤ X := by
    by_contra hnot
    have hXle : X ≤ 8 := by omega
    have hXsq : X ^ 2 ≤ 8 ^ 2 :=
      Nat.pow_le_pow_left hXle 2
    norm_num at hXsq
    omega
  have hlogNine : (2 : ℝ) ≤ Real.log 9 := by
    apply (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 9)).2
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
    nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
  have hlogX : (2 : ℝ) ≤ Real.log (X : ℝ) := by
    exact hlogNine.trans
      (Real.strictMonoOn_log.monotoneOn
        (show (9 : ℝ) ∈ Set.Ioi 0 by norm_num)
        (show (X : ℝ) ∈ Set.Ioi 0 by
          change (0 : ℝ) < (X : ℝ)
          exact_mod_cast (show 0 < X by omega))
        (by exact_mod_cast hXnine))
  have hlogPow :
      (2 : ℝ) ≤
        Real.log (X : ℝ) ^ fixedAwayCkSourceLogExponent := by
    have hp :
        (2 : ℝ) ^ fixedAwayCkSourceLogExponent ≤
          Real.log (X : ℝ) ^ fixedAwayCkSourceLogExponent :=
      pow_le_pow_left₀ (by norm_num) hlogX _
    have htwo :
        (2 : ℝ) ≤ (2 : ℝ) ^ fixedAwayCkSourceLogExponent := by
      norm_num [fixedAwayCkSourceLogExponent]
    exact htwo.trans hp
  have hKXsq : (K : ℝ) ≤ (X : ℝ) ^ 2 := by
    exact_mod_cast hLong.le
  constructor
  · exact (by
      exact_mod_cast
        hXleK.trans (Nat.le_mul_of_pos_left K (by omega : 0 < 2)))
  · calc
      2 * (K : ℝ) ≤ 2 * (X : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left hKXsq (by norm_num)
      _ = (X : ℝ) ^ 2 * 2 := by ring
      _ ≤ (X : ℝ) ^ 2 *
          Real.log (X : ℝ) ^ fixedAwayCkSourceLogExponent :=
        mul_le_mul_of_nonneg_left hlogPow (sq_nonneg _)

private theorem eventually_fixedAwayCkTerminal_bounds :
    ∀ᶠ K : ℕ in atTop,
      1 ≤ fixedAwayCkTerminal K ∧
      Nat.sqrt K < fixedAwayCkTerminal K ∧
      Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
          Real.sqrt (K : ℝ) /
          (fixedAwayCkTerminal K : ℝ) ≤ 1 := by
  have h64 := tendsto_log_pow_div_natCast_zero 64
  have h67 := tendsto_log_pow_div_natCast_zero 67
  have h64small : ∀ᶠ K : ℕ in atTop,
      Real.log (K : ℝ) ^ 64 / (K : ℝ) < 1 / 16 :=
    h64.eventually_lt_const (by norm_num)
  have h67small : ∀ᶠ K : ℕ in atTop,
      Real.log (K : ℝ) ^ 67 / (K : ℝ) ≤ 1 / 216 := by
    have hlt : ∀ᶠ K : ℕ in atTop,
        Real.log (K : ℝ) ^ 67 / (K : ℝ) < 1 / 216 :=
      h67.eventually_lt_const (by norm_num)
    exact hlt.mono fun _ h ↦ h.le
  filter_upwards [eventually_ge_atTop 3, h64small, h67small] with
      K hK h64K h67K
  have hKR : (0 : ℝ) < (K : ℝ) := by positivity
  have hlog : 0 < Real.log (K : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < K by omega))
  have hlogOne : 1 ≤ Real.log (K : ℝ) := by
    have hthree : (3 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
    have hlogThree : 1 ≤ Real.log (3 : ℝ) := by
      have he : Real.exp 1 < 3 := by
        have := Real.exp_one_lt_d9
        norm_num at this ⊢
        linarith
      exact (Real.le_log_iff_exp_le (by norm_num : 0 < (3 : ℝ))).2 he.le
    have hmono : Real.log (3 : ℝ) ≤ Real.log (K : ℝ) :=
      Real.strictMonoOn_log.monotoneOn
        (show (3 : ℝ) ∈ Set.Ioi 0 by norm_num)
        (show (K : ℝ) ∈ Set.Ioi 0 by exact hKR)
        hthree
    exact hlogThree.trans hmono
  let x : ℝ := (K : ℝ) / Real.log (K : ℝ) ^ 32
  let T : ℕ := fixedAwayCkTerminal K
  have hxPos : 0 < x := by
    dsimp [x]
    positivity
  have hlogPow64 : Real.log (K : ℝ) ^ 64 < (K : ℝ) / 16 := by
    have h := (div_lt_iff₀ hKR).1 h64K
    calc
      Real.log (K : ℝ) ^ 64 < (1 / 16 : ℝ) * (K : ℝ) := h
      _ = (K : ℝ) / 16 := by ring
  have hxTwo : 2 ≤ x := by
    have hlogPow32Pos : 0 < Real.log (K : ℝ) ^ 32 := by positivity
    have hfourLog : 4 * Real.log (K : ℝ) ^ 64 < (K : ℝ) := by
      linarith [hlogPow64]
    have htwoLog : 2 * Real.log (K : ℝ) ^ 32 <
        Real.sqrt (K : ℝ) := by
      apply (sq_lt_sq₀ (by positivity)
        (Real.sqrt_nonneg (K : ℝ))).mp
      rw [mul_pow, Real.sq_sqrt hKR.le]
      norm_num
      simpa only [← pow_mul] using! hfourLog
    have hsqrtK : Real.sqrt (K : ℝ) ≤ (K : ℝ) := by
      rw [Real.sqrt_le_iff]
      have hKone : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast (show 1 ≤ K by omega)
      exact ⟨hKR.le, by nlinarith⟩
    dsimp [x]
    apply (le_div_iff₀ hlogPow32Pos).2
    exact (le_of_lt htwoLog).trans hsqrtK
  have hTfloor : (T : ℝ) ≤ x :=
    Nat.floor_le hxPos.le
  have hxFloor : x < (T : ℝ) + 1 := by
    simpa only [T, x] using! Nat.lt_floor_add_one x
  have hTlower : x / 2 ≤ (T : ℝ) := by
    linarith
  have hTone : 1 ≤ T := by
    exact_mod_cast (show (1 : ℝ) ≤ (T : ℝ) by
      linarith)
  have hsqrtNat : (Nat.sqrt K : ℝ) ≤ Real.sqrt (K : ℝ) := by
    apply (Real.le_sqrt (by positivity) hKR.le).2
    exact_mod_cast Nat.sqrt_le' K
  have hsqrtRealT : Real.sqrt (K : ℝ) < (T : ℝ) := by
    have hlog32 :
        2 * Real.log (K : ℝ) ^ 32 < Real.sqrt (K : ℝ) := by
      apply (sq_lt_sq₀ (by positivity)
        (Real.sqrt_nonneg (K : ℝ))).mp
      rw [mul_pow, Real.sq_sqrt hKR.le]
      norm_num
      simpa only [← pow_mul] using!
        (show 4 * Real.log (K : ℝ) ^ 64 < (K : ℝ) by
          linarith [hlogPow64])
    have hxHalf :
        Real.sqrt (K : ℝ) < x / 2 := by
      have hscale :
          x / 2 = (K : ℝ) /
            (2 * Real.log (K : ℝ) ^ 32) := by
        dsimp [x]
        field_simp [hlog.ne']
      rw [hscale]
      apply (lt_div_iff₀ (by positivity :
        0 < (2 : ℝ) * Real.log (K : ℝ) ^ 32)).2
      calc
        Real.sqrt (K : ℝ) *
            (2 * Real.log (K : ℝ) ^ 32) =
          (2 * Real.log (K : ℝ) ^ 32) *
            Real.sqrt (K : ℝ) := by ring
        _ < Real.sqrt (K : ℝ) * Real.sqrt (K : ℝ) := by
          gcongr
        _ = (K : ℝ) := by
          rw [← sq, Real.sq_sqrt hKR.le]
    exact hxHalf.trans_le hTlower
  have hsqrtT : Nat.sqrt K < T := by
    exact_mod_cast hsqrtNat.trans_lt hsqrtRealT
  have hTposR : (0 : ℝ) < (T : ℝ) := by exact_mod_cast (show 0 < T by omega)
  have hharm :
      (harmonic (2 * K) : ℝ) ≤
        3 * Real.log (K : ℝ) := by
    have hraw := harmonic_le_one_add_log (2 * K)
    have hlogMul :
        Real.log ((2 * K : ℕ) : ℝ) =
          Real.log 2 + Real.log (K : ℝ) := by
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      exact Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hKR.ne'
    rw [hlogMul] at hraw
    have hlogTwo : Real.log 2 ≤ Real.log (K : ℝ) := by
      exact Real.strictMonoOn_log.monotoneOn
        (show (2 : ℝ) ∈ Set.Ioi 0 by norm_num)
        (show (K : ℝ) ∈ Set.Ioi 0 by exact hKR)
        (by exact_mod_cast (show 2 ≤ K by omega))
    linarith
  have hharmNonneg : 0 ≤ (harmonic (2 * K) : ℝ) := by
    exact_mod_cast (harmonic_pos (by omega : 2 * K ≠ 0)).le
  have htailSq :
      (Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
          Real.sqrt (K : ℝ) / (T : ℝ)) ^ 2 ≤ 1 := by
    have hTinv : 1 / (T : ℝ) ≤ 2 / x := by
      calc
        1 / (T : ℝ) ≤ 1 / (x / 2) :=
          one_div_le_one_div_of_le (by positivity) hTlower
        _ = 2 / x := by field_simp [hxPos.ne']
    have hTinv' : (T : ℝ)⁻¹ ≤ 2 / x := by
      simpa only [one_div] using! hTinv
    have htailNonneg :
        0 ≤ Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
          Real.sqrt (K : ℝ) := by positivity
    have hdiv :
        Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
            Real.sqrt (K : ℝ) / (T : ℝ) ≤
          Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
            Real.sqrt (K : ℝ) * (2 / x) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hTinv' htailNonneg
    have hsqBound := pow_le_pow_left₀ (by positivity) hdiv 2
    calc
      (Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
          Real.sqrt (K : ℝ) / (T : ℝ)) ^ 2 ≤
        (Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
          Real.sqrt (K : ℝ) * (2 / x)) ^ 2 := hsqBound
      _ = 8 * (harmonic (2 * K) : ℝ) ^ 3 *
          Real.log (K : ℝ) ^ 64 / (K : ℝ) := by
        rw [mul_pow, mul_pow,
          Real.sq_sqrt (by positivity :
            0 ≤ 2 * (harmonic (2 * K) : ℝ) ^ 3),
          Real.sq_sqrt hKR.le]
        dsimp [x]
        field_simp [hKR.ne', hlog.ne']
        ring
      _ ≤ 216 * Real.log (K : ℝ) ^ 67 / (K : ℝ) := by
        have hcube :
            (harmonic (2 * K) : ℝ) ^ 3 ≤
              (3 * Real.log (K : ℝ)) ^ 3 :=
          pow_le_pow_left₀ hharmNonneg hharm 3
        calc
          8 * (harmonic (2 * K) : ℝ) ^ 3 *
              Real.log (K : ℝ) ^ 64 / (K : ℝ) ≤
            8 * (3 * Real.log (K : ℝ)) ^ 3 *
              Real.log (K : ℝ) ^ 64 / (K : ℝ) := by
                gcongr
          _ = 216 * Real.log (K : ℝ) ^ 67 / (K : ℝ) := by ring
      _ ≤ 1 := by
        calc
          216 * Real.log (K : ℝ) ^ 67 / (K : ℝ) =
              216 * (Real.log (K : ℝ) ^ 67 / (K : ℝ)) := by ring
          _ ≤ 216 * (1 / 216 : ℝ) :=
            mul_le_mul_of_nonneg_left h67K (by norm_num)
          _ = 1 := by norm_num
  have htailNonneg :
      0 ≤ Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
        Real.sqrt (K : ℝ) / (T : ℝ) := by positivity
  have htail :
      Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
          Real.sqrt (K : ℝ) / (T : ℝ) ≤ 1 := by
    nlinarith [sq_nonneg
      (Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
        Real.sqrt (K : ℝ) / (T : ℝ) - 1)]
  exact ⟨by simpa only [T] using! hTone,
    by simpa only [T] using! hsqrtT,
    by simpa only [T] using! htail⟩

def fixedAwayUnshiftedCkShellUniformBound
    (C T0 δ : ℝ) : ℝ :=
  2 * fixedAwayUnshiftedLowShellUniformConstant T0 δ +
    24 * C *
      fixedAwayUnshiftedTransitionMultiplierUniformConstant T0 δ +
    12 * fixedAwayUnshiftedHighMultiplierUniformConstant T0 δ

theorem fixedAwayUnshiftedCkShellUniformBound_nonneg
    {C T0 δ : ℝ} (hC : 0 ≤ C) (hT0 : 0 ≤ T0) :
    0 ≤ fixedAwayUnshiftedCkShellUniformBound C T0 δ := by
  have hlocal := fixedAwayPVLocalUniformBound_nonneg hT0
  have hderiv0 :=
    fixedAwayDerivativeUniformBound_nonneg hT0 δ 0
  have hderiv2 :=
    fixedAwayDerivativeUniformBound_nonneg hT0 δ 2
  unfold fixedAwayUnshiftedCkShellUniformBound
  have hlow : 0 ≤ fixedAwayUnshiftedLowShellUniformConstant T0 δ := by
    unfold fixedAwayUnshiftedLowShellUniformConstant
      fixedAwayPVInverseDecayUniformConstant
      fixedAwayDerivativeCauchyUniformConstant
    positivity
  have htransition :
      0 ≤ fixedAwayUnshiftedTransitionMultiplierUniformConstant T0 δ := by
    unfold fixedAwayUnshiftedTransitionMultiplierUniformConstant
      fixedAwayPVGlobalDecayUniformConstant
    positivity
  have hhigh :
      0 ≤ fixedAwayUnshiftedHighMultiplierUniformConstant T0 δ := by
    unfold fixedAwayUnshiftedHighMultiplierUniformConstant
      fixedAwayPVGlobalDecayUniformConstant
    positivity
  positivity

theorem norm_fixedAwayUnshiftedFiniteVector_two_le_ckTerminal_uniform
    (C : ℝ) {t δ T0 : ℝ} (K N : ℕ)
    (hCK : RamanujanPrefixL2Estimate C K
      (fixedAwayCkTerminal K))
    (hterminal :
      1 ≤ fixedAwayCkTerminal K ∧
      Nat.sqrt K < fixedAwayCkTerminal K ∧
      Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
          Real.sqrt (K : ℝ) /
          (fixedAwayCkTerminal K : ℝ) ≤ 1)
    (hδ : 0 < δ) (hδt : δ < t) (htT0 : t ≤ T0)
    (hN : 1 ≤ N) :
    ‖fixedAwayUnshiftedFiniteVector t δ K 2 N‖ ≤
      fixedAwayUnshiftedCkShellUniformBound C T0 δ := by
  have hK : 0 < K := by
    by_contra hK0
    have : K = 0 := Nat.eq_zero_of_not_pos hK0
    subst K
    norm_num [fixedAwayCkTerminal,
      fixedAwayCkTerminalLogExponent] at hterminal
  have hT0 : 0 ≤ T0 :=
    hδ.le.trans hδt.le |>.trans htT0
  have hlocal := fixedAwayPVLocalUniformBound_nonneg hT0
  have hderiv0 :=
    fixedAwayDerivativeUniformBound_nonneg hT0 δ 0
  have hderiv2 :=
    fixedAwayDerivativeUniformBound_nonneg hT0 δ 2
  by_cases hNT : N ≤ fixedAwayCkTerminal K
  · have hraw :=
      norm_fixedAwayUnshiftedFiniteVector_two_le_of_prefixEstimate_uniform
        C K (fixedAwayCkTerminal K) N hCK
        hδ hδt htT0 hK hN hNT
    calc
      ‖fixedAwayUnshiftedFiniteVector t δ K 2 N‖ ≤
          2 * fixedAwayUnshiftedLowShellUniformConstant T0 δ +
            24 * C *
              fixedAwayUnshiftedTransitionMultiplierUniformConstant T0 δ :=
        hraw
      _ ≤ fixedAwayUnshiftedCkShellUniformBound C T0 δ := by
        unfold fixedAwayUnshiftedCkShellUniformBound
        have hhigh :
            0 ≤ fixedAwayUnshiftedHighMultiplierUniformConstant T0 δ := by
          unfold fixedAwayUnshiftedHighMultiplierUniformConstant
            fixedAwayPVGlobalDecayUniformConstant
          positivity
        linarith
  · have hTN : fixedAwayCkTerminal K < N := lt_of_not_ge hNT
    have hraw :=
      norm_fixedAwayUnshiftedFiniteVector_two_le_prefixThenDivisor_uniform
        C K (fixedAwayCkTerminal K) N hCK
        hδ hδt htT0 hK hterminal.1 hterminal.2.1 hTN
    have hhigh :
        0 ≤ fixedAwayUnshiftedHighMultiplierUniformConstant T0 δ := by
      unfold fixedAwayUnshiftedHighMultiplierUniformConstant
        fixedAwayPVGlobalDecayUniformConstant
      positivity
    have htailNonneg :
        0 ≤ 12 *
          (Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
            Real.sqrt (K : ℝ) /
            (fixedAwayCkTerminal K : ℝ)) := by positivity
    calc
      ‖fixedAwayUnshiftedFiniteVector t δ K 2 N‖ ≤
        2 * fixedAwayUnshiftedLowShellUniformConstant T0 δ +
          24 * C *
            fixedAwayUnshiftedTransitionMultiplierUniformConstant T0 δ +
          (12 *
            Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
            Real.sqrt (K : ℝ) /
            (fixedAwayCkTerminal K : ℝ)) *
            fixedAwayUnshiftedHighMultiplierUniformConstant T0 δ := hraw
      _ ≤ 2 * fixedAwayUnshiftedLowShellUniformConstant T0 δ +
          24 * C *
            fixedAwayUnshiftedTransitionMultiplierUniformConstant T0 δ +
          12 * fixedAwayUnshiftedHighMultiplierUniformConstant T0 δ := by
        gcongr
        calc
          12 *
              Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
              Real.sqrt (K : ℝ) /
              (fixedAwayCkTerminal K : ℝ) =
            12 * (Real.sqrt (2 * (harmonic (2 * K) : ℝ) ^ 3) *
              Real.sqrt (K : ℝ) /
              (fixedAwayCkTerminal K : ℝ)) := by ring
          _ ≤ 12 * 1 :=
            mul_le_mul_of_nonneg_left hterminal.2.2 (by norm_num)
          _ = 12 := by norm_num
      _ = fixedAwayUnshiftedCkShellUniformBound C T0 δ := rfl

/-! ## The complete unshifted carrier away from the two fixed endpoints -/

def fixedAwayZeroCarrierRestCoefficients
    (t δ : ℝ) (N : ℕ) (n : ℤ) : ℂ :=
  fixedAwayRamanujanProfileBlock (Finset.Icc 2 N)
    (fixedAwayShiftedProfile t δ N 0) n

theorem fixedAwayUnshiftedFiniteVector_two_apply_eq_zeroCarrierRest
    (t δ : ℝ) (K N : ℕ) (n : nearDyadicIndex K) :
    fixedAwayUnshiftedFiniteVector t δ K 2 N n =
      fixedAwayZeroCarrierRestCoefficients t δ N ((n : ℕ) : ℤ) := by
  rw [fixedAwayUnshiftedFiniteVector_apply]
  unfold fixedAwayZeroCarrierRestCoefficients
    fixedAwayRamanujanProfileBlock fixedAwayRamanujanProfileTerm
    fixedAwayShiftedProfile fixedAwayScaledPV
    nearBernoulliCarrierFrequency
  apply Finset.sum_congr rfl
  intro p _hp
  push_cast
  ring_nf

theorem norm_sq_fixedAwayUnshiftedFiniteVector_two_eq_zeroCarrierRest
    (t δ : ℝ) (K N : ℕ) :
    ‖fixedAwayUnshiftedFiniteVector t δ K 2 N‖ ^ 2 =
      ∑ n ∈ Finset.Ioc K (2 * K),
        ‖fixedAwayZeroCarrierRestCoefficients
          t δ N (n : ℤ)‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq]
  rw [← Finset.sum_coe_sort (Finset.Ioc K (2 * K))]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [fixedAwayUnshiftedFiniteVector_two_apply_eq_zeroCarrierRest]

theorem summable_fixedAwayZeroCarrierRestCoefficients_norm_sq
    {t δ : ℝ} (N : ℕ) (hδ : 0 < δ) (hδt : δ < t) :
    Summable fun n : ℤ ↦
      ‖fixedAwayZeroCarrierRestCoefficients t δ N n‖ ^ 2 := by
  unfold fixedAwayZeroCarrierRestCoefficients
  apply summable_fixedAwayRamanujanProfileBlock_norm_sq
  intro p hp p' hp'
  exact summable_fixedAwayShiftedProfile_hermitianRamanujanMultiplier
    hδ hδt
      (by have := (Finset.mem_Icc.mp hp).1; omega)
      (by have := (Finset.mem_Icc.mp hp').1; omega)

/-- The frequency blocks `2^s < n ≤ 2^(s+1)` partition the positive
frequencies `1 < n ≤ 2^H` literally, including every endpoint once. -/
theorem sum_sq_norm_fixedAwayUnshiftedFiniteVector_range_eq
    (t δ : ℝ) (N H : ℕ) :
    ∑ s ∈ Finset.range H,
        ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ s) 2 N‖ ^ 2 =
      ∑ n ∈ Finset.Ioc (1 : ℕ) (2 ^ H),
        ‖fixedAwayZeroCarrierRestCoefficients
          t δ N (n : ℤ)‖ ^ 2 := by
  induction H with
  | zero => simp
  | succ H ih =>
      rw [Finset.sum_range_succ, ih,
        norm_sq_fixedAwayUnshiftedFiniteVector_two_eq_zeroCarrierRest]
      have hpow : 2 * 2 ^ H = 2 ^ (H + 1) := by
        rw [pow_succ]
        ring
      rw [hpow]
      exact Finset.sum_Ioc_consecutive
        (fun n : ℕ ↦
          ‖fixedAwayZeroCarrierRestCoefficients
            t δ N (n : ℤ)‖ ^ 2)
        Nat.one_le_two_pow
        (Nat.pow_le_pow_right (by omega : 0 < 2) (Nat.le_succ H))

def fixedAwayUnshiftedInitialShellUniformBound
    (T0 δ : ℝ) (s : ℕ) : ℝ :=
  2 * fixedAwayUnshiftedLowShellUniformConstant T0 δ +
    24 * Real.sqrt
      (2 * (harmonic (2 * 2 ^ s) : ℝ) ^ 3) *
      fixedAwayUnshiftedTransitionMultiplierUniformConstant T0 δ

theorem fixedAwayUnshiftedInitialShellUniformBound_nonneg
    {T0 δ : ℝ} (hT0 : 0 ≤ T0) (s : ℕ) :
    0 ≤ fixedAwayUnshiftedInitialShellUniformBound T0 δ s := by
  have hlocal := fixedAwayPVLocalUniformBound_nonneg hT0
  have hderiv0 := fixedAwayDerivativeUniformBound_nonneg hT0 δ 0
  have hderiv2 := fixedAwayDerivativeUniformBound_nonneg hT0 δ 2
  unfold fixedAwayUnshiftedInitialShellUniformBound
    fixedAwayUnshiftedLowShellUniformConstant
    fixedAwayUnshiftedTransitionMultiplierUniformConstant
    fixedAwayPVInverseDecayUniformConstant
    fixedAwayDerivativeCauchyUniformConstant
    fixedAwayPVGlobalDecayUniformConstant
  positivity

/-- A single source-faithful Chan--Kumchev prefix hypothesis gives one
threshold-uniform `O(H)` bound for the first `H` positive frequency shells.
The finitely many shells before the arithmetic hypothesis starts are
controlled by the proved divisor-square estimate. -/
theorem exists_fixedAwayZeroCarrierDyadicLinearBound
    (hCKsource : FixedAwayChanKumchevHypothesis)
    {δ T0 : ℝ} (hδ : 0 < δ) (hT0 : δ < T0) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (t : ℝ) (N H : ℕ), δ < t → t ≤ T0 → 1 ≤ N →
        ∑ s ∈ Finset.range H,
            ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ s) 2 N‖ ^ 2
          ≤ (H : ℝ) * B := by
  obtain ⟨D, hD, hCKevent⟩ := hCKsource
  let C : ℝ := Real.sqrt (D + 6)
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  rcases (eventually_atTop.1 hCKevent) with ⟨K₁, hK₁⟩
  rcases (eventually_atTop.1
    eventually_fixedAwayCkTerminal_bounds) with ⟨K₂, hK₂⟩
  let K₀ : ℕ := max K₁ K₂
  let I : ℝ :=
    ∑ s ∈ Finset.range K₀,
      fixedAwayUnshiftedInitialShellUniformBound T0 δ s ^ 2
  let Bck : ℝ :=
    fixedAwayUnshiftedCkShellUniformBound C T0 δ
  let B : ℝ := I + Bck ^ 2
  have hT0nonneg : 0 ≤ T0 := hδ.le.trans hT0.le
  have hI : 0 ≤ I := by
    dsimp [I]
    exact Finset.sum_nonneg fun s _hs ↦ sq_nonneg _
  have hBck : 0 ≤ Bck := by
    dsimp [Bck]
    exact fixedAwayUnshiftedCkShellUniformBound_nonneg hC hT0nonneg
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  refine ⟨B, hB, ?_⟩
  intro t N H hδt htT0 hN
  have hpowSelf : ∀ k : ℕ, k ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        have hone : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        omega
  have hpoint : ∀ s ∈ Finset.range H,
      ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ s) 2 N‖ ^ 2 ≤ B := by
    intro s hs
    by_cases hs₀ : s < K₀
    · let Cs : ℝ :=
        Real.sqrt (2 * (harmonic (2 * 2 ^ s) : ℝ) ^ 3)
      have hprefix :
          RamanujanPrefixL2Estimate Cs (2 ^ s) N := by
        dsimp [Cs]
        exact
          (chanKumchevInitialSecondMomentEstimate_divisorSquare
            (2 ^ s) N).toDyadic.toL2
      have hraw :=
        norm_fixedAwayUnshiftedFiniteVector_two_le_of_prefixEstimate_uniform
          Cs (2 ^ s) N N hprefix hδ hδt htT0
          (by positivity) hN le_rfl
      have hraw' :
          ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ s) 2 N‖ ≤
            fixedAwayUnshiftedInitialShellUniformBound T0 δ s := by
        simpa only [Cs] using! hraw
      have hsq :
          ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ s) 2 N‖ ^ 2 ≤
            fixedAwayUnshiftedInitialShellUniformBound T0 δ s ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hraw' 2
      have htermI :
          fixedAwayUnshiftedInitialShellUniformBound T0 δ s ^ 2 ≤ I := by
        dsimp [I]
        exact Finset.single_le_sum
          (fun j _hj ↦ sq_nonneg
            (fixedAwayUnshiftedInitialShellUniformBound T0 δ j))
          (Finset.mem_range.mpr hs₀)
      exact hsq.trans (htermI.trans (by
        dsimp [B]
        exact le_add_of_nonneg_right (sq_nonneg Bck)))
    · have hK₀s : K₀ ≤ s := le_of_not_gt hs₀
      have hK₁pow : K₁ ≤ 2 ^ s := by
        have hK₁s : K₁ ≤ s := (le_max_left K₁ K₂).trans hK₀s
        exact hK₁s.trans (hpowSelf s)
      have hK₂pow : K₂ ≤ 2 ^ s := by
        have hK₂s : K₂ ≤ s := (le_max_right K₁ K₂).trans hK₀s
        exact hK₂s.trans (hpowSelf s)
      have hprefix :
          RamanujanPrefixL2Estimate C (2 ^ s)
            (fixedAwayCkTerminal (2 ^ s)) := by
        dsimp [C]
        exact
          (hK₁ (2 ^ s) hK₁pow).withElementaryRange.toDyadic.toL2
      have hterminal := hK₂ (2 ^ s) hK₂pow
      have hraw :=
        norm_fixedAwayUnshiftedFiniteVector_two_le_ckTerminal_uniform
          C (2 ^ s) N hprefix hterminal hδ hδt htT0 hN
      have hsq :
          ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ s) 2 N‖ ^ 2 ≤
            Bck ^ 2 := by
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        simpa only [Bck] using! hraw
      exact hsq.trans (by
        dsimp [B]
        exact le_add_of_nonneg_left hI)
  calc
    ∑ s ∈ Finset.range H,
        ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ s) 2 N‖ ^ 2 ≤
        ∑ _s ∈ Finset.range H, B := by
      exact Finset.sum_le_sum hpoint
    _ = (H : ℝ) * B := by simp

private theorem sum_inv_pow_two_range_le_two (H : ℕ) :
    (∑ r ∈ Finset.range H, 1 / (2 : ℝ) ^ r) ≤ 2 := by
  have h := geom_sum_Ico_le_of_lt_one
    (m := 0) (n := H) (x := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  calc
    (∑ r ∈ Finset.range H, 1 / (2 : ℝ) ^ r) =
        ∑ r ∈ Finset.Ico 0 H, (1 / 2 : ℝ) ^ r := by
      apply Finset.sum_congr
      · ext r
        simp
      · intro r _hr
        simp only [one_div]
        exact (inv_pow (2 : ℝ) r).symm
    _ ≤ (1 / 2 : ℝ) ^ 0 / (1 - (1 / 2 : ℝ)) := h
    _ = 2 := by norm_num

/-- Starting at the least binary power above `N²`, the positive-frequency
shell energy is a genuine geometric series. -/
theorem sum_sq_norm_fixedAwayUnshiftedFiniteVector_clogTail_le
    {t δ T0 : ℝ} (N H : ℕ)
    (hδ : 0 < δ) (hδt : δ < t) (htT0 : t ≤ T0) (hN : 0 < N) :
    ∑ r ∈ Finset.range H,
        ‖fixedAwayUnshiftedFiniteVector t δ
          (2 ^ (Nat.clog 2 (N ^ 2) + r)) 2 N‖ ^ 2 ≤
      8 * fixedAwayUnshiftedLowShellUniformConstant T0 δ ^ 2 := by
  let R : ℕ := Nat.clog 2 (N ^ 2)
  have hNR : N ^ 2 ≤ 2 ^ R := by
    dsimp [R]
    exact Nat.le_pow_clog (by omega) (N ^ 2)
  have hT0nonneg : 0 ≤ T0 := hδ.le.trans hδt.le |>.trans htT0
  have hCu :
      0 ≤ fixedAwayUnshiftedLowShellUniformConstant T0 δ := by
    have hderiv2 := fixedAwayDerivativeUniformBound_nonneg hT0nonneg δ 2
    have hderiv0 := fixedAwayDerivativeUniformBound_nonneg hT0nonneg δ 0
    unfold fixedAwayUnshiftedLowShellUniformConstant
      fixedAwayPVInverseDecayUniformConstant
      fixedAwayDerivativeCauchyUniformConstant
    exact mul_nonneg
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg 42))
      (add_nonneg
        (mul_nonneg (by norm_num)
          (div_nonneg hderiv2 (sq_nonneg (2 * Real.pi))))
        (mul_nonneg (by norm_num)
          (mul_nonneg (by norm_num) (add_nonneg hderiv0 hderiv2))))
  have hpoint : ∀ r ∈ Finset.range H,
      ‖fixedAwayUnshiftedFiniteVector t δ
          (2 ^ (R + r)) 2 N‖ ^ 2 ≤
        4 * fixedAwayUnshiftedLowShellUniformConstant T0 δ ^ 2 /
          (2 : ℝ) ^ r := by
    intro r _hr
    have hK : 0 < 2 ^ (R + r) := by positivity
    have hRK : 2 ^ R ≤ 2 ^ (R + r) :=
      Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
    have hNK : N ^ 2 ≤ 2 ^ (R + r) := hNR.trans hRK
    have hraw := norm_fixedAwayUnshiftedFiniteVector_two_le_lowRange
      (2 ^ (R + r)) N hδ hδt hK hN hNK
    have hC := fixedAwayUnshiftedLowShellConstant_le_uniform
      hδ hδt.le htT0
    have hrawU :
        ‖fixedAwayUnshiftedFiniteVector t δ
            (2 ^ (R + r)) 2 N‖ ≤
          2 * fixedAwayUnshiftedLowShellUniformConstant T0 δ *
            (N : ℝ) / Real.sqrt ((2 ^ (R + r) : ℕ) : ℝ) := by
      exact hraw.trans (by
        gcongr
        )
    have hrightNonneg :
        0 ≤ 2 * fixedAwayUnshiftedLowShellUniformConstant T0 δ *
          (N : ℝ) / Real.sqrt ((2 ^ (R + r) : ℕ) : ℝ) := by
      positivity
    calc
      ‖fixedAwayUnshiftedFiniteVector t δ
          (2 ^ (R + r)) 2 N‖ ^ 2 ≤
        (2 * fixedAwayUnshiftedLowShellUniformConstant T0 δ *
          (N : ℝ) / Real.sqrt ((2 ^ (R + r) : ℕ) : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hrawU 2
      _ = 4 * fixedAwayUnshiftedLowShellUniformConstant T0 δ ^ 2 *
          (N : ℝ) ^ 2 / (2 : ℝ) ^ (R + r) := by
        rw [div_pow, mul_pow, mul_pow,
          Real.sq_sqrt (by positivity :
            0 ≤ ((2 ^ (R + r) : ℕ) : ℝ))]
        norm_num
      _ ≤ 4 * fixedAwayUnshiftedLowShellUniformConstant T0 δ ^ 2 *
          (2 : ℝ) ^ R / (2 : ℝ) ^ (R + r) := by
        gcongr
        exact_mod_cast hNR
      _ = 4 * fixedAwayUnshiftedLowShellUniformConstant T0 δ ^ 2 /
          (2 : ℝ) ^ r := by
        rw [pow_add]
        field_simp
  calc
    ∑ r ∈ Finset.range H,
        ‖fixedAwayUnshiftedFiniteVector t δ
          (2 ^ (Nat.clog 2 (N ^ 2) + r)) 2 N‖ ^ 2 =
        ∑ r ∈ Finset.range H,
          ‖fixedAwayUnshiftedFiniteVector t δ
            (2 ^ (R + r)) 2 N‖ ^ 2 := by rfl
    _ ≤ ∑ r ∈ Finset.range H,
        4 * fixedAwayUnshiftedLowShellUniformConstant T0 δ ^ 2 /
          (2 : ℝ) ^ r := Finset.sum_le_sum hpoint
    _ = 4 * fixedAwayUnshiftedLowShellUniformConstant T0 δ ^ 2 *
        ∑ r ∈ Finset.range H, 1 / (2 : ℝ) ^ r := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring
    _ ≤ 4 * fixedAwayUnshiftedLowShellUniformConstant T0 δ ^ 2 * 2 := by
      exact mul_le_mul_of_nonneg_left
        (sum_inv_pow_two_range_le_two H)
        (mul_nonneg (by norm_num) (sq_nonneg _))
    _ = 8 * fixedAwayUnshiftedLowShellUniformConstant T0 δ ^ 2 := by ring

theorem fixedAwayZeroCarrierRestCoefficients_zero
    (t δ : ℝ) (N : ℕ) :
    fixedAwayZeroCarrierRestCoefficients t δ N 0 = 0 := by
  simp [fixedAwayZeroCarrierRestCoefficients,
    fixedAwayRamanujanProfileBlock, fixedAwayRamanujanProfileTerm,
    fixedAwayShiftedProfile, fixedAwayScaledPV,
    nearBernoulliCarrierFrequency, fixedAwayPVTransform_zero]

/-- Complete positive-frequency energy of the zero carrier.  The only
arithmetic input is `FixedAwayChanKumchevHypothesis`; the displayed
binary-shell count is the full logarithmic loss. -/
theorem exists_tsum_fixedAwayZeroCarrierRest_nat_le
    (hCKsource : FixedAwayChanKumchevHypothesis)
    {δ T0 : ℝ} (hδ : 0 < δ) (hT0 : δ < T0) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ (t : ℝ) (N : ℕ), δ < t → t ≤ T0 → 1 ≤ N →
        (∑' n : ℕ,
          ‖fixedAwayZeroCarrierRestCoefficients
            t δ N (n : ℤ)‖ ^ 2) ≤
          (fixedAwayPVGlobalDecayConstant t δ *
              fixedAwayInverseSquareMass) ^ 2 +
            (Nat.clog 2 (N ^ 2) : ℝ) * B +
            8 * fixedAwayUnshiftedLowShellUniformConstant T0 δ ^ 2 := by
  obtain ⟨B, hB, hdyadic⟩ :=
    exists_fixedAwayZeroCarrierDyadicLinearBound
      hCKsource hδ hT0
  refine ⟨B, hB, ?_⟩
  intro t N hδt htT0 hN
  let R : ℕ := Nat.clog 2 (N ^ 2)
  let f : ℕ → ℝ := fun n ↦
    ‖fixedAwayZeroCarrierRestCoefficients t δ N (n : ℤ)‖ ^ 2
  let C1 : ℝ :=
    fixedAwayPVGlobalDecayConstant t δ *
      fixedAwayInverseSquareMass
  let Tail : ℝ :=
    8 * fixedAwayUnshiftedLowShellUniformConstant T0 δ ^ 2
  have hfzero : f 0 = 0 := by
    dsimp [f]
    rw [fixedAwayZeroCarrierRestCoefficients_zero, norm_zero,
      zero_pow (by omega : (2 : ℕ) ≠ 0)]
  have hC1 : 0 ≤ C1 := by
    dsimp [C1]
    exact mul_nonneg
      (fixedAwayPVGlobalDecayConstant_nonneg t δ)
      fixedAwayInverseSquareMass_nonneg
  have hfone : f 1 ≤ C1 ^ 2 := by
    dsimp [f, C1]
    exact pow_le_pow_left₀ (norm_nonneg _)
      (norm_fixedAwayUnshiftedRest_one_le N hδ hδt) 2
  have hpowSelf : ∀ k : ℕ, k ≤ 2 ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ]
        have hone : 1 ≤ 2 ^ k := Nat.one_le_two_pow
        omega
  apply Real.tsum_le_of_sum_range_le (fun n ↦ sq_nonneg _)
  intro k
  let E : ℕ := max R k
  let H : ℕ := E - R
  let T : Finset ℕ :=
    insert 0 (insert 1 (Finset.Ioc (1 : ℕ) (2 ^ E)))
  have hRE : R ≤ E := by
    dsimp [E]
    exact le_max_left _ _
  have hkE : k ≤ E := by
    dsimp [E]
    exact le_max_right _ _
  have hRH : R + H = E := by
    dsimp [H]
    omega
  have hkPow : k ≤ 2 ^ E := hkE.trans (hpowSelf E)
  have hsubset : Finset.range k ⊆ T := by
    intro n hn
    have hnk : n < k := Finset.mem_range.mp hn
    have hnPow : n ≤ 2 ^ E := (Nat.le_of_lt hnk).trans hkPow
    simp only [T, Finset.mem_insert, Finset.mem_Ioc]
    omega
  have hfirst :
      ∑ s ∈ Finset.range R,
          ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ s) 2 N‖ ^ 2 ≤
        (R : ℝ) * B :=
    hdyadic t N R hδt htT0 hN
  have htail :
      ∑ r ∈ Finset.range H,
          ‖fixedAwayUnshiftedFiniteVector t δ
            (2 ^ (R + r)) 2 N‖ ^ 2 ≤ Tail := by
    dsimp [R, Tail]
    exact sum_sq_norm_fixedAwayUnshiftedFiniteVector_clogTail_le
      N H hδ hδt htT0 (by omega)
  have hshell :
      ∑ s ∈ Finset.range E,
          ‖fixedAwayUnshiftedFiniteVector t δ (2 ^ s) 2 N‖ ^ 2 ≤
        (R : ℝ) * B + Tail := by
    rw [← hRH, Finset.sum_range_add]
    exact add_le_add hfirst htail
  have hfinite :
      ∑ n ∈ Finset.Ioc (1 : ℕ) (2 ^ E), f n ≤
        (R : ℝ) * B + Tail := by
    rw [← sum_sq_norm_fixedAwayUnshiftedFiniteVector_range_eq
      t δ N E]
    simpa only [f] using! hshell
  calc
    ∑ n ∈ Finset.range k, f n ≤ ∑ n ∈ T, f n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro n _hn _hnot
      exact sq_nonneg _
    _ = f 0 + f 1 + ∑ n ∈ Finset.Ioc (1 : ℕ) (2 ^ E), f n := by
      simp [T, add_assoc]
    _ ≤ C1 ^ 2 + ((R : ℝ) * B + Tail) := by
      rw [hfzero, zero_add]
      exact add_le_add hfone hfinite
    _ = (fixedAwayPVGlobalDecayConstant t δ *
              fixedAwayInverseSquareMass) ^ 2 +
            (Nat.clog 2 (N ^ 2) : ℝ) * B +
            8 * fixedAwayUnshiftedLowShellUniformConstant T0 δ ^ 2 := by
      dsimp [C1, R, Tail]
      ring

/-! ## Exact denominator decomposition of every shifted carrier -/

theorem fixedAwayFullCarrierBlock_eq_four_denominator_ranges
    (t δ : ℝ) (N : ℕ) (ell n : ℤ) (Q₁ Q₂ : ℕ)
    (hQ₁ : 2 ≤ Q₁)
    (hQ₁Q₂ : Q₁ ≤ Q₂) (hQ₂N : Q₂ ≤ N) :
    fixedAwayFullCarrierBlock N t δ N ell n =
      fixedAwayShiftedFinitePrefix t δ N ell n +
        (fixedAwayShiftedDenominatorRangeCoefficients
          t δ N ell 2 Q₁ n +
        (fixedAwayShiftedDenominatorRangeCoefficients
          t δ N ell Q₁ Q₂ n +
        fixedAwayShiftedPartialDyadicBlock
          (Finset.Ioc Q₂ N) t δ N ell n)) := by
  let g : ℕ → ℂ := fun p ↦
    fixedAwayRamanujanProfileTerm
      (fixedAwayShiftedProfile t δ N ell) p n
  have hfullSet : Finset.Icc 1 N =
      Finset.Icc 1 2 ∪ Finset.Ioc 2 N := by
    ext p
    simp only [Finset.mem_Icc, Finset.mem_union, Finset.mem_Ioc]
    omega
  have hdisjointFull :
      Disjoint (Finset.Icc 1 2) (Finset.Ioc 2 N) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    have hp' := Finset.mem_Icc.mp hp
    have hq' := Finset.mem_Ioc.mp hq
    omega
  have htail :
      (∑ p ∈ Finset.Ioc 2 N, g p) =
        (∑ p ∈ Finset.Ioc 2 Q₁, g p) +
          ((∑ p ∈ Finset.Ioc Q₁ Q₂, g p) +
            ∑ p ∈ Finset.Ioc Q₂ N, g p) := by
    calc
      (∑ p ∈ Finset.Ioc 2 N, g p) =
          (∑ p ∈ Finset.Ioc 2 Q₁, g p) +
            ∑ p ∈ Finset.Ioc Q₁ N, g p :=
        (Finset.sum_Ioc_consecutive g hQ₁
          (hQ₁Q₂.trans hQ₂N)).symm
      _ = (∑ p ∈ Finset.Ioc 2 Q₁, g p) +
          ((∑ p ∈ Finset.Ioc Q₁ Q₂, g p) +
            ∑ p ∈ Finset.Ioc Q₂ N, g p) := by
        rw [Finset.sum_Ioc_consecutive g hQ₁Q₂ hQ₂N]
  have hprefix :
      (∑ p ∈ Finset.Icc 1 2, g p) =
        fixedAwayShiftedFinitePrefix t δ N ell n := by
    have hsmall : Finset.Icc 1 2 = {1, 2} := by decide
    rw [hsmall]
    simp [g, fixedAwayShiftedFinitePrefix,
      fixedAwayShiftedSingletonOne, fixedAwayShiftedDyadicBlock,
      fixedAwayDyadicDenominators, fixedAwayRamanujanProfileBlock]
  unfold fixedAwayFullCarrierBlock fixedAwayRamanujanProfileBlock
    fixedAwayShiftedDenominatorRangeCoefficients
    fixedAwayShiftedPartialDyadicBlock
  change (∑ p ∈ Finset.Icc 1 N, g p) = _
  rw [hfullSet, Finset.sum_union hdisjointFull, hprefix, htail]
  simp only [fixedAwayRamanujanProfileBlock]
  rfl

theorem fixedAwayFullCarrierBlock_eq_explicit_ranges
    (t δ : ℝ) (N : ℕ) (ell n : ℤ)
    (hN : 4 ≤ N)
    (hroom : nearCarrierGapWidth (Real.log (N : ℝ)) + 1 ≤
      nearCarrierLogExponent N) :
    fixedAwayFullCarrierBlock N t δ N ell n =
      fixedAwayShiftedFinitePrefix t δ N ell n +
        (fixedAwayShiftedDyadicTotalSum t δ N
          (nearCarrierLowBlockCount N (Real.log (N : ℝ))) ell n +
        (fixedAwayShiftedExponentFinsetSum
          (nearCarrierDyadicRangeExponents
            (nearCarrierHighStart N (Real.log (N : ℝ)))
            (nearCarrierGapWidth (Real.log (N : ℝ))))
          t δ N ell n +
        fixedAwayShiftedPartialDyadicBlock
          (Finset.Ioc (2 ^ nearCarrierLogExponent N) N)
          t δ N ell n)) := by
  let L : ℝ := Real.log (N : ℝ)
  let M : ℕ := nearCarrierLowBlockCount N L
  let S : ℕ := nearCarrierHighStart N L
  let H : ℕ := nearCarrierGapWidth L
  let R : ℕ := nearCarrierLogExponent N
  let Q₁ : ℕ := 2 ^ (M + 1)
  let Q₂ : ℕ := 2 ^ R
  have hNpos : 0 < N := by omega
  have hS : 1 ≤ S := by
    dsimp [S, nearCarrierHighStart]
    omega
  have hQ₁ : 2 ≤ Q₁ := by
    dsimp [Q₁]
    exact Nat.pow_le_pow_right (by omega : 0 < 2) (by omega : 1 ≤ M + 1)
  have hQ₁Q₂ : Q₁ ≤ Q₂ := by
    apply Nat.pow_le_pow_right (by omega : 0 < 2)
    dsimp [Q₁, Q₂, M, R, nearCarrierLowBlockCount]
    omega
  have hQ₂N : Q₂ ≤ N := by
    dsimp [Q₂, R]
    exact pow_nearCarrierLogExponent_le N hNpos
  have hboundary :
      (2 ^ S) / 2 = Q₁ := by
    dsimp [S, Q₁, M, L]
    exact (nearCarrier_low_high_boundary N
      (Real.log (N : ℝ))).symm
  have hendpoint :
      (2 ^ (S + H)) / 2 = Q₂ := by
    dsimp [S, H, Q₂, R, L]
    exact nearCarrier_high_endpoint N
      (Real.log (N : ℝ)) hroom
  have hbase :=
    fixedAwayFullCarrierBlock_eq_four_denominator_ranges
      t δ N ell n Q₁ Q₂ hQ₁ hQ₁Q₂ hQ₂N
  have hlow := congrFun
    (fixedAwayShiftedDyadicTotalSum_eq_denominatorRange
      t δ N M ell) n
  have hhigh := congrFun
    (fixedAwayShiftedExponentRangeSum_eq_denominatorRange
      t δ N S H ell hS) n
  rw [hlow, hhigh, hboundary, hendpoint]
  simpa only [L, M, S, H, R, Q₁, Q₂] using! hbase

theorem summable_fixedAwayFullCarrierBlock_norm_sq
    {t δ : ℝ} (N : ℕ) (ell : ℤ)
    (hδ : 0 < δ) (hδt : δ < t) :
    Summable fun n : ℤ ↦
      ‖fixedAwayFullCarrierBlock N t δ N ell n‖ ^ 2 := by
  unfold fixedAwayFullCarrierBlock
  apply summable_fixedAwayRamanujanProfileBlock_norm_sq
  intro p hp p' hp'
  exact summable_fixedAwayShiftedProfile_hermitianRamanujanMultiplier
    hδ hδt
      (by have := (Finset.mem_Icc.mp hp).1; omega)
      (by have := (Finset.mem_Icc.mp hp').1; omega)

/-- Exact four-range square estimate for one nonzero carrier.  No
cardinality factor is hidden: the factor `4` is the pointwise Hilbert-space
inequality for the four displayed, square-summable denominator pieces. -/
theorem tsum_fixedAwayFullCarrierBlock_norm_sq_le_explicit
    {t δ T0 : ℝ} (N : ℕ) (ell : ℤ) (hell : ell ≠ 0)
    (hδ : 0 < δ) (hδt : δ < t) (htT0 : t ≤ T0)
    (hN : 4 ≤ N) (hL : 1 ≤ Real.log (N : ℝ))
    (hroom : nearCarrierGapWidth (Real.log (N : ℝ)) + 1 ≤
      nearCarrierLogExponent N) :
    (∑' n : ℤ, ‖fixedAwayFullCarrierBlock N t δ N ell n‖ ^ 2) ≤
      4 * (
        fixedAwayPrefixCommonEnergyUniformBound T0 δ 12 +
        fixedAwayLowCommonEnergyUniformBound T0 δ
          (Real.exp ((Real.log (N : ℝ)) ^ (1 / 3 : ℝ)))
          (nearCarrierLowBlockCount N (Real.log (N : ℝ))) 12 +
        fixedAwayHighCommonEnergyUniformBound T0 δ
          (nearCarrierGapWidth (Real.log (N : ℝ))) 12 +
        fixedAwayShiftedDyadicEnergyUniformConstant T0 δ 12) := by
  let L : ℝ := Real.log (N : ℝ)
  let M : ℕ := nearCarrierLowBlockCount N L
  let S : ℕ := nearCarrierHighStart N L
  let H : ℕ := nearCarrierGapWidth L
  let R : ℕ := nearCarrierLogExponent N
  let Q₂ : ℕ := 2 ^ R
  let E : Finset ℕ := nearCarrierDyadicRangeExponents S H
  let c₀ : ℤ → ℂ := fixedAwayShiftedFinitePrefix t δ N ell
  let c₁ : ℤ → ℂ := fixedAwayShiftedDyadicTotalSum t δ N M ell
  let c₂ : ℤ → ℂ := fixedAwayShiftedExponentFinsetSum E t δ N ell
  let c₃ : ℤ → ℂ := fixedAwayShiftedPartialDyadicBlock
    (Finset.Ioc Q₂ N) t δ N ell
  have hNpos : 0 < N := by omega
  have hlogexp : Real.exp L = (N : ℝ) := by
    dsimp [L]
    rw [Real.exp_log]
    positivity
  have hcutDiv := nearCarrierLowBlock_cutoff N L hNpos hL hroom
  have hsepPos : 0 < Real.exp (L ^ (1 / 3 : ℝ)) := Real.exp_pos _
  have hcut :
      ∀ s ∈ nearCarrierDyadicExponents M,
        ((2 ^ s : ℕ) : ℝ) *
            Real.exp (L ^ (1 / 3 : ℝ)) ≤ (N : ℝ) := by
    intro s hs
    have hdiv := hcutDiv s hs
    have hNR : 0 < (N : ℝ) := by exact_mod_cast hNpos
    have ha :
        ((2 ^ s : ℕ) : ℝ) ≤
          (N : ℝ) / Real.exp (L ^ (1 / 3 : ℝ)) := by
      calc
        ((2 ^ s : ℕ) : ℝ) ≤
            Real.exp (-(L ^ (1 / 3 : ℝ))) * (N : ℝ) :=
          (div_le_iff₀ hNR).mp hdiv
        _ = (N : ℝ) / Real.exp (L ^ (1 / 3 : ℝ)) := by
          rw [Real.exp_neg]
          ring
    exact (le_div_iff₀ hsepPos).mp ha
  have hS2 : 2 ≤ S := by
    dsimp [S, nearCarrierHighStart]
    omega
  have hE2 : ∀ s ∈ E, 2 ≤ s := by
    intro s hs
    have hsLower := (Finset.mem_Ico.mp hs).1
    dsimp [E, nearCarrierDyadicRangeExponents] at hs
    exact hS2.trans hsLower
  have hQ₂pos : 0 < Q₂ := by positivity
  obtain ⟨hPdiv, _hPfour, hNP⟩ :=
    nearCarrier_terminal_partial_block_parameters N hN
  have hNQ₂ : N ≤ 2 * Q₂ := by
    dsimp [Q₂, R]
    rw [pow_succ] at hNP
    simpa only [mul_comm] using! hNP
  have hpartialSubset :
      Finset.Ioc Q₂ N ⊆ fixedAwayDyadicDenominators Q₂ :=
    Ioc_subset_fixedAwayDyadicDenominators hNQ₂
  have hs₀ : Summable fun n : ℤ ↦ ‖c₀ n‖ ^ 2 := by
    dsimp [c₀]
    exact summable_fixedAwayShiftedFinitePrefix_norm_sq hδ hδt
  have hs₁ : Summable fun n : ℤ ↦ ‖c₁ n‖ ^ 2 := by
    dsimp [c₁]
    exact summable_fixedAwayShiftedDyadicTotalSum_norm_sq
      hδ hδt hNpos hell
  have hs₂ : Summable fun n : ℤ ↦ ‖c₂ n‖ ^ 2 := by
    dsimp [c₂]
    exact summable_fixedAwayShiftedExponentFinsetSum_norm_sq
      hδ hδt hE2
  have hs₃ : Summable fun n : ℤ ↦ ‖c₃ n‖ ^ 2 := by
    dsimp [c₃]
    exact summable_fixedAwayShiftedPartialDyadicBlock_norm_sq
      hδ hδt hQ₂pos hpartialSubset
  have hb₀ :
      (∑' n : ℤ, ‖c₀ n‖ ^ 2) ≤
        fixedAwayPrefixCommonEnergyUniformBound T0 δ 12 := by
    dsimp [c₀, fixedAwayPrefixCommonEnergyUniformBound]
    exact tsum_fixedAwayShiftedFinitePrefix_norm_sq_le_uniform
      hδ hδt htT0 (by norm_num)
  have hb₁ :
      (∑' n : ℤ, ‖c₁ n‖ ^ 2) ≤
        fixedAwayLowCommonEnergyUniformBound T0 δ
          (Real.exp (L ^ (1 / 3 : ℝ))) M 12 := by
    dsimp [c₁, fixedAwayLowCommonEnergyUniformBound]
    exact tsum_fixedAwayShiftedDyadicTotalSum_norm_sq_le_of_cutoff_uniform
      hδ hδt htT0 hNpos hell
      hsepPos hcut (by norm_num)
  have hb₂ :
      (∑' n : ℤ, ‖c₂ n‖ ^ 2) ≤
        fixedAwayHighCommonEnergyUniformBound T0 δ H 12 := by
    have hcard : E.card = H := by
      dsimp [E, nearCarrierDyadicRangeExponents]
      simp
    dsimp [c₂, fixedAwayHighCommonEnergyUniformBound]
    rw [← hcard]
    exact tsum_fixedAwayShiftedExponentFinsetSum_norm_sq_le_uniform
      hδ hδt htT0 hE2 (by norm_num)
  have hb₃ :
      (∑' n : ℤ, ‖c₃ n‖ ^ 2) ≤
        fixedAwayShiftedDyadicEnergyUniformConstant T0 δ 12 := by
    dsimp [c₃]
    exact tsum_fixedAwayShiftedPartialDyadicBlock_norm_sq_le_uniform
      hδ hδt htT0 hQ₂pos hpartialSubset (by norm_num)
  have hright : Summable fun n : ℤ ↦
      4 * (‖c₀ n‖ ^ 2 + ‖c₁ n‖ ^ 2 +
        ‖c₂ n‖ ^ 2 + ‖c₃ n‖ ^ 2) :=
    (((hs₀.add hs₁).add hs₂).add hs₃).mul_left 4
  have hpoint : ∀ n : ℤ,
      ‖fixedAwayFullCarrierBlock N t δ N ell n‖ ^ 2 ≤
        4 * (‖c₀ n‖ ^ 2 + ‖c₁ n‖ ^ 2 +
          ‖c₂ n‖ ^ 2 + ‖c₃ n‖ ^ 2) := by
    intro n
    rw [fixedAwayFullCarrierBlock_eq_explicit_ranges
      t δ N ell n hN hroom]
    change ‖c₀ n + (c₁ n + (c₂ n + c₃ n))‖ ^ 2 ≤ _
    have hnorm :
        ‖c₀ n + (c₁ n + (c₂ n + c₃ n))‖ ≤
          ‖c₀ n‖ + ‖c₁ n‖ + ‖c₂ n‖ + ‖c₃ n‖ := by
      calc
        ‖c₀ n + (c₁ n + (c₂ n + c₃ n))‖ ≤
            ‖c₀ n‖ + ‖c₁ n + (c₂ n + c₃ n)‖ := norm_add_le _ _
        _ ≤ ‖c₀ n‖ + (‖c₁ n‖ + ‖c₂ n + c₃ n‖) := by
          gcongr
          exact norm_add_le _ _
        _ ≤ ‖c₀ n‖ + (‖c₁ n‖ + (‖c₂ n‖ + ‖c₃ n‖)) := by
          gcongr
          exact norm_add_le _ _
        _ = ‖c₀ n‖ + ‖c₁ n‖ + ‖c₂ n‖ + ‖c₃ n‖ := by ring
    refine (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans ?_
    nlinarith [sq_nonneg (‖c₀ n‖ - ‖c₁ n‖),
      sq_nonneg (‖c₀ n‖ - ‖c₂ n‖),
      sq_nonneg (‖c₀ n‖ - ‖c₃ n‖),
      sq_nonneg (‖c₁ n‖ - ‖c₂ n‖),
      sq_nonneg (‖c₁ n‖ - ‖c₃ n‖),
      sq_nonneg (‖c₂ n‖ - ‖c₃ n‖)]
  have hleft :
      Summable fun n : ℤ ↦
        ‖fixedAwayFullCarrierBlock N t δ N ell n‖ ^ 2 :=
    hright.of_nonneg_of_le (fun n ↦ sq_nonneg _) hpoint
  calc
    (∑' n : ℤ, ‖fixedAwayFullCarrierBlock N t δ N ell n‖ ^ 2) ≤
        ∑' n : ℤ,
          4 * (‖c₀ n‖ ^ 2 + ‖c₁ n‖ ^ 2 +
            ‖c₂ n‖ ^ 2 + ‖c₃ n‖ ^ 2) :=
      hleft.tsum_le_tsum hpoint hright
    _ = 4 * ((∑' n : ℤ, ‖c₀ n‖ ^ 2) +
        (∑' n : ℤ, ‖c₁ n‖ ^ 2) +
        (∑' n : ℤ, ‖c₂ n‖ ^ 2) +
        (∑' n : ℤ, ‖c₃ n‖ ^ 2)) := by
      rw [tsum_mul_left,
        ((hs₀.add hs₁).add hs₂).tsum_add hs₃,
        (hs₀.add hs₁).tsum_add hs₂,
        hs₀.tsum_add hs₁]
    _ ≤ 4 * (
        fixedAwayPrefixCommonEnergyUniformBound T0 δ 12 +
        fixedAwayLowCommonEnergyUniformBound T0 δ
          (Real.exp (L ^ (1 / 3 : ℝ))) M 12 +
        fixedAwayHighCommonEnergyUniformBound T0 δ H 12 +
        fixedAwayShiftedDyadicEnergyUniformConstant T0 δ 12) := by
      gcongr
    _ = 4 * (
        fixedAwayPrefixCommonEnergyUniformBound T0 δ 12 +
        fixedAwayLowCommonEnergyUniformBound T0 δ
          (Real.exp ((Real.log (N : ℝ)) ^ (1 / 3 : ℝ)))
          (nearCarrierLowBlockCount N (Real.log (N : ℝ))) 12 +
        fixedAwayHighCommonEnergyUniformBound T0 δ
          (nearCarrierGapWidth (Real.log (N : ℝ))) 12 +
        fixedAwayShiftedDyadicEnergyUniformConstant T0 δ 12) := by
      rfl

/-- The separated-carrier leakage has no residual logarithmic loss.  The
proof unfolds the rapid envelope and uses the explicit domination
`L² = (L^(1/3))^6 ≪ exp(12 L^(1/3))`. -/
theorem eventually_fixedAwayLowLeakageFactor_le_one :
    ∀ᶠ L : ℝ in atTop, ∀ (N : ℕ),
      1 ≤ N → Real.exp L = (N : ℝ) →
      (nearCarrierLowBlockCount N L : ℝ) ^ 2 *
        fixedAwayRapidEnvelope 12
          (Real.exp (L ^ (1 / 3 : ℝ)) / 4) ≤ 1 := by
  let D : ℝ := nearCarrierBinaryLogLinearConstant
  let C : ℝ := 4 ^ (12 : ℕ) * D ^ 2
  have hD : 0 ≤ D := by
    dsimp [D]
    exact nearCarrierBinaryLogLinearConstant_pos.le
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  have hxEventually : ∀ᶠ x : ℝ in atTop,
      C * x ^ 6 ≤ Real.exp (12 * x) :=
    eventually_const_mul_pow_le_exp C 6 12 hC (by norm_num)
  have hrpow : Tendsto (fun L : ℝ ↦ L ^ (1 / 3 : ℝ)) atTop atTop :=
    tendsto_rpow_atTop (by norm_num)
  have hpolyEventually := hrpow.eventually hxEventually
  filter_upwards [hpolyEventually, eventually_ge_atTop (1 : ℝ)] with
      L hpoly hL
  intro N hN hNL
  let x : ℝ := L ^ (1 / 3 : ℝ)
  let y : ℝ := Real.exp x / 4
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hx0 : 0 ≤ x := by
    dsimp [x]
    exact Real.rpow_nonneg hLpos.le _
  have hy : 0 < y := by
    dsimp [y]
    positivity
  have hM :
      (nearCarrierLowBlockCount N L : ℝ) ≤ D * L := by
    dsimp [D]
    exact nearCarrierLowBlockCount_cast_le_linear N L hN hL hNL
  have hM0 : 0 ≤ (nearCarrierLowBlockCount N L : ℝ) := by positivity
  have hDL0 : 0 ≤ D * L := mul_nonneg hD hLpos.le
  have hMsq :
      (nearCarrierLowBlockCount N L : ℝ) ^ 2 ≤ (D * L) ^ 2 :=
    pow_le_pow_left₀ hM0 hM 2
  have hxSix : x ^ 6 = L ^ 2 := by
    dsimp [x]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]
    norm_num
  have henv :
      fixedAwayRapidEnvelope 12 y ≤ y⁻¹ ^ 12 := by
    unfold fixedAwayRapidEnvelope
    rw [abs_of_pos hy]
    have hinv : (1 + y)⁻¹ ≤ y⁻¹ := by
      simpa only [one_div] using!
        (one_div_le_one_div_of_le hy (show y ≤ 1 + y by linarith))
    exact pow_le_pow_left₀ (by positivity) hinv 12
  have hyInv :
      y⁻¹ ^ 12 =
        4 ^ (12 : ℕ) / Real.exp (12 * x) := by
    dsimp [y]
    rw [inv_pow]
    rw [div_pow]
    rw [← Real.exp_nat_mul]
    norm_num only [Nat.cast_ofNat]
    field_simp
  have hpoly' :
      4 ^ (12 : ℕ) * D ^ 2 * L ^ 2 ≤
        Real.exp (12 * x) := by
    dsimp [C] at hpoly
    dsimp [x]
    rw [hxSix] at hpoly
    exact hpoly
  calc
    (nearCarrierLowBlockCount N L : ℝ) ^ 2 *
        fixedAwayRapidEnvelope 12
          (Real.exp (L ^ (1 / 3 : ℝ)) / 4) =
        (nearCarrierLowBlockCount N L : ℝ) ^ 2 *
          fixedAwayRapidEnvelope 12 y := by rfl
    _ ≤ (D * L) ^ 2 * (y⁻¹ ^ 12) := by
      exact mul_le_mul hMsq henv
        (fixedAwayRapidEnvelope_nonneg 12 y)
        (sq_nonneg (D * L))
    _ = (4 ^ (12 : ℕ) * D ^ 2 * L ^ 2) /
          Real.exp (12 * x) := by
      rw [hyInv]
      ring
    _ ≤ 1 := by
      exact (div_le_one (Real.exp_pos (12 * x))).2 hpoly'

def fixedAwayNonzeroCarrierLinearEnergyBound
    (T0 δ : ℝ) : ℝ :=
  4 * (
    fixedAwayPrefixCommonEnergyUniformBound T0 δ 12 +
    fixedAwayShiftedDyadicEnergyUniformConstant T0 δ 12 +
    2 * fixedAwayProjectedDyadicEnergyUniformConstant T0 δ 12 +
    (8 * nearCarrierBinaryLogLinearConstant + 9) *
      fixedAwayShiftedDyadicEnergyUniformConstant T0 δ 12)

theorem fixedAwayShiftedDiagonalUniformConstant_nonneg
    {T0 δ : ℝ} (hT0 : 0 ≤ T0) :
    0 ≤ fixedAwayShiftedDiagonalUniformConstant T0 δ := by
  have hquad := fixedAwayPVQuadraticDecayUniformConstant_nonneg hT0 δ
  have hmass := fixedAwayIntegerQuadraticEnvelopeMass_nonneg
  unfold fixedAwayShiftedDiagonalUniformConstant
  positivity

theorem fixedAwayShiftedDyadicEnergyUniformConstant_nonneg
    {T0 δ : ℝ} (hT0 : 0 ≤ T0) (J : ℕ) :
    0 ≤ fixedAwayShiftedDyadicEnergyUniformConstant T0 δ J := by
  have hdiag :=
    fixedAwayShiftedDiagonalUniformConstant_nonneg (δ := δ) hT0
  have hpvJ :=
    fixedAwayPVRapidDecayUniformConstant_nonneg hT0 δ J
  have hpvJ2 :=
    fixedAwayPVRapidDecayUniformConstant_nonneg hT0 δ (J + 2)
  have hderJ2 :=
    fixedAwayDerivativeRapidDecayUniformConstant_nonneg hT0 δ (J + 2)
  have hmass := fixedAwayRapidEnvelopeTwoMass_nonneg
  unfold fixedAwayShiftedDyadicEnergyUniformConstant
    fixedAwayHermitianRapidBVUniformConstant
    fixedAwayHermitianRapidVariationUniformConstant
  positivity

theorem fixedAwayProjectedDyadicEnergyUniformConstant_nonneg
    {T0 δ : ℝ} (hT0 : 0 ≤ T0) (J : ℕ) :
    0 ≤ fixedAwayProjectedDyadicEnergyUniformConstant T0 δ J := by
  have hpvJ :=
    fixedAwayPVRapidDecayUniformConstant_nonneg hT0 δ J
  have hpvJ2 :=
    fixedAwayPVRapidDecayUniformConstant_nonneg hT0 δ (J + 2)
  have hderJ2 :=
    fixedAwayDerivativeRapidDecayUniformConstant_nonneg hT0 δ (J + 2)
  have hmass := fixedAwayRapidEnvelopeTwoMass_nonneg
  have hquadMass := fixedAwayIntegerQuadraticEnvelopeMass_nonneg
  unfold fixedAwayProjectedDyadicEnergyUniformConstant
    fixedAwayProjectedRapidBVUniformConstant
    fixedAwayProjectedRapidVariationUniformConstant
  positivity

theorem fixedAwayNonzeroCarrierLinearEnergyBound_nonneg
    {T0 δ : ℝ} (hT0 : 0 ≤ T0) :
    0 ≤ fixedAwayNonzeroCarrierLinearEnergyBound T0 δ := by
  have hshift :=
    fixedAwayShiftedDyadicEnergyUniformConstant_nonneg
      (δ := δ) hT0 12
  have hproj :=
    fixedAwayProjectedDyadicEnergyUniformConstant_nonneg
      (δ := δ) hT0 12
  have hprefix : 0 ≤
      fixedAwayPrefixCommonEnergyUniformBound T0 δ 12 := by
    unfold fixedAwayPrefixCommonEnergyUniformBound
    exact mul_nonneg (by norm_num)
      (add_nonneg
        (fixedAwayShiftedDiagonalUniformConstant_nonneg
          (δ := δ) hT0)
        hshift)
  have hD := nearCarrierBinaryLogLinearConstant_pos.le
  unfold fixedAwayNonzeroCarrierLinearEnergyBound
  positivity

theorem tsum_fixedAwayFullCarrierBlock_norm_sq_le_linear
    {t δ T0 : ℝ} (N : ℕ) (ell : ℤ) (hell : ell ≠ 0)
    (hδ : 0 < δ) (hδt : δ < t) (htT0 : t ≤ T0)
    (hN : 4 ≤ N) (hL : 1 ≤ Real.log (N : ℝ))
    (hroom : nearCarrierGapWidth (Real.log (N : ℝ)) + 1 ≤
      nearCarrierLogExponent N)
    (hleak :
      (nearCarrierLowBlockCount N (Real.log (N : ℝ)) : ℝ) ^ 2 *
        fixedAwayRapidEnvelope 12
          (Real.exp ((Real.log (N : ℝ)) ^ (1 / 3 : ℝ)) / 4) ≤ 1) :
    (∑' n : ℤ, ‖fixedAwayFullCarrierBlock N t δ N ell n‖ ^ 2) ≤
      fixedAwayNonzeroCarrierLinearEnergyBound T0 δ *
        Real.log (N : ℝ) := by
  let L : ℝ := Real.log (N : ℝ)
  let M : ℕ := nearCarrierLowBlockCount N L
  let H : ℕ := nearCarrierGapWidth L
  let E : ℝ := fixedAwayShiftedDyadicEnergyUniformConstant T0 δ 12
  let P : ℝ := fixedAwayProjectedDyadicEnergyUniformConstant T0 δ 12
  let F : ℝ := fixedAwayPrefixCommonEnergyUniformBound T0 δ 12
  let D : ℝ := nearCarrierBinaryLogLinearConstant
  have hT0nonneg : 0 ≤ T0 := hδ.le.trans hδt.le |>.trans htT0
  have hE : 0 ≤ E := by
    dsimp [E]
    exact fixedAwayShiftedDyadicEnergyUniformConstant_nonneg
      (δ := δ) hT0nonneg 12
  have hP : 0 ≤ P := by
    dsimp [P]
    exact fixedAwayProjectedDyadicEnergyUniformConstant_nonneg
      (δ := δ) hT0nonneg 12
  have hF : 0 ≤ F := by
    dsimp [F, fixedAwayPrefixCommonEnergyUniformBound]
    exact mul_nonneg (by norm_num)
      (add_nonneg
        (fixedAwayShiftedDiagonalUniformConstant_nonneg
          (δ := δ) hT0nonneg) hE)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact nearCarrierBinaryLogLinearConstant_pos.le
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hNL : Real.exp L = (N : ℝ) := by
    dsimp [L]
    rw [Real.exp_log]
    positivity
  have hM :
      (M : ℝ) ≤ D * L := by
    dsimp [M, D]
    exact nearCarrierLowBlockCount_cast_le_linear N L
      (by omega) hL hNL
  have hM0 : 0 ≤ (M : ℝ) := by positivity
  have hHsq : (H : ℝ) ^ 2 ≤ 9 * L := by
    dsimp [H]
    exact nearCarrierGapWidth_cast_sq_le_nine_mul L hL
  have hleak' :
      (M : ℝ) ^ 2 *
        fixedAwayRapidEnvelope 12
          (Real.exp (L ^ (1 / 3 : ℝ)) / 4) ≤ 1 := by
    simpa only [M, L] using! hleak
  have hraw :=
    tsum_fixedAwayFullCarrierBlock_norm_sq_le_explicit
      N ell hell hδ hδt htT0 hN hL hroom
  have hinside :
      F +
        fixedAwayLowCommonEnergyUniformBound T0 δ
          (Real.exp (L ^ (1 / 3 : ℝ))) M 12 +
        fixedAwayHighCommonEnergyUniformBound T0 δ H 12 + E ≤
      (F + E + 2 * P + (8 * D + 9) * E) * L := by
    unfold fixedAwayLowCommonEnergyUniformBound
      fixedAwayHighCommonEnergyUniformBound
    change F + 2 * (4 * (M : ℝ) * E +
        (M : ℝ) ^ 2 * P *
          fixedAwayRapidEnvelope 12
            (Real.exp (L ^ (1 / 3 : ℝ)) / 4)) +
      (H : ℝ) ^ 2 * E + E ≤ _
    have hlinear :
        8 * (M : ℝ) * E ≤ 8 * D * E * L := by
      calc
        8 * (M : ℝ) * E ≤ 8 * (D * L) * E := by gcongr
        _ = 8 * D * E * L := by ring
    have hleakP :
        2 * ((M : ℝ) ^ 2 * P *
          fixedAwayRapidEnvelope 12
            (Real.exp (L ^ (1 / 3 : ℝ)) / 4)) ≤ 2 * P := by
      calc
        2 * ((M : ℝ) ^ 2 * P *
            fixedAwayRapidEnvelope 12
              (Real.exp (L ^ (1 / 3 : ℝ)) / 4)) =
            2 * P * ((M : ℝ) ^ 2 *
              fixedAwayRapidEnvelope 12
                (Real.exp (L ^ (1 / 3 : ℝ)) / 4)) := by ring
        _ ≤ 2 * P * 1 := by gcongr
        _ = 2 * P := by ring
    have hhigh :
        (H : ℝ) ^ 2 * E ≤ 9 * E * L := by
      calc
        (H : ℝ) ^ 2 * E ≤ (9 * L) * E := by gcongr
        _ = 9 * E * L := by ring
    have hconst :
        F + E + 2 * P ≤ (F + E + 2 * P) * L := by
      have hbase :
          0 ≤ F + E + 2 * P :=
        add_nonneg (add_nonneg hF hE) (mul_nonneg (by norm_num) hP)
      calc
        F + E + 2 * P = (F + E + 2 * P) * 1 := by ring
        _ ≤ (F + E + 2 * P) * L :=
          mul_le_mul_of_nonneg_left hL hbase
    calc
      F + 2 * (4 * (M : ℝ) * E +
          (M : ℝ) ^ 2 * P *
            fixedAwayRapidEnvelope 12
              (Real.exp (L ^ (1 / 3 : ℝ)) / 4)) +
          (H : ℝ) ^ 2 * E + E
          ≤ F + (8 * D * E * L + 2 * P) + 9 * E * L + E := by
        linarith
      _ ≤ (F + E + 2 * P) * L +
          (8 * D * E + 9 * E) * L := by
        linarith
      _ = (F + E + 2 * P + (8 * D + 9) * E) * L := by ring
  calc
    (∑' n : ℤ, ‖fixedAwayFullCarrierBlock N t δ N ell n‖ ^ 2) ≤
        4 * (F +
          fixedAwayLowCommonEnergyUniformBound T0 δ
            (Real.exp (L ^ (1 / 3 : ℝ))) M 12 +
          fixedAwayHighCommonEnergyUniformBound T0 δ H 12 + E) := by
      simpa only [L, M, H, E, F] using! hraw
    _ ≤ 4 * ((F + E + 2 * P + (8 * D + 9) * E) * L) := by
      gcongr
    _ = fixedAwayNonzeroCarrierLinearEnergyBound T0 δ *
        Real.log (N : ℝ) := by
      dsimp [F, E, P, D, L,
        fixedAwayNonzeroCarrierLinearEnergyBound]
      ring

theorem eventually_tsum_fixedAwayFullCarrierBlock_nonzero_le_linear
    {δ T0 : ℝ} (hδ : 0 < δ) :
    ∀ᶠ N : ℕ in atTop, ∀ (t : ℝ), δ < t → t ≤ T0 →
      ∀ (ell : ℤ), ell ≠ 0 →
      (∑' n : ℤ, ‖fixedAwayFullCarrierBlock N t δ N ell n‖ ^ 2) ≤
        fixedAwayNonzeroCarrierLinearEnergyBound T0 δ *
          Real.log (N : ℝ) := by
  have hlogTendsto :
      Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hleakN :=
    hlogTendsto.eventually
      eventually_fixedAwayLowLeakageFactor_le_one
  have hlogOne : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    hlogTendsto.eventually (eventually_ge_atTop 1)
  filter_upwards [
      eventually_ge_atTop 4,
      eventually_nearCarrierGapWidth_add_one_le_logExponent,
      hleakN,
      hlogOne] with N hN hroom hleak hL
  intro t hδt htT0 ell hell
  have hNpos : (0 : ℝ) < (N : ℝ) := by positivity
  have hNL : Real.exp (Real.log (N : ℝ)) = (N : ℝ) :=
    Real.exp_log hNpos
  exact tsum_fixedAwayFullCarrierBlock_norm_sq_le_linear
    N ell hell hδ hδt htT0 hN hL hroom
      (hleak N (by omega) hNL)

theorem fixedAwayFullCarrierBlock_zero_eq_singleton_add_rest
    (t δ : ℝ) (N : ℕ) (n : ℤ) (hN : 1 ≤ N) :
    fixedAwayFullCarrierBlock N t δ N 0 n =
      fixedAwayShiftedSingletonOne t δ N 0 n +
        fixedAwayZeroCarrierRestCoefficients t δ N n := by
  let g : ℕ → ℂ := fun p ↦
    fixedAwayRamanujanProfileTerm
      (fixedAwayShiftedProfile t δ N 0) p n
  have hset : Finset.Icc 1 N = {1} ∪ Finset.Icc 2 N := by
    ext p
    simp only [Finset.mem_Icc, Finset.mem_union,
      Finset.mem_singleton]
    omega
  have hdisjoint : Disjoint ({1} : Finset ℕ) (Finset.Icc 2 N) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [Finset.mem_singleton] at hp
    have hq' := Finset.mem_Icc.mp hq
    omega
  unfold fixedAwayFullCarrierBlock fixedAwayZeroCarrierRestCoefficients
    fixedAwayRamanujanProfileBlock fixedAwayShiftedSingletonOne
  change (∑ p ∈ Finset.Icc 1 N, g p) =
    g 1 + ∑ p ∈ Finset.Icc 2 N, g p
  rw [hset, Finset.sum_union hdisjoint]
  simp

def fixedAwayNonzeroFullCarrierCoefficients
    (t δ : ℝ) (N : ℕ) (ell : NonzeroFourierIndex) (n : ℤ) : ℂ :=
  fixedAwayFullCarrierBlock N t δ N (ell : ℤ) n

theorem summable_fixedAwayNonzeroFullCarrierCoefficients_norm_sq
    {t δ : ℝ} (N : ℕ) (hδ : 0 < δ) (hδt : δ < t)
    (ell : NonzeroFourierIndex) :
    Summable fun n : ℤ ↦
      ‖fixedAwayNonzeroFullCarrierCoefficients t δ N ell n‖ ^ 2 := by
  exact summable_fixedAwayFullCarrierBlock_norm_sq
    N (ell : ℤ) hδ hδt

def fixedAwayInfiniteNonzeroFullCarrierL2
    (t δ : ℝ) (N : ℕ) (hδ : 0 < δ) (hδt : δ < t) :
    UnitCircleL2 :=
  fixedAwayInfiniteCarrierL2
    (fixedAwayNonzeroFullCarrierCoefficients t δ N)
    (summable_fixedAwayNonzeroFullCarrierCoefficients_norm_sq
      N hδ hδt)

theorem norm_fixedAwayInfiniteNonzeroFullCarrierL2_le
    {t δ T0 : ℝ} (N : ℕ)
    (hδ : 0 < δ) (hδt : δ < t)
    (hC : ∀ (ell : NonzeroFourierIndex),
      (∑' n : ℤ,
        ‖fixedAwayNonzeroFullCarrierCoefficients
          t δ N ell n‖ ^ 2) ≤
        fixedAwayNonzeroCarrierLinearEnergyBound T0 δ *
          Real.log (N : ℝ))
    (hT0nonneg : 0 ≤ T0)
    (hlog : 0 ≤ Real.log (N : ℝ)) :
    ‖fixedAwayInfiniteNonzeroFullCarrierL2
        t δ N hδ hδt‖ ≤
      windowCarrierMassConstant *
        Real.sqrt
          (fixedAwayNonzeroCarrierLinearEnergyBound T0 δ *
            Real.log (N : ℝ)) := by
  unfold fixedAwayInfiniteNonzeroFullCarrierL2
  apply norm_fixedAwayInfiniteCarrierL2_le
    (C := fixedAwayNonzeroCarrierLinearEnergyBound T0 δ *
      Real.log (N : ℝ))
  · exact mul_nonneg
      (fixedAwayNonzeroCarrierLinearEnergyBound_nonneg
        hT0nonneg)
      hlog
  · exact hC

private def fixedAwayNonzeroEquivFinsetComplZero :
    NonzeroFourierIndex ≃ {ell : ℤ // ell ∉ ({0} : Finset ℤ)} where
  toFun ell := ⟨ell, by simpa using! ell.property⟩
  invFun ell := ⟨ell, by simpa using! ell.property⟩
  left_inv ell := by rfl
  right_inv ell := by rfl

theorem fixedAwayFullCarrierCoefficient_pos_eq_zero_add_nonzero
    {t δ : ℝ} (N n : ℕ)
    (hδ : 0 < δ) (hδt : δ < t) (ht : t ≤ 1 / 2)
    (hN : 0 < N) (hn : 0 < n) :
    fixedAwayFullCarrierCoefficient N t δ (n : ℤ) =
      bernoulliMarkFourierCoefficient 0 *
          fixedAwayFullCarrierBlock N t δ N 0 (n : ℤ) +
        ∑' ell : NonzeroFourierIndex,
          bernoulliMarkFourierCoefficient (ell : ℤ) *
            fixedAwayNonzeroFullCarrierCoefficients
              t δ N ell (n : ℤ) := by
  let g : ℤ → ℂ := fun ell ↦
    bernoulliMarkFourierCoefficient ell *
      fixedAwayFullCarrierBlock N t δ N ell (n : ℤ)
  let Np : ℕ+ := ⟨N, hN⟩
  have hs :
      Summable g := by
    dsimp [g]
    exact (hasSum_fixedAwayFullCarrierBlock_pos
      hδ hδt ht Np n hn).summable
  have hreindex :
      (∑' ell : NonzeroFourierIndex, g (ell : ℤ)) =
        ∑' ell : {ell : ℤ // ell ∉ ({0} : Finset ℤ)},
          g (ell : ℤ) := by
    simpa [Function.comp_def, fixedAwayNonzeroEquivFinsetComplZero] using!
      (fixedAwayNonzeroEquivFinsetComplZero.tsum_eq
        (fun ell : {ell : ℤ // ell ∉ ({0} : Finset ℤ)} ↦ g (ell : ℤ)))
  have hdecomp := hs.sum_add_tsum_subtype_compl ({0} : Finset ℤ)
  unfold fixedAwayFullCarrierCoefficient
  rw [← hreindex] at hdecomp
  simpa only [Finset.sum_singleton, g,
    fixedAwayNonzeroFullCarrierCoefficients] using! hdecomp.symm

theorem fourierCoeff_fixedAwayInfiniteNonzeroFullCarrierL2
    {t δ T0 : ℝ} (N : ℕ)
    (hδ : 0 < δ) (hδt : δ < t)
    (hbound : ∀ ell : NonzeroFourierIndex,
      (∑' n : ℤ,
        ‖fixedAwayNonzeroFullCarrierCoefficients
          t δ N ell n‖ ^ 2) ≤
        fixedAwayNonzeroCarrierLinearEnergyBound T0 δ *
          Real.log (N : ℝ))
    (hC : 0 ≤ fixedAwayNonzeroCarrierLinearEnergyBound T0 δ *
      Real.log (N : ℝ))
    (n : ℤ) :
    fourierCoeff
        (fixedAwayInfiniteNonzeroFullCarrierL2
          t δ N hδ hδt : AddCircle (1 : ℝ) → ℂ) n =
      ∑' ell : NonzeroFourierIndex,
        bernoulliMarkFourierCoefficient (ell : ℤ) *
          fixedAwayNonzeroFullCarrierCoefficients t δ N ell n := by
  unfold fixedAwayInfiniteNonzeroFullCarrierL2
  exact fourierCoeff_fixedAwayInfiniteCarrierL2
    (fixedAwayNonzeroFullCarrierCoefficients t δ N)
    (summable_fixedAwayNonzeroFullCarrierCoefficients_norm_sq
      N hδ hδt)
    hC hbound n

def fixedAwayZeroRestLinearEnergyBound
    (T0 δ B : ℝ) : ℝ :=
  (fixedAwayPVGlobalDecayUniformConstant T0 δ *
      fixedAwayInverseSquareMass) ^ 2 +
    8 * fixedAwayUnshiftedLowShellUniformConstant T0 δ ^ 2 +
    B + 2 * B / Real.log 2

theorem fixedAwayZeroRestLinearEnergyBound_nonneg
    {T0 δ B : ℝ} (hT0 : 0 ≤ T0) (hB : 0 ≤ B) :
    0 ≤ fixedAwayZeroRestLinearEnergyBound T0 δ B := by
  have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hglobal : 0 ≤ fixedAwayPVGlobalDecayUniformConstant T0 δ := by
    have hlocal := fixedAwayPVLocalUniformBound_nonneg hT0
    have hderiv2 := fixedAwayDerivativeUniformBound_nonneg hT0 δ 2
    unfold fixedAwayPVGlobalDecayUniformConstant
    positivity
  have hlow :
      0 ≤ fixedAwayUnshiftedLowShellUniformConstant T0 δ := by
    have hderiv0 := fixedAwayDerivativeUniformBound_nonneg hT0 δ 0
    have hderiv2 := fixedAwayDerivativeUniformBound_nonneg hT0 δ 2
    unfold fixedAwayUnshiftedLowShellUniformConstant
      fixedAwayPVInverseDecayUniformConstant
      fixedAwayDerivativeCauchyUniformConstant
    positivity
  unfold fixedAwayZeroRestLinearEnergyBound
  positivity

theorem tsum_fixedAwayZeroCarrierRest_nat_le_linear
    {t δ T0 B : ℝ} (N : ℕ)
    (hδ : 0 < δ) (hδt : δ < t) (htT0 : t ≤ T0)
    (hB : 0 ≤ B)
    (hraw :
      (∑' n : ℕ,
        ‖fixedAwayZeroCarrierRestCoefficients
          t δ N (n : ℤ)‖ ^ 2) ≤
        (fixedAwayPVGlobalDecayConstant t δ *
            fixedAwayInverseSquareMass) ^ 2 +
          (Nat.clog 2 (N ^ 2) : ℝ) * B +
          8 * fixedAwayUnshiftedLowShellUniformConstant T0 δ ^ 2)
    (hN : 1 ≤ N) (hL : 1 ≤ Real.log (N : ℝ)) :
    (∑' n : ℕ,
      ‖fixedAwayZeroCarrierRestCoefficients
        t δ N (n : ℤ)‖ ^ 2) ≤
      fixedAwayZeroRestLinearEnergyBound T0 δ B *
        Real.log (N : ℝ) := by
  let L : ℝ := Real.log (N : ℝ)
  let G : ℝ := fixedAwayPVGlobalDecayUniformConstant T0 δ *
    fixedAwayInverseSquareMass
  let U : ℝ := 8 * fixedAwayUnshiftedLowShellUniformConstant T0 δ ^ 2
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hT0nonneg : 0 ≤ T0 := hδ.le.trans hδt.le |>.trans htT0
  have hglobal :=
    fixedAwayPVGlobalDecayConstant_le_uniform hδ hδt.le htT0
  have hmass := fixedAwayInverseSquareMass_nonneg
  have hGbound :
      (fixedAwayPVGlobalDecayConstant t δ *
          fixedAwayInverseSquareMass) ^ 2 ≤ G ^ 2 := by
    apply pow_le_pow_left₀
      (mul_nonneg
        (fixedAwayPVGlobalDecayConstant_nonneg t δ) hmass)
    dsimp [G]
    exact mul_le_mul_of_nonneg_right hglobal hmass
  have hclog :=
    nat_clog_two_cast_le_log_div_add_one (N ^ 2) (by
      nlinarith [Nat.zero_le N])
  have hlogPow :
      Real.log ((N ^ 2 : ℕ) : ℝ) = 2 * L := by
    norm_num only [Nat.cast_pow]
    rw [Real.log_pow]
    norm_num
    rfl
  rw [hlogPow] at hclog
  have hclogB :
      (Nat.clog 2 (N ^ 2) : ℝ) * B ≤
        (2 * B / Real.log 2) * L + B := by
    have hlogTwo : 0 < Real.log 2 := Real.log_pos (by norm_num)
    calc
      (Nat.clog 2 (N ^ 2) : ℝ) * B ≤
          (2 * L / Real.log 2 + 1) * B := by gcongr
      _ = (2 * B / Real.log 2) * L + B := by ring
  have hU : 0 ≤ U := by
    dsimp [U]
    positivity
  have hconst :
      G ^ 2 + U + B ≤ (G ^ 2 + U + B) * L := by
    have hbase : 0 ≤ G ^ 2 + U + B := by positivity
    calc
      G ^ 2 + U + B = (G ^ 2 + U + B) * 1 := by ring
      _ ≤ (G ^ 2 + U + B) * L :=
        mul_le_mul_of_nonneg_left hL hbase
  calc
    (∑' n : ℕ,
        ‖fixedAwayZeroCarrierRestCoefficients
          t δ N (n : ℤ)‖ ^ 2) ≤
        (fixedAwayPVGlobalDecayConstant t δ *
            fixedAwayInverseSquareMass) ^ 2 +
          (Nat.clog 2 (N ^ 2) : ℝ) * B + U := by
      simpa only [U] using! hraw
    _ ≤ G ^ 2 + ((2 * B / Real.log 2) * L + B) + U := by
      linarith
    _ ≤ (G ^ 2 + U + B) * L +
        (2 * B / Real.log 2) * L := by
      linarith
    _ = fixedAwayZeroRestLinearEnergyBound T0 δ B *
        Real.log (N : ℝ) := by
      dsimp [G, U, L, fixedAwayZeroRestLinearEnergyBound]
      ring

/-- Parseval in norm form for an arbitrary circle `L²` function. -/
theorem tsum_sq_fourierCoeff_eq_norm_sq (F : UnitCircleL2) :
    (∑' n : ℤ,
      ‖fourierCoeff (F : AddCircle (1 : ℝ) → ℂ) n‖ ^ 2) =
      ‖F‖ ^ 2 := by
  have hparseval := tsum_sq_fourierCoeff F
  have hinner := congrArg RCLike.re
    (@L2.inner_def (AddCircle (1 : ℝ)) ℂ ℂ _ _ _ _ _ F F)
  rw [← integral_re] at hinner
  · simp only [← norm_sq_eq_re_inner] at hinner
    calc
      (∑' n : ℤ,
          ‖fourierCoeff (F : AddCircle (1 : ℝ) → ℂ) n‖ ^ 2) =
          ∫ x : AddCircle (1 : ℝ),
            ‖(F : AddCircle (1 : ℝ) → ℂ) x‖ ^ 2
              ∂AddCircle.haarAddCircle := hparseval
      _ = ‖F‖ ^ 2 := hinner.symm
  · exact L2.integrable_inner F F

theorem tsum_pnat_comp_le_tsum
    (g : ℕ → ℝ) (hg : Summable g)
    (hzero : ∀ n : ℕ, 0 ≤ g n) :
    (∑' n : ℕ+, g (n : ℕ)) ≤ ∑' n : ℕ, g n := by
  have hsub : Summable fun n : ℕ+ ↦ g (n : ℕ) :=
    hg.comp_injective Subtype.val_injective
  exact hsub.tsum_le_tsum_of_inj
    (fun n : ℕ+ ↦ (n : ℕ)) Subtype.val_injective
    (fun n _hn ↦ hzero n) (fun _n ↦ le_rfl) hg

theorem tsum_pnat_intCast_le_tsum
    (g : ℤ → ℝ) (hg : Summable g)
    (hzero : ∀ n : ℤ, 0 ≤ g n) :
    (∑' n : ℕ+, g (n : ℤ)) ≤ ∑' n : ℤ, g n := by
  have hinj : Function.Injective (fun n : ℕ+ ↦ (n : ℤ)) := by
    intro a b hab
    exact Subtype.ext (Int.ofNat_inj.mp hab)
  have hsub : Summable fun n : ℕ+ ↦ g (n : ℤ) :=
    hg.comp_injective hinj
  exact hsub.tsum_le_tsum_of_inj
    (fun n : ℕ+ ↦ (n : ℤ)) hinj
    (fun n _hn ↦ hzero n) (fun _n ↦ le_rfl) hg

theorem sq_add_three_le (a b c : ℝ) :
    (a + b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  nlinarith [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (b - c)]

def fixedAwayReconstructionLinearEnergyBound
    (T0 δ B : ℝ) : ℝ :=
  6 * (
    ‖bernoulliMarkFourierCoefficient 0‖ ^ 2 *
      (fixedAwayShiftedDiagonalUniformConstant T0 δ +
        fixedAwayZeroRestLinearEnergyBound T0 δ B) +
    windowCarrierMassConstant ^ 2 *
      fixedAwayNonzeroCarrierLinearEnergyBound T0 δ)

theorem fixedAwayReconstructionLinearEnergyBound_nonneg
    {T0 δ B : ℝ} (hT0 : 0 ≤ T0) (hB : 0 ≤ B) :
    0 ≤ fixedAwayReconstructionLinearEnergyBound T0 δ B := by
  have hdiag :=
    fixedAwayShiftedDiagonalUniformConstant_nonneg (δ := δ) hT0
  have hzero :=
    fixedAwayZeroRestLinearEnergyBound_nonneg
      (δ := δ) hT0 hB
  have hnonzero :=
    fixedAwayNonzeroCarrierLinearEnergyBound_nonneg (δ := δ) hT0
  have hmass := windowCarrierMassConstant_nonneg
  unfold fixedAwayReconstructionLinearEnergyBound
  positivity

/-- Uniform `O(log N)` Parseval bound for the complete fixed-away smooth
reconstruction.  Consequently its norm is `O(sqrt(log N))`, which is
strictly sublogarithmic. -/
theorem exists_eventually_norm_sq_fixedAwaySmoothReconstructionL2_le_linear
    (hCKsource : FixedAwayChanKumchevHypothesis)
    {δ T0 : ℝ} (hδ : 0 < δ) (hδT0 : δ < T0)
    (hT0half : T0 ≤ 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ N : ℕ in atTop, ∀ (hNpos : 0 < N) (t : ℝ),
        ∀ (hδt : δ < t) (_htT0 : t ≤ T0),
        ‖fixedAwaySmoothReconstructionL2
            (⟨N, hNpos⟩ : ℕ+) N t δ hδ hδt.le‖ ^ 2 ≤
          C * Real.log (N : ℝ) := by
  obtain ⟨B, hB, hzeroRaw⟩ :=
    exists_tsum_fixedAwayZeroCarrierRest_nat_le
      hCKsource hδ hδT0
  let C : ℝ := fixedAwayReconstructionLinearEnergyBound T0 δ B
  have hT0nonneg : 0 ≤ T0 := hδ.le.trans hδT0.le
  have hC : 0 ≤ C := by
    dsimp [C]
    exact fixedAwayReconstructionLinearEnergyBound_nonneg
      hT0nonneg hB
  refine ⟨C, hC, ?_⟩
  have hnonzeroEvent :=
    eventually_tsum_fixedAwayFullCarrierBlock_nonzero_le_linear
      (T0 := T0) hδ
  have hlogTendsto :
      Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogOne : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log (N : ℝ) :=
    hlogTendsto.eventually (eventually_ge_atTop 1)
  filter_upwards [eventually_ge_atTop 4, hlogOne, hnonzeroEvent] with
      N hN hL hnonzero
  intro hNpos t hδt htT0
  let Np : ℕ+ := ⟨N, hNpos⟩
  let L : ℝ := Real.log (N : ℝ)
  let Z : ℝ := fixedAwayZeroRestLinearEnergyBound T0 δ B
  let D : ℝ := fixedAwayNonzeroCarrierLinearEnergyBound T0 δ
  let b : ℂ := bernoulliMarkFourierCoefficient 0
  let Y : UnitCircleL2 :=
    fixedAwayInfiniteNonzeroFullCarrierL2 t δ N hδ hδt
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hZ : 0 ≤ Z := by
    dsimp [Z]
    exact fixedAwayZeroRestLinearEnergyBound_nonneg
      hT0nonneg hB
  have hD : 0 ≤ D := by
    dsimp [D]
    exact fixedAwayNonzeroCarrierLinearEnergyBound_nonneg hT0nonneg
  have hbound : ∀ ell : NonzeroFourierIndex,
      (∑' n : ℤ,
        ‖fixedAwayNonzeroFullCarrierCoefficients
          t δ N ell n‖ ^ 2) ≤ D * L := by
    intro ell
    simpa only [D, L,
      fixedAwayNonzeroFullCarrierCoefficients] using!
      hnonzero t hδt htT0 (ell : ℤ) ell.property
  have hYnorm :=
    norm_fixedAwayInfiniteNonzeroFullCarrierL2_le
      (T0 := T0) N hδ hδt hbound hT0nonneg hLpos.le
  have hYsq :
      ‖Y‖ ^ 2 ≤ windowCarrierMassConstant ^ 2 * D * L := by
    have hsq := pow_le_pow_left₀ (norm_nonneg Y)
      (by simpa only [Y, D, L] using! hYnorm) 2
    calc
      ‖Y‖ ^ 2 ≤
          (windowCarrierMassConstant * Real.sqrt (D * L)) ^ 2 := hsq
      _ = windowCarrierMassConstant ^ 2 * D * L := by
        rw [mul_pow, Real.sq_sqrt (mul_nonneg hD hLpos.le)]
        ring
  have hrestRaw := hzeroRaw t N hδt htT0 (by omega)
  have hrest :
      (∑' n : ℕ,
        ‖fixedAwayZeroCarrierRestCoefficients
          t δ N (n : ℤ)‖ ^ 2) ≤ Z * L := by
    simpa only [Z, L] using!
      tsum_fixedAwayZeroCarrierRest_nat_le_linear
        N hδ hδt htT0 hB hrestRaw (by omega) hL
  have hsingleInt :
      (∑' n : ℤ,
        ‖fixedAwayShiftedSingletonOne t δ N 0 n‖ ^ 2) ≤
        fixedAwayShiftedDiagonalUniformConstant T0 δ := by
    exact (tsum_fixedAwayShiftedSingletonOne_norm_sq_le
      (N := N) (ell := 0) hδ hδt).trans
        (fixedAwayShiftedDiagonalConstant_le_uniform
          hδ hδt.le htT0)
  have hsingleSummable :=
    summable_fixedAwayShiftedSingletonOne_norm_sq
      (N := N) (ell := 0) hδ hδt
  have hsingleP :
      (∑' n : ℕ+,
        ‖fixedAwayShiftedSingletonOne t δ N 0 (n : ℤ)‖ ^ 2) ≤
        fixedAwayShiftedDiagonalUniformConstant T0 δ :=
    (tsum_pnat_intCast_le_tsum
      (fun n : ℤ ↦ ‖fixedAwayShiftedSingletonOne t δ N 0 n‖ ^ 2)
      hsingleSummable (fun _n ↦ sq_nonneg _)).trans hsingleInt
  have hrestNatSummable :
      Summable fun n : ℕ ↦
        ‖fixedAwayZeroCarrierRestCoefficients
          t δ N (n : ℤ)‖ ^ 2 :=
    (summable_fixedAwayZeroCarrierRestCoefficients_norm_sq
      N hδ hδt).comp_injective Int.ofNat_injective
  have hrestP :
      (∑' n : ℕ+,
        ‖fixedAwayZeroCarrierRestCoefficients
          t δ N (n : ℤ)‖ ^ 2) ≤ Z * L :=
    (tsum_pnat_comp_le_tsum
      (fun n : ℕ ↦ ‖fixedAwayZeroCarrierRestCoefficients
        t δ N (n : ℤ)‖ ^ 2)
      hrestNatSummable (fun _n ↦ sq_nonneg _)).trans hrest
  have hYFourierSummable :
      Summable fun n : ℤ ↦
        ‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) n‖ ^ 2 :=
    (hasSum_sq_fourierCoeff Y).summable
  have hYP :
      (∑' n : ℕ+,
        ‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2) ≤
        windowCarrierMassConstant ^ 2 * D * L := by
    calc
      (∑' n : ℕ+,
          ‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2) ≤
          ∑' n : ℤ,
            ‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) n‖ ^ 2 :=
        tsum_pnat_intCast_le_tsum
          (fun n : ℤ ↦
            ‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) n‖ ^ 2)
          hYFourierSummable (fun _n ↦ sq_nonneg _)
      _ = ‖Y‖ ^ 2 := tsum_sq_fourierCoeff_eq_norm_sq Y
      _ ≤ windowCarrierMassConstant ^ 2 * D * L := hYsq
  have hCnonneg : 0 ≤ D * L := mul_nonneg hD hLpos.le
  have hfullPoint : ∀ n : ℕ+,
      ‖fixedAwayFullCarrierCoefficient N t δ (n : ℤ)‖ ^ 2 ≤
        3 * (
          ‖b‖ ^ 2 *
              ‖fixedAwayShiftedSingletonOne t δ N 0 (n : ℤ)‖ ^ 2 +
          ‖b‖ ^ 2 *
              ‖fixedAwayZeroCarrierRestCoefficients
                t δ N (n : ℤ)‖ ^ 2 +
          ‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2) := by
    intro n
    rw [fixedAwayFullCarrierCoefficient_pos_eq_zero_add_nonzero
      N (n : ℕ) hδ hδt (htT0.trans hT0half)
      (by omega) n.pos]
    rw [← fourierCoeff_fixedAwayInfiniteNonzeroFullCarrierL2
      N hδ hδt hbound hCnonneg (n : ℤ)]
    rw [fixedAwayFullCarrierBlock_zero_eq_singleton_add_rest
      t δ N (n : ℤ) (by omega)]
    change ‖b * (_ + _) + _‖ ^ 2 ≤ _
    rw [mul_add]
    have hnorm :
        ‖b * fixedAwayShiftedSingletonOne t δ N 0 (n : ℤ) +
          b * fixedAwayZeroCarrierRestCoefficients
            t δ N (n : ℤ) +
          fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ≤
        ‖b * fixedAwayShiftedSingletonOne t δ N 0 (n : ℤ)‖ +
          ‖b * fixedAwayZeroCarrierRestCoefficients
            t δ N (n : ℤ)‖ +
          ‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ := by
      exact (norm_add_le _ _).trans
        (add_le_add (norm_add_le _ _) le_rfl)
    refine (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans ?_
    have hthree := sq_add_three_le
      (‖b * fixedAwayShiftedSingletonOne t δ N 0 (n : ℤ)‖)
      (‖b * fixedAwayZeroCarrierRestCoefficients
        t δ N (n : ℤ)‖)
      (‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖)
    simpa only [norm_mul, mul_pow] using! hthree
  have hpnatIntInj : Function.Injective (fun n : ℕ+ ↦ (n : ℤ)) := by
    intro a b hab
    exact Subtype.ext (Int.ofNat_inj.mp hab)
  have hsP :
      Summable fun n : ℕ+ ↦
        ‖fixedAwayShiftedSingletonOne t δ N 0 (n : ℤ)‖ ^ 2 :=
    hsingleSummable.comp_injective hpnatIntInj
  have hrP :
      Summable fun n : ℕ+ ↦
        ‖fixedAwayZeroCarrierRestCoefficients
          t δ N (n : ℤ)‖ ^ 2 :=
    hrestNatSummable.comp_injective Subtype.val_injective
  have hyP :
      Summable fun n : ℕ+ ↦
        ‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2 :=
    hYFourierSummable.comp_injective hpnatIntInj
  let f₀ : ℕ+ → ℝ := fun n ↦
    ‖b‖ ^ 2 *
      ‖fixedAwayShiftedSingletonOne t δ N 0 (n : ℤ)‖ ^ 2
  let f₁ : ℕ+ → ℝ := fun n ↦
    ‖b‖ ^ 2 *
      ‖fixedAwayZeroCarrierRestCoefficients
        t δ N (n : ℤ)‖ ^ 2
  let f₂ : ℕ+ → ℝ := fun n ↦
    ‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2
  have hf₀ : Summable f₀ := by
    dsimp [f₀]
    exact hsP.mul_left (‖b‖ ^ 2)
  have hf₁ : Summable f₁ := by
    dsimp [f₁]
    exact hrP.mul_left (‖b‖ ^ 2)
  have hf₂ : Summable f₂ := by
    simpa only [f₂] using! hyP
  have hright :
      Summable fun n : ℕ+ ↦ 3 * (f₀ n + f₁ n + f₂ n) :=
    ((hf₀.add hf₁).add hf₂).mul_left 3
  have hfullSummable :
      Summable fun n : ℕ+ ↦
        ‖fixedAwayFullCarrierCoefficient N t δ (n : ℤ)‖ ^ 2 := by
    apply hright.of_nonneg_of_le (fun _n ↦ sq_nonneg _)
    intro n
    simpa only [f₀, f₁, f₂] using! hfullPoint n
  have hsum :
      (∑' n : ℕ+,
        ‖fixedAwayFullCarrierCoefficient N t δ (n : ℤ)‖ ^ 2) ≤
        3 * (
          ‖b‖ ^ 2 * fixedAwayShiftedDiagonalUniformConstant T0 δ +
          ‖b‖ ^ 2 * (Z * L) +
          windowCarrierMassConstant ^ 2 * D * L) := by
    calc
      (∑' n : ℕ+,
          ‖fixedAwayFullCarrierCoefficient N t δ (n : ℤ)‖ ^ 2) ≤
          ∑' n : ℕ+, 3 * (f₀ n + f₁ n + f₂ n) := by
        apply hfullSummable.tsum_le_tsum _ hright
        intro n
        simpa only [f₀, f₁, f₂] using! hfullPoint n
      _ = 3 * (
          ‖b‖ ^ 2 *
              (∑' n : ℕ+,
                ‖fixedAwayShiftedSingletonOne t δ N 0 (n : ℤ)‖ ^ 2) +
          ‖b‖ ^ 2 *
              (∑' n : ℕ+,
                ‖fixedAwayZeroCarrierRestCoefficients
                  t δ N (n : ℤ)‖ ^ 2) +
          (∑' n : ℕ+,
            ‖fourierCoeff (Y : AddCircle (1 : ℝ) → ℂ) (n : ℤ)‖ ^ 2)) := by
        rw [tsum_mul_left, (hf₀.add hf₁).tsum_add hf₂,
          hf₀.tsum_add hf₁]
        dsimp [f₀, f₁, f₂]
        rw [tsum_mul_left, tsum_mul_left]
      _ ≤ 3 * (
          ‖b‖ ^ 2 * fixedAwayShiftedDiagonalUniformConstant T0 δ +
          ‖b‖ ^ 2 * (Z * L) +
          windowCarrierMassConstant ^ 2 * D * L) := by
        gcongr
  have hdiag0 :
      0 ≤ fixedAwayShiftedDiagonalUniformConstant T0 δ :=
    fixedAwayShiftedDiagonalUniformConstant_nonneg hT0nonneg
  have hdiagAbsorb :
      fixedAwayShiftedDiagonalUniformConstant T0 δ ≤
        fixedAwayShiftedDiagonalUniformConstant T0 δ * L := by
    calc
      fixedAwayShiftedDiagonalUniformConstant T0 δ =
          fixedAwayShiftedDiagonalUniformConstant T0 δ * 1 := by ring
      _ ≤ fixedAwayShiftedDiagonalUniformConstant T0 δ * L :=
        mul_le_mul_of_nonneg_left hL hdiag0
  change
    ‖fixedAwaySmoothReconstructionL2
      Np (Np : ℕ) t δ hδ hδt.le‖ ^ 2 ≤ C * Real.log (N : ℝ)
  rw [norm_fixedAwaySmoothReconstructionL2_sq_eq_positiveCarriers
    hδ hδt (htT0.trans hT0half) Np]
  calc
    2 * (∑' n : ℕ+,
        ‖fixedAwayFullCarrierCoefficient N t δ (n : ℤ)‖ ^ 2) ≤
      2 * (3 * (
        ‖b‖ ^ 2 * fixedAwayShiftedDiagonalUniformConstant T0 δ +
        ‖b‖ ^ 2 * (Z * L) +
        windowCarrierMassConstant ^ 2 * D * L)) := by gcongr
    _ ≤ 6 * (
        ‖b‖ ^ 2 *
          (fixedAwayShiftedDiagonalUniformConstant T0 δ + Z) +
        windowCarrierMassConstant ^ 2 * D) * L := by
      have hbdiag :
          ‖b‖ ^ 2 * fixedAwayShiftedDiagonalUniformConstant T0 δ ≤
            ‖b‖ ^ 2 *
              (fixedAwayShiftedDiagonalUniformConstant T0 δ * L) :=
        mul_le_mul_of_nonneg_left hdiagAbsorb (sq_nonneg ‖b‖)
      nlinarith
    _ = C * Real.log (N : ℝ) := by
      dsimp [C, b, Z, D, L,
        fixedAwayReconstructionLinearEnergyBound]

theorem uniform_norm_sq_fixedAwaySmoothShotL2_small
    (hCKsource : FixedAwayChanKumchevHypothesis)
    {δ T0 : ℝ} (hδ : 0 < δ) (hδT0 : δ < T0)
    (hT0half : T0 ≤ 1 / 2)
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop, ∀ (_hNpos : 0 < N) (t : ℝ),
      ∀ (hδt : δ < t) (_htT0 : t ≤ T0),
      ‖fixedAwaySmoothShotL2 t δ N N hδ hδt.le‖ ^ 2 ≤
        eta * Real.log (N : ℝ) ^ 2 := by
  obtain ⟨C, hC, hreconEvent⟩ :=
    exists_eventually_norm_sq_fixedAwaySmoothReconstructionL2_le_linear
      hCKsource hδ hδT0 hT0half
  obtain ⟨N₀, herror⟩ :=
    uniform_norm_naturalCutoffShotErrorL2_sq_small
      (show 0 < eta / 4 by positivity)
  have hlogTendsto :
      Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogLarge : ∀ᶠ N : ℕ in atTop,
      4 * C / eta ≤ Real.log (N : ℝ) :=
    hlogTendsto.eventually (eventually_ge_atTop (4 * C / eta))
  have hlogPos : ∀ᶠ N : ℕ in atTop, 0 < Real.log (N : ℝ) :=
    hlogTendsto.eventually (eventually_gt_atTop 0)
  filter_upwards [
      hreconEvent, eventually_ge_atTop N₀, hlogLarge, hlogPos] with
      N hrecon hN₀ hlogLargeN hlogN
  intro hNpos t hδt htT0
  let Np : ℕ+ := ⟨N, hNpos⟩
  let R : UnitCircleL2 :=
    fixedAwaySmoothReconstructionL2 Np N t δ hδ hδt.le
  let E : UnitCircleL2 := naturalCutoffShotErrorL2 Np
  have hreconSq : ‖R‖ ^ 2 ≤ C * Real.log (N : ℝ) := by
    simpa only [R, Np] using! hrecon hNpos t hδt htT0
  have hreconSmall :
      ‖R‖ ^ 2 ≤ (eta / 4) * Real.log (N : ℝ) ^ 2 := by
    calc
      ‖R‖ ^ 2 ≤ C * Real.log (N : ℝ) := hreconSq
      _ ≤ (eta / 4) * Real.log (N : ℝ) ^ 2 := by
        have heta0 : 0 ≤ eta := heta.le
        have hscale :
            C ≤ (eta / 4) * Real.log (N : ℝ) := by
          have hmul :
              4 * C ≤ Real.log (N : ℝ) * eta :=
            (div_le_iff₀ heta).mp hlogLargeN
          nlinarith
        nlinarith
  have herrorSq :
      ‖E‖ ^ 2 ≤ (eta / 4) * Real.log (N : ℝ) ^ 2 := by
    simpa only [E, Np] using! herror Np hN₀
  have hwindow := fixedAwaySmooth_windowError_identity
    Np N hδ hδt.le
  have herrId :
      primitiveShotSumL2 (Np : ℕ) N -
          naturalCutoffReconstructionL2 Np N = -E := by
    change primitiveShotSumL2 (Np : ℕ) (Np : ℕ) -
      naturalCutoffReconstructionL2 Np (Np : ℕ) = -E
    dsimp [E, naturalCutoffShotErrorL2, reconstructedShotL2]
    abel
  rw [herrId] at hwindow
  have hshot :
      fixedAwaySmoothShotL2 t δ N N hδ hδt.le = R - E := by
    change fixedAwaySmoothShotL2 t δ (Np : ℕ) N hδ hδt.le = R - E
    calc
      fixedAwaySmoothShotL2 t δ (Np : ℕ) N hδ hδt.le =
          (fixedAwaySmoothShotL2 t δ (Np : ℕ) N hδ hδt.le - R) + R := by
        abel
      _ = -E + R := by rw [hwindow]
      _ = R - E := by abel
  rw [hshot]
  have hnorm := norm_sub_le R E
  have hsq :
      ‖R - E‖ ^ 2 ≤ 2 * (‖R‖ ^ 2 + ‖E‖ ^ 2) := by
    refine (pow_le_pow_left₀ (norm_nonneg _) hnorm 2).trans ?_
    nlinarith [sq_nonneg (‖R‖ - ‖E‖)]
  calc
    ‖R - E‖ ^ 2 ≤ 2 * (‖R‖ ^ 2 + ‖E‖ ^ 2) := hsq
    _ ≤ 2 * ((eta / 4) * Real.log (N : ℝ) ^ 2 +
        (eta / 4) * Real.log (N : ℝ) ^ 2) := by gcongr
    _ = eta * Real.log (N : ℝ) ^ 2 := by ring

theorem unitCircleL2Pullback_fixedAwaySmoothShotL2_ae
    {t δ : ℝ} (N P : ℕ) (hδ : 0 < δ) (hδt : δ ≤ t) :
    unitCircleL2Pullback
        (fixedAwaySmoothShotL2 t δ N P hδ hδt) =ᵐ[uniform01Measure]
      fixedAwaySmoothShotSum t δ N P := by
  have hcoe :=
    measurePreserving_unitCircleMk_uniform01.quasiMeasurePreserving.ae
      (fixedAwaySmoothShotL2_coe_ae hδ hδt N P)
  have hIoo : ∀ᵐ alpha : ℝ ∂uniform01Measure,
      alpha ∈ Ioo (0 : ℝ) 1 := by
    rw [uniform01Measure]
    exact ae_restrict_mem measurableSet_Ioo
  filter_upwards [hcoe, hIoo] with alpha hrepresentative halpha
  change
    (fixedAwaySmoothShotL2 t δ N P hδ hδt :
        AddCircle (1 : ℝ) → ℂ) (alpha : AddCircle (1 : ℝ)) = _
  rw [hrepresentative]
  unfold fixedAwaySmoothShotCircle
  exact AddCircle.liftIoc_coe_apply
    (by simpa using! (show alpha ∈ Ioc (0 : ℝ) 1 from
      ⟨halpha.1, halpha.2.le⟩))

theorem eLpNorm_fixedAwaySmoothShotSum_eq_enorm
    {t δ : ℝ} (N P : ℕ) (hδ : 0 < δ) (hδt : δ ≤ t) :
    eLpNorm (fixedAwaySmoothShotSum t δ N P) 2 uniform01Measure =
      ‖fixedAwaySmoothShotL2 t δ N P hδ hδt‖ₑ := by
  rw [← eLpNorm_unitCircleL2Pullback]
  exact eLpNorm_congr_ae
    (unitCircleL2Pullback_fixedAwaySmoothShotL2_ae
      N P hδ hδt).symm

theorem eLpNorm_fixedAwaySmoothShotSum_div_eq_ofReal
    {t δ : ℝ} (N P : ℕ) (L : ℝ)
    (hδ : 0 < δ) (hδt : δ ≤ t) (hL : 0 < L) :
    eLpNorm
        (fun alpha ↦ fixedAwaySmoothShotSum t δ N P alpha / L)
        2 uniform01Measure =
      ENNReal.ofReal
        (‖fixedAwaySmoothShotL2 t δ N P hδ hδt‖ / L) := by
  have hfun :
      (fun alpha ↦ fixedAwaySmoothShotSum t δ N P alpha / L) =
        ((L : ℂ)⁻¹ • fixedAwaySmoothShotSum t δ N P) := by
    funext alpha
    simp only [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv]
    ring
  rw [hfun, eLpNorm_const_smul,
    eLpNorm_fixedAwaySmoothShotSum_eq_enorm N P hδ hδt]
  rw [← ofReal_norm_eq_enorm, ← ofReal_norm_eq_enorm]
  rw [← ENNReal.ofReal_mul (norm_nonneg ((L : ℂ)⁻¹))]
  congr 1
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
  field_simp [hL.ne']

theorem uniform_eLpNorm_fixedAwaySmoothShotSum_div_small
    (hCKsource : FixedAwayChanKumchevHypothesis)
    {δ T0 : ℝ} (hδ : 0 < δ) (hδT0 : δ < T0)
    (hT0half : T0 ≤ 1 / 2) :
    ∀ eta > 0, ∀ᶠ N : ℕ in atTop, ∀ (_hNpos : 0 < N) (t : ℝ),
      ∀ (_hδt : δ < t) (_htT0 : t ≤ T0),
      eLpNorm
          (fun alpha ↦
            fixedAwaySmoothShotSum t δ N N alpha /
              Real.log (N : ℝ))
          2 uniform01Measure ≤ ENNReal.ofReal eta := by
  intro eta heta
  have hsquare :=
    uniform_norm_sq_fixedAwaySmoothShotL2_small
      hCKsource hδ hδT0 hT0half (eta := eta ^ 2)
        (sq_pos_of_pos heta)
  have hlogTendsto :
      Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlogPos : ∀ᶠ N : ℕ in atTop, 0 < Real.log (N : ℝ) :=
    hlogTendsto.eventually (eventually_gt_atTop 0)
  filter_upwards [hsquare, hlogPos] with N hsquareN hlogN
  intro hNpos t hδt htT0
  rw [eLpNorm_fixedAwaySmoothShotSum_div_eq_ofReal
    N N (Real.log (N : ℝ)) hδ hδt.le hlogN]
  apply ENNReal.ofReal_le_ofReal
  have hsquare' :
      ‖fixedAwaySmoothShotL2 t δ N N hδ hδt.le‖ ^ 2 ≤
        (eta * Real.log (N : ℝ)) ^ 2 := by
    simpa only [mul_pow] using!
      hsquareN hNpos t hδt htT0
  have hnorm :
      ‖fixedAwaySmoothShotL2 t δ N N hδ hδt.le‖ ≤
        eta * Real.log (N : ℝ) := by
    exact (sq_le_sq₀ (norm_nonneg _)
      (mul_nonneg heta.le hlogN.le)).mp hsquare'
  exact (div_le_iff₀ hlogN).2 hnorm

theorem measurable_fixedAwayMinorEndpointDiscrepancy
    (N : ℕ) (ε : ℝ) :
    Measurable (fixedAwayMinorEndpointDiscrepancy N ε) := by
  unfold fixedAwayMinorEndpointDiscrepancy
  exact Finset.measurable_fun_sum (Finset.Icc 1 2) fun p _hp ↦
    (measurable_minorFixedAwaySharpTerm N p (ε / 4)).sub
      (measurable_fixedAwaySmoothShotTerm ε (ε / 2) N p)

theorem eLpNorm_fixedAwayMinorEndpointDiscrepancy_div_log_le
    (N : ℕ) (ε L : ℝ) (hε : 0 < ε) (hL : 0 < L) :
    eLpNorm
        (fun alpha ↦
          fixedAwayMinorEndpointDiscrepancy N ε alpha / L)
        2 uniform01Measure ≤
      ENNReal.ofReal ((2 / ε) / L) := by
  have hpoint : ∀ᵐ alpha : ℝ ∂uniform01Measure,
      ‖fixedAwayMinorEndpointDiscrepancy N ε alpha / L‖ ≤
        (2 / ε) / L := by
    filter_upwards with alpha
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hL]
    exact div_le_div_of_nonneg_right
      (norm_fixedAwayMinorEndpointDiscrepancy_le N ε alpha hε) hL.le
  simpa using! eLpNorm_le_of_ae_bound (p := (2 : ENNReal)) hpoint

theorem eventually_eLpNorm_fixedAwayMinorEndpointDiscrepancy_div_log_small
    (ε : ℝ) (hε : 0 < ε) :
    ∀ eta > 0, ∀ᶠ N : ℕ in atTop,
      eLpNorm
          (fun alpha ↦
            fixedAwayMinorEndpointDiscrepancy N ε alpha /
              Real.log (N : ℝ))
          2 uniform01Measure ≤ ENNReal.ofReal eta := by
  intro eta heta
  have hlog :
      Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio :
      Tendsto (fun N : ℕ ↦ (2 / ε) / Real.log (N : ℝ))
        atTop (nhds 0) :=
    hlog.const_div_atTop (2 / ε)
  have hsmall : ∀ᶠ N : ℕ in atTop,
      (2 / ε) / Real.log (N : ℝ) < eta :=
    hratio.eventually_lt_const heta
  filter_upwards [eventually_ge_atTop 2, hsmall] with N hN hsmallN
  have hlogN : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast hN)
  exact (eLpNorm_fixedAwayMinorEndpointDiscrepancy_div_log_le
    N ε (Real.log (N : ℝ)) hε hlogN).trans
      (ENNReal.ofReal_le_ofReal hsmallN.le)

theorem normalizedFixedAwayMinorRemainder_eq_smooth_add_endpoints
    (N : ℕ) (A ε alpha : ℝ)
    (hN : 2 ≤ N)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ))
    (hε : 0 < ε)
    (hroom : A / Real.log (N : ℝ) ≤ ε / 4) :
    normalizedFixedAwayMinorRemainder N A ε alpha =
      fixedAwaySmoothShotSum ε (ε / 2) N N alpha /
          Real.log (N : ℝ) +
        fixedAwayMinorEndpointDiscrepancy N ε alpha /
          Real.log (N : ℝ) := by
  unfold normalizedFixedAwayMinorRemainder
  rw [minorFixedAwaySharp_sub_upper_eq_smooth_add_endpoints
    N A ε alpha hN hA hL hε hroom]
  ring

theorem iterated_eventually_aestronglyMeasurable_fixedAwayMinorRemainder
    (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      AEStronglyMeasurable
        (normalizedFixedAwayMinorRemainder N (A : ℝ) ε)
        uniform01Measure := by
  filter_upwards [eventually_ge_atTop 1] with A hA
  have hadmissible :=
    eventually_minorComponentSplit_admissible (A : ℝ) ε hε
  filter_upwards [hadmissible] with N hadmissibleN
  rcases hadmissibleN with ⟨hN, hL, hquarter⟩
  have hApos : 0 < (A : ℝ) := by
    exact_mod_cast (show 0 < A by omega)
  have hroom : (A : ℝ) / Real.log (N : ℝ) ≤ ε / 4 :=
    (div_le_iff₀ hL).2 (by simpa only [mul_comm] using! hquarter.le)
  have hfun :
      normalizedFixedAwayMinorRemainder N (A : ℝ) ε =
        (fun alpha ↦
          fixedAwaySmoothShotSum ε (ε / 2) N N alpha /
              Real.log (N : ℝ) +
            fixedAwayMinorEndpointDiscrepancy N ε alpha /
              Real.log (N : ℝ)) := by
    funext alpha
    exact
      normalizedFixedAwayMinorRemainder_eq_smooth_add_endpoints
        N (A : ℝ) ε alpha hN hApos hL hε hroom
  rw [hfun]
  exact
    (((measurable_fixedAwaySmoothShotSum ε (ε / 2) N N).div_const _).add
      ((measurable_fixedAwayMinorEndpointDiscrepancy N ε).div_const _))
      |>.aestronglyMeasurable

theorem iterated_eLpNorm_normalizedFixedAwayMinorRemainder_small
    (hCKsource : FixedAwayChanKumchevHypothesis)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ eta > 0, ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
      eLpNorm
          (normalizedFixedAwayMinorRemainder N (A : ℝ) ε)
          2 uniform01Measure ≤ ENNReal.ofReal eta := by
  intro eta heta
  have hsmooth :=
    uniform_eLpNorm_fixedAwaySmoothShotSum_div_small
      hCKsource (δ := ε / 2) (T0 := ε)
        (by positivity) (by linarith) hεhalf.le
        (eta / 2) (by positivity)
  have hendpoint :=
    eventually_eLpNorm_fixedAwayMinorEndpointDiscrepancy_div_log_small
      ε hε (eta / 2) (by positivity)
  filter_upwards [eventually_ge_atTop 1] with A hA
  have hadmissible :=
    eventually_minorComponentSplit_admissible (A : ℝ) ε hε
  filter_upwards [hsmooth, hendpoint, hadmissible] with
      N hsmoothN hendpointN hadmissibleN
  rcases hadmissibleN with ⟨hN, hL, hquarter⟩
  have hApos : 0 < (A : ℝ) := by
    exact_mod_cast (show 0 < A by omega)
  have hroom : (A : ℝ) / Real.log (N : ℝ) ≤ ε / 4 :=
    (div_le_iff₀ hL).2 (by simpa only [mul_comm] using! hquarter.le)
  have hNpos : 0 < N := by omega
  have hhalf : ε / 2 < ε := by linarith
  have hsmoothN' :
      eLpNorm
          (fun alpha ↦
            fixedAwaySmoothShotSum ε (ε / 2) N N alpha /
              Real.log (N : ℝ))
          2 uniform01Measure ≤ ENNReal.ofReal (eta / 2) :=
    hsmoothN hNpos ε hhalf le_rfl
  have hfun :
      normalizedFixedAwayMinorRemainder N (A : ℝ) ε =
        (fun alpha ↦
          fixedAwaySmoothShotSum ε (ε / 2) N N alpha /
              Real.log (N : ℝ) +
            fixedAwayMinorEndpointDiscrepancy N ε alpha /
              Real.log (N : ℝ)) := by
    funext alpha
    exact
      normalizedFixedAwayMinorRemainder_eq_smooth_add_endpoints
        N (A : ℝ) ε alpha hN hApos hL hε hroom
  rw [hfun]
  have hf : AEStronglyMeasurable
      (fun alpha ↦
        fixedAwaySmoothShotSum ε (ε / 2) N N alpha /
          Real.log (N : ℝ))
      uniform01Measure :=
    ((measurable_fixedAwaySmoothShotSum ε (ε / 2) N N).div_const
      (Real.log (N : ℝ) : ℂ)).aestronglyMeasurable
  have hg : AEStronglyMeasurable
      (fun alpha ↦
        fixedAwayMinorEndpointDiscrepancy N ε alpha /
          Real.log (N : ℝ))
      uniform01Measure :=
    ((measurable_fixedAwayMinorEndpointDiscrepancy N ε).div_const
      (Real.log (N : ℝ) : ℂ)).aestronglyMeasurable
  have hadd :
      eLpNorm
          (fun alpha ↦
            fixedAwaySmoothShotSum ε (ε / 2) N N alpha /
                Real.log (N : ℝ) +
              fixedAwayMinorEndpointDiscrepancy N ε alpha /
                Real.log (N : ℝ))
          2 uniform01Measure ≤
        eLpNorm
            (fun alpha ↦
              fixedAwaySmoothShotSum ε (ε / 2) N N alpha /
                Real.log (N : ℝ))
            2 uniform01Measure +
          eLpNorm
            (fun alpha ↦
              fixedAwayMinorEndpointDiscrepancy N ε alpha /
                Real.log (N : ℝ))
            2 uniform01Measure := by
    simpa only [Pi.add_apply] using!
      eLpNorm_add_le hf hg (by norm_num : (1 : ENNReal) ≤ 2)
  calc
    eLpNorm
        (fun alpha ↦
          fixedAwaySmoothShotSum ε (ε / 2) N N alpha /
              Real.log (N : ℝ) +
            fixedAwayMinorEndpointDiscrepancy N ε alpha /
              Real.log (N : ℝ))
        2 uniform01Measure ≤
      eLpNorm
          (fun alpha ↦
            fixedAwaySmoothShotSum ε (ε / 2) N N alpha /
              Real.log (N : ℝ))
          2 uniform01Measure +
        eLpNorm
          (fun alpha ↦
            fixedAwayMinorEndpointDiscrepancy N ε alpha /
              Real.log (N : ℝ))
          2 uniform01Measure := hadd
    _ ≤ ENNReal.ofReal (eta / 2) + ENNReal.ofReal (eta / 2) :=
      add_le_add hsmoothN' hendpointN
    _ = ENNReal.ofReal eta := by
      rw [← ENNReal.ofReal_add
        (by positivity : 0 ≤ eta / 2)
        (by positivity : 0 ≤ eta / 2)]
      congr 1
      ring

theorem iterated_probabilityDeletion_normalizedFixedAwayMinorRemainder
    (hCKsource : FixedAwayChanKumchevHypothesis)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤
            ‖normalizedFixedAwayMinorRemainder
              N (A : ℝ) ε alpha‖} < δ := by
  apply iterated_probabilityDeletion_of_iterated_eLpNorm_two
    (μ := uniform01Measure)
    (fun A N ↦ normalizedFixedAwayMinorRemainder N (A : ℝ) ε)
  · exact
      iterated_eventually_aestronglyMeasurable_fixedAwayMinorRemainder
        ε hε
  · exact
      iterated_eLpNorm_normalizedFixedAwayMinorRemainder_small
        hCKsource ε hε hεhalf

/-- Source-facing full-moment form of the fixed-away deletion theorem.
The hypothesis is the literal second moment
`∑_{1 ≤ n ≤ 2K} |∑_{q ≤ X} c_q(n)|² ≪ K X²`, encoded by
`ChanKumchevInitialSecondMomentEstimate`, uniformly up to the manuscript's
terminal cutoff.  The conversion to the long-range interface is proved
above, rather than postulated. -/
theorem
    iterated_probabilityDeletion_normalizedFixedAwayMinorRemainder_of_initialSecondMoment
    {D : ℝ} (hD : 0 ≤ D)
    (hSecond : ∀ᶠ K : ℕ in atTop,
      ChanKumchevInitialSecondMomentEstimate
        D K (fixedAwayCkTerminal K))
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤
            ‖normalizedFixedAwayMinorRemainder
              N (A : ℝ) ε alpha‖} < δ := by
  exact
    iterated_probabilityDeletion_normalizedFixedAwayMinorRemainder
      (fixedAwayChanKumchevHypothesis_of_initialSecondMoment hD hSecond)
      ε hε hεhalf

/-- Completely scalar source-facing form.  It is enough to establish the
displayed finite Ramanujan second moment; every subsequent Fourier,
`L²`, endpoint, and probability step is then theorem-checked. -/
theorem
    iterated_probabilityDeletion_normalizedFixedAwayMinorRemainder_of_coefficientSecondMoment
    {D : ℝ} (hD : 0 ≤ D)
    (hCoeff : ∀ᶠ K : ℕ in atTop,
      ∀ X ∈ Finset.Icc 1 (fixedAwayCkTerminal K),
        (∑ n ∈ Finset.Icc 1 (2 * K),
          initialRawRamanujanBlockCoefficient X n ^ 2) ≤
            D * (K : ℝ) * (X : ℝ) ^ 2)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤
            ‖normalizedFixedAwayMinorRemainder
              N (A : ℝ) ε alpha‖} < δ := by
  exact
    iterated_probabilityDeletion_normalizedFixedAwayMinorRemainder
      (fixedAwayChanKumchevHypothesis_of_coefficientSecondMoment
        hD hCoeff)
      ε hε hεhalf

/-- Once the lower transition has been deleted, the single explicit
Chan--Kumchev prefix hypothesis closes the entire minor-resonance branch. -/
theorem minorProbabilityDeletion_of_lower_and_fixedAway_ck
    (hCKsource : FixedAwayChanKumchevHypothesis)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hlower : ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖normalizedNearMinorLowerTransitionSum
            N (A : ℝ) ε alpha‖} < δ) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖normalizedMinorResonanceShotSum
            N (A : ℝ) alpha‖} < δ := by
  exact minorProbabilityDeletion_of_lower_and_fixedAway
    ε hε hεhalf hlower
      (iterated_probabilityDeletion_normalizedFixedAwayMinorRemainder
        hCKsource ε hε hεhalf)

/-- Paper-facing version: actual-grid factorial limits supply the lower
transition, and the explicit Chan--Kumchev prefix hypothesis supplies the
fixed-away transition. -/
theorem minorProbabilityDeletion_of_actualGridFactorialLimits_and_ck
    (hCKsource : FixedAwayChanKumchevHypothesis)
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (hFac : LowerTransitionActualGridFactorialLimits) :
    ∀ r > 0, ∀ δ > 0,
      ∀ᶠ A : ℕ in atTop, ∀ᶠ N : ℕ in atTop,
        uniform01Measure.real
          {alpha | r ≤ ‖normalizedMinorResonanceShotSum
            N (A : ℝ) alpha‖} < δ := by
  exact
    minorProbabilityDeletion_of_actualGridFactorialLimits_and_fixedAway
      ε hε hεhalf hFac
        (iterated_probabilityDeletion_normalizedFixedAwayMinorRemainder
          hCKsource ε hε hεhalf)

theorem nearMinorUpperTransitionSum_eq_finiteStrictTransitionSum
    (N : ℕ) (A ε alpha : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ))
    (hε : 0 < ε)
    (hroom : A / Real.log (N : ℝ) ≤ ε / 4) :
    nearMinorUpperTransitionSum N A ε alpha =
      finiteStrictTransitionSum
        (Finset.Ioc 2 N)
        (fun p ↦ |(p : ℝ) * resonanceDelta p alpha|)
        (fun p ↦ (primitiveShot N p alpha : ℂ))
        (gevreyOuterCutoff ε) (ε / 4) ε := by
  unfold nearMinorUpperTransitionSum finiteStrictTransitionSum
  apply Finset.sum_congr rfl
  intro p _hp
  let x : ℝ := (p : ℝ) * resonanceDelta p alpha
  by_cases hlower : ε / 4 < |x|
  · by_cases hupper : |x| < ε
    · have ha : 0 < A / (2 * Real.log (N : ℝ)) := by positivity
      have hinner :
          2 * (A / (2 * Real.log (N : ℝ))) ≤ |x| := by
        have hscale :
            2 * (A / (2 * Real.log (N : ℝ))) =
              A / Real.log (N : ℝ) := by
          field_simp [hL.ne']
        rw [hscale]
        exact hroom.trans hlower.le
      have hrho :
          nearRho (A / (2 * Real.log (N : ℝ))) ε x =
            (gevreyOuterCutoff ε x : ℂ) :=
        nearRho_eq_outer_of_inner_support ha hε hinner
      have houterAbs :
          gevreyOuterCutoff ε x = gevreyOuterCutoff ε |x| := by
        rcases le_total 0 x with hx | hx
        · rw [abs_of_nonneg hx]
        · rw [abs_of_nonpos hx, gevreyOuterCutoff_even]
      unfold nearMinorUpperTransitionTerm
      rw [if_pos (by simpa only [x] using! hlower),
        if_pos ⟨hlower, hupper⟩,
        smoothNearLiteralShotTerm_eq_rho_mul_primitiveShot,
        show nearRho (A / (2 * Real.log (N : ℝ))) ε
            ((p : ℝ) * resonanceDelta p alpha) =
              (gevreyOuterCutoff ε
                ((p : ℝ) * resonanceDelta p alpha) : ℂ) by
          simpa only [x] using! hrho]
      rw [show gevreyOuterCutoff ε
          ((p : ℝ) * resonanceDelta p alpha) =
            gevreyOuterCutoff ε
              |(p : ℝ) * resonanceDelta p alpha| by
        simpa only [x] using! houterAbs]
      simp only [Complex.real_smul]
    · have houter : ε ≤ |x| := le_of_not_gt hupper
      rw [if_neg (fun hs ↦ hupper hs.2)]
      exact nearMinorUpperTransitionTerm_eq_zero_of_epsilon_le_abs
        N p A ε alpha hA hL hε
          (by
            have hscale :
                A / (2 * Real.log (N : ℝ)) =
                  (A / Real.log (N : ℝ)) / 2 := by
              field_simp [hL.ne']
            rw [hscale]
            linarith [div_nonneg hA.le hL.le])
          (by simpa only [x] using! houter)
  · unfold nearMinorUpperTransitionTerm
    rw [if_neg (by simpa only [x] using! hlower),
      if_neg (fun hs ↦ hlower hs.1)]

theorem nearMinorUpperTransitionSum_layerCake
    (N : ℕ) (A ε alpha : ℝ)
    (hA : 0 < A) (hL : 0 < Real.log (N : ℝ))
    (hε : 0 < ε)
    (hroom : A / Real.log (N : ℝ) ≤ ε / 4)
    (hnoLower : ∀ p ∈ Finset.Ioc 2 N,
      |(p : ℝ) * resonanceDelta p alpha| ≠ ε / 4) :
    gevreyOuterCutoff ε (ε / 4) •
          finiteSharpTail
            (Finset.Ioc 2 N)
            (fun p ↦ |(p : ℝ) * resonanceDelta p alpha|)
            (fun p ↦ (primitiveShot N p alpha : ℂ))
            (ε / 4) +
        ∫ t in ε / 4..ε,
          deriv (gevreyOuterCutoff ε) t •
            finiteSharpTail
              (Finset.Ioc 2 N)
              (fun p ↦ |(p : ℝ) * resonanceDelta p alpha|)
              (fun p ↦ (primitiveShot N p alpha : ℂ))
              t =
      nearMinorUpperTransitionSum N A ε alpha := by
  rw [finite_stieltjes_layerCake_strict
    (Finset.Ioc 2 N)
    (fun p ↦ |(p : ℝ) * resonanceDelta p alpha|)
    (fun p ↦ (primitiveShot N p alpha : ℂ))
    (h := gevreyOuterCutoff ε)
    (h' := deriv (gevreyOuterCutoff ε))
    (by linarith : ε / 4 ≤ ε)
    (gevreyOuterCutoff_eq_zero_of_le_abs hε
      (by rw [abs_of_pos hε]))
    (fun t _ht ↦
      ((gevreyOuterCutoff_contDiff (m := 1) ε).differentiable
        (by norm_num) t).hasDerivAt)
    ((gevreyOuterCutoff_contDiff (m := 1) ε).continuous_deriv
      le_rfl |>.intervalIntegrable (ε / 4) ε)
    hnoLower]
  exact
    (nearMinorUpperTransitionSum_eq_finiteStrictTransitionSum
      N A ε alpha hA hL hε hroom).symm

end

end Erdos1002
