/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.AppendixPair
import ErdosProblems.Erdos1165.GaussianA12TailCertificate
import ErdosProblems.Erdos1165.AppendixA11A12Numerical
import ErdosProblems.Erdos1165.Proposition13Scales
import ErdosProblems.Erdos1165.RadialHarnackSpecialization
import ErdosProblems.Erdos1165.BoundaryStoppedHarnack
import ErdosProblems.Erdos1165.MarkedTerminalDisintegration
import ErdosProblems.Erdos1165.PoissonKernelMarkedAlgebra
import ErdosProblems.Erdos1165.ProfileWeightUpper
import ErdosProblems.Erdos1165.GaussianGeometricCutoff
import ErdosProblems.Erdos1165.GaussianGeometricNumerical

/-!
# Concrete finite two-point profile and separation bounds

This file supplies the deterministic part of HLOZ Proposition A.3(2).  The
prefix probability occurring in the two-point conditional ratio is bounded
below by the explicit fixed-cutoff geometric A.12 schedule, after the shifted
A.11 Taylor certificate has been instantiated at `delta = 1/5`.  The
resulting prefix quantity is then inserted into the exact separation-level
sum from `AppendixPair`.

No summed pair estimate is assumed.  The only walk-facing input to
`pairMoment_of_annularPrefixComparison` is pointwise: a pair with separation
level `l` is bounded by the explicit prefix-denominator envelope at that
level.  This is the form in which the sharp annular Harnack/strong-Markov
comparison is consumed.
-/

open MeasureTheory Set Filter
open scoped BigOperators ENNReal NNReal ProbabilityTheory

namespace Erdos1165.AppendixPairMoment

noncomputable section

open AppendixFirstMoment AppendixA11A12OnePoint AppendixPair
  GaussianA12Schedule GaussianA12TailCertificate GaussianBlockFactorization
  GaussianMultiBlockProfile AppendixA11A12Numerical
  Proposition13Assembly Proposition13Scales RadialHarnackSpecialization
  GaussianGeometricSchedule GaussianGeometricCutoff GaussianGeometricNumerical
  MarkedTerminalDisintegration AppendixLocalTime PoissonKernelMarkedAlgebra

/-- The complete lattice-Gaussian A.11/A.12 upper bound, specialized to the
certificate's `delta = 1/5`, fits the reserved one-point upper envelope as
soon as its explicit coefficient is absorbed by one quarter of
`scaleCost`. -/
theorem constrainedProfileWeight_le_pointUpperBound
    {delta : ℝ} {n : ℕ}
    (hq : ProfileWeightUpper.profileUpperTailStart ≤ scaleIndex delta n)
    (hcost : ProfileWeightUpper.profileUpperConstant *
        (scaleIndex delta n : ℝ) ^ (3 / 5 : ℝ) ≤ scaleCost delta n / 4) :
    constrainedProfileWeight (scaleIndex delta n) chosenProfileDelta ≤
      pointUpperBound delta n := by
  have hupper := ProfileWeightUpper.constrainedProfileWeight_le_exp hq
  have hexp :
      -(2 * (scaleIndex delta n : ℝ)) +
          ProfileWeightUpper.profileUpperConstant *
            (scaleIndex delta n : ℝ) ^ (3 / 5 : ℝ) ≤
        -2 * (scaleIndex delta n : ℝ) + scaleCost delta n / 4 := by
    linarith
  have h := hupper.trans (Real.exp_le_exp.mpr hexp)
  simpa [ProfileWeightUpper.profileUpperDelta, chosenProfileDelta,
    pointUpperBound] using h

lemma profileUpperConstant_nonneg :
    0 ≤ ProfileWeightUpper.profileUpperConstant := by
  unfold ProfileWeightUpper.profileUpperConstant
    ProfileWeightUpper.profileUpperCoreConstant
  have ha11 : 0 ≤
      ProfileA11Assembly.a11ErrorCoefficient
        ProfileWeightUpper.profileUpperDelta 2 1 11 :=
    ProfileA11Assembly.a11ErrorCoefficient_nonneg
      (by norm_num [ProfileWeightUpper.profileUpperDelta])
      (by norm_num) (by norm_num) (by norm_num)
  have hlog : 0 ≤ Real.log
      ((constrainedProfiles ProfileWeightUpper.profileUpperTailStart
        ProfileWeightUpper.profileUpperDelta).card + 1) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega :
      (constrainedProfiles ProfileWeightUpper.profileUpperTailStart
        ProfileWeightUpper.profileUpperDelta).card + 1 ≠ 0)
  positivity

/-- The positive slack in `costExponent` eventually absorbs the complete
profile-upper coefficient with the exact factor `1/4` reserved by the scale
certificate. -/
theorem eventually_profileUpperCost_le_quarter_scaleCost
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      ProfileWeightUpper.profileUpperConstant *
          (scaleIndex delta n : ℝ) ^ (3 / 5 : ℝ) ≤
        scaleCost delta n / 4 := by
  have hexp : (3 / 5 : ℝ) < costExponent delta := by
    unfold costExponent
    linarith [scaleSlack_pos hdelta]
  have habsorbReal := eventually_const_mul_rpow_le_half_rpow
    (C := 2 * ProfileWeightUpper.profileUpperConstant) hexp
    (mul_nonneg (by norm_num) profileUpperConstant_nonneg)
  have habsorb := (tendsto_scaleIndex_atTop delta).eventually habsorbReal
  filter_upwards [habsorb] with n hn
  unfold scaleCost
  nlinarith

/-- A sharper share of the same asymptotic budget, reserved for the far-pair
calculation where the one-point upper occurs twice. -/
theorem eventually_profileUpperCost_le_sixtyFourth_scaleCost
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      ProfileWeightUpper.profileUpperConstant *
          (scaleIndex delta n : ℝ) ^ (3 / 5 : ℝ) ≤
        scaleCost delta n / 64 := by
  have hexp : (3 / 5 : ℝ) < costExponent delta := by
    unfold costExponent
    linarith [scaleSlack_pos hdelta]
  have habsorbReal := eventually_const_mul_rpow_le_half_rpow
    (C := 32 * ProfileWeightUpper.profileUpperConstant) hexp
    (mul_nonneg (by norm_num) profileUpperConstant_nonneg)
  have habsorb := (tendsto_scaleIndex_atTop delta).eventually habsorbReal
  filter_upwards [habsorb] with n hn
  unfold scaleCost
  nlinarith

/-- The complete fixed-prefix A.11/A.12 denominator cost also fits in one
sixty-fourth of the ambient scale budget. -/
theorem eventually_geometricPrefixCost_le_sixtyFourth_scaleCost
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      geometricProfileCostCoefficient geometricCutoff *
          (scaleIndex delta n : ℝ) ^ (3 / 5 : ℝ) ≤
        scaleCost delta n / 64 := by
  have hexp : (3 / 5 : ℝ) < costExponent delta := by
    unfold costExponent
    linarith [scaleSlack_pos hdelta]
  have hcoeff0 : 0 ≤ geometricProfileCostCoefficient geometricCutoff :=
    geometricProfileCostCoefficient_nonneg _
  have habsorbReal := eventually_const_mul_rpow_le_half_rpow
    (C := 32 * geometricProfileCostCoefficient geometricCutoff) hexp
    (mul_nonneg (by norm_num) hcoeff0)
  have habsorb := (tendsto_scaleIndex_atTop delta).eventually habsorbReal
  filter_upwards [habsorb] with n hn
  unfold scaleCost
  nlinarith

/-- Eventually the complete constrained-profile upper bound is exactly the
`pointUpperBound` used in the corrected near-pair contribution. -/
theorem eventually_constrainedProfileWeight_le_pointUpperBound
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      constrainedProfileWeight (scaleIndex delta n) chosenProfileDelta ≤
        pointUpperBound delta n := by
  have hstart := (tendsto_scaleIndex_atTop delta).eventually
    (eventually_ge_atTop
      (ProfileWeightUpper.profileUpperTailStart : ℝ))
  filter_upwards [hstart,
      eventually_profileUpperCost_le_quarter_scaleCost hdelta]
      with n hn hcost
  apply constrainedProfileWeight_le_pointUpperBound
  · exact_mod_cast hn
  · exact hcost

/-- The completely explicit shifted-A.11/A.12 lower mass used for a prefix
ending at scale `q`.  Its first block begins at the fixed
`geometricCutoff`, independent of `q`, and the dyadic schedule reaches `q`.
This fixed-prefix choice is essential: starting at a positive fraction of
`q` would force one exact path for linearly many scales and lose the required
sublinear error. -/
def prefixProfileLower (q : ℕ) : ℝ :=
  multiblockProfileLower q chosenProfileDelta 2 1 10
    (geometricSchedule geometricCutoff (geometricDepth geometricCutoff q) q)

/-- Exact analytic cost in the explicit prefix denominator. -/
def prefixProfileCost (q : ℕ) : ℝ :=
  multiblockProfileCost q geometricCutoff chosenProfileDelta 2 1 10
    (geometricSchedule geometricCutoff (geometricDepth geometricCutoff q) q)

/-- The prefix mass has no hidden asymptotic notation: it is exactly the
leading `exp(-2q)` times the shifted A.11 and finite A.12 cost. -/
lemma prefixProfileLower_eq_exp {q : ℕ} (hq : geometricCutoff ≤ q) :
    prefixProfileLower q =
      Real.exp (-(2 * (q : ℝ)) - prefixProfileCost q) := by
  unfold prefixProfileLower prefixProfileCost
  cases hdepth : geometricDepth geometricCutoff q with
  | zero =>
      change multiblockProfileLower q chosenProfileDelta 2 1 10
          ([terminalGeometricBlock geometricCutoff q]) = _
      apply multiblockProfileLower_eq_exp_neg_two_sub_cost hq
  | succ j =>
      change multiblockProfileLower q chosenProfileDelta 2 1 10
          (completeGeometricBlock geometricCutoff ::
            geometricSchedule (2 * geometricCutoff) j q) = _
      apply multiblockProfileLower_eq_exp_neg_two_sub_cost hq

/-- An explicit additive A.11/A.12 budget gives the denominator estimate
used in the far-pair correlation bound. -/
lemma exp_neg_two_sub_le_prefixProfileLower
    {q : ℕ} {C : ℝ} (hq : geometricCutoff ≤ q)
    (hcost : prefixProfileCost q ≤ C) :
    Real.exp (-(2 * (q : ℝ)) - C) ≤ prefixProfileLower q := by
  rw [prefixProfileLower_eq_exp hq]
  exact Real.exp_le_exp.mpr (by linarith)

/-- Reciprocal form of the checked prefix bound. -/
lemma div_prefixProfileLower_le_mul_exp
    {q : ℕ} {C A : ℝ} (hq : geometricCutoff ≤ q)
    (hA : 0 ≤ A) (hcost : prefixProfileCost q ≤ C) :
    A / prefixProfileLower q ≤ A * Real.exp (2 * (q : ℝ) + C) := by
  rw [prefixProfileLower_eq_exp hq]
  rw [div_eq_mul_inv, ← Real.exp_neg]
  apply mul_le_mul_of_nonneg_left _ hA
  exact Real.exp_le_exp.mpr (by linarith)

lemma prefixProfileLower_pos (q : ℕ) : 0 < prefixProfileLower q := by
  unfold prefixProfileLower
  cases geometricDepth geometricCutoff q <;>
    exact multiblockProfileLower_pos

lemma prefixProfileLower_nonneg (q : ℕ) : 0 ≤ prefixProfileLower q :=
  (prefixProfileLower_pos q).le

/-- **Concrete shifted A.11 plus finite A.12.**  Every profile/Taylor/block
hypothesis is discharged by the fixed-cutoff geometric schedule. -/
theorem prefixProfileLower_le_constrainedProfileWeight
    {q : ℕ} (hq : geometricCutoff ≤ q) :
    prefixProfileLower q ≤
      constrainedProfileWeight q chosenProfileDelta := by
  simpa [prefixProfileLower, chosenProfileDelta] using
    cutoff_canonicalGeometricSchedule_profileLower_le hq

/-- Explicit finite cost bound for the corrected fixed-prefix denominator. -/
lemma prefixProfileCost_le_geometricCost {q : ℕ} (hq : geometricCutoff ≤ q) :
    prefixProfileCost q ≤
      geometricProfileCostCoefficient geometricCutoff *
        (q : ℝ) ^ (3 / 5 : ℝ) := by
  simpa [prefixProfileCost, chosenProfileDelta] using
    canonicalGeometric_multiblockProfileCost_le
      geometricCutoff_ge_thirty_two hq

/-- Integer padding `ceil(3 log q)` used between the separation scale and the
inner profile block in HLOZ A.15--A.17. -/
def decorrelationPadding (q : ℕ) : ℕ := ⌈3 * Real.log q⌉₊

/-- The integer padding differs from `3 log q` by strictly less than one. -/
lemma decorrelationPadding_cast_lt_add_one {q : ℕ} (hq : 1 ≤ q) :
    (decorrelationPadding q : ℝ) < 3 * Real.log q + 1 := by
  unfold decorrelationPadding
  exact Nat.ceil_lt_add_one (mul_nonneg (by norm_num)
    (Real.log_nonneg (by exact_mod_cast hq)))

/-- The logarithmic padding is eventually strictly smaller than its scale. -/
lemma eventually_decorrelationPadding_lt :
    ∀ᶠ q : ℕ in atTop, decorrelationPadding q < q := by
  have hsmallReal := Real.isLittleO_log_id_atTop.bound
    (show (0 : ℝ) < 1 / 12 by norm_num)
  have hsmall := tendsto_natCast_atTop_atTop.eventually hsmallReal
  filter_upwards [hsmall, eventually_ge_atTop 2] with q hlog hq
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hlog0 : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hlog' : Real.log (q : ℝ) ≤ (q : ℝ) / 12 := by
    simpa [id, Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hq0,
      div_eq_mul_inv, mul_comm] using hlog
  have hp := decorrelationPadding_cast_lt_add_one
    (q := q) (by omega : 1 ≤ q)
  have hqR : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hpq : (decorrelationPadding q : ℝ) < q := by linarith
  exact_mod_cast hpq

/-- The fixed A.11/A.12 cutoff is eventually contained in the logarithmic
decorrelation prefix. -/
lemma eventually_geometricCutoff_le_decorrelationPadding :
    ∀ᶠ q : ℕ in atTop, geometricCutoff ≤ decorrelationPadding q := by
  have hlog := tendsto_log_nat_atTop.eventually
    (eventually_ge_atTop ((geometricCutoff : ℝ) / 3))
  filter_upwards [hlog] with q hq
  have hceil := Nat.le_ceil (3 * Real.log (q : ℝ))
  have hreal : (geometricCutoff : ℝ) ≤
      (decorrelationPadding q : ℝ) := by
    unfold decorrelationPadding
    linarith
  exact_mod_cast hreal

/-- A positive power eventually absorbs the complete logarithmic padding,
with the exact `3/16` share used by the corrected pair certificate. -/
lemma eventually_decorrelationPadding_budget_rpow {a : ℝ} (ha : 0 < a) :
    ∀ᶠ q : ℕ in atTop,
      2 + 2 * (decorrelationPadding q : ℝ) ≤
        3 * (q : ℝ) ^ a / 16 := by
  have hlogReal := (isLittleO_log_rpow_atTop ha).bound
    (show (0 : ℝ) < 1 / 64 by norm_num)
  have hlog := tendsto_natCast_atTop_atTop.eventually hlogReal
  have hpow := ((tendsto_rpow_atTop ha).comp
    tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop 128)
  filter_upwards [hlog, hpow, eventually_ge_atTop 2] with q hlog hpow hq
  simp only [Function.comp_apply] at hpow
  have hq0 : (0 : ℝ) ≤ q := by positivity
  have hlog0 : 0 ≤ Real.log (q : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ q))
  have hrpow0 : 0 ≤ (q : ℝ) ^ a := Real.rpow_nonneg hq0 _
  have hlog' : Real.log (q : ℝ) ≤
      (1 / 64 : ℝ) * (q : ℝ) ^ a := by
    simpa [Function.comp_apply, Real.norm_of_nonneg hlog0,
      Real.norm_of_nonneg hrpow0] using hlog
  have hp := decorrelationPadding_cast_lt_add_one
    (q := q) (by omega : 1 ≤ q)
  linarith

/-- The shifted prefix scale used for a pair first separating at `l`, capped
at the full profile scale. -/
def pairPrefixScale (q l : ℕ) : ℕ := min q (l + decorrelationPadding q)

/-- A budget at the ambient scale controls every geometric prefix cost.
This is the exact finite bridge used after separation at level `l`. -/
lemma prefixProfileCost_pairPrefixScale_le_of_budget
    {q l : ℕ} {C : ℝ}
    (hcutoff : geometricCutoff ≤ pairPrefixScale q l)
    (hbudget : geometricProfileCostCoefficient geometricCutoff *
        (q : ℝ) ^ (3 / 5 : ℝ) ≤ C) :
    prefixProfileCost (pairPrefixScale q l) ≤ C := by
  have hfinite := prefixProfileCost_le_geometricCost hcutoff
  have hprefix : (pairPrefixScale q l : ℝ) ^ (3 / 5 : ℝ) ≤
      (q : ℝ) ^ (3 / 5 : ℝ) := by
    apply Real.rpow_le_rpow (Nat.cast_nonneg _)
    · exact_mod_cast min_le_left q (l + decorrelationPadding q)
    · norm_num
  have hcoeff0 : 0 ≤ geometricProfileCostCoefficient geometricCutoff :=
    geometricProfileCostCoefficient_nonneg _
  exact hfinite.trans ((mul_le_mul_of_nonneg_left hprefix hcoeff0).trans hbudget)

/-- Last separation level to which the A.5 prefix decorrelation argument is
applied.  Levels above it form the single close band of A.6. -/
def decorrelationCutoff (q : ℕ) : ℕ := q - decorrelationPadding q

/-- The exact near-band radius is at most `3 q^12`: the `q^9` base radius
and the `ceil (3 log q)` cutoff contribute the remaining cubic factor. -/
lemma cutoff_scaleRadius_le_three_mul_pow12 {q : ℕ} (hq : 1 ≤ q)
    (hpad : decorrelationPadding q ≤ q) :
    ThickPoint.scaleRadius q (decorrelationCutoff q) ≤
      3 * (q + 1 : ℝ) ^ (12 : ℕ) := by
  have hp := decorrelationPadding_cast_lt_add_one hq
  have hqpos : (0 : ℝ) < q := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hq)
  have hexpPad : Real.exp (decorrelationPadding q : ℝ) ≤
      3 * (q : ℝ) ^ (3 : ℕ) := by
    calc
      Real.exp (decorrelationPadding q : ℝ) ≤
          Real.exp (3 * Real.log q + 1) := Real.exp_le_exp.mpr hp.le
      _ = Real.exp 1 * Real.exp (3 * Real.log q) := by
        rw [Real.exp_add]
        ring
      _ = Real.exp 1 * (Real.exp (Real.log q)) ^ (3 : ℕ) := by
        rw [← Real.exp_nat_mul]
        norm_num
      _ = Real.exp 1 * (q : ℝ) ^ (3 : ℕ) := by
        rw [Real.exp_log hqpos]
      _ ≤ 3 * (q : ℝ) ^ (3 : ℕ) := by
        gcongr
        exact Real.exp_one_lt_three.le
  unfold decorrelationCutoff
  rw [ThickPoint.scaleRadius_of_le (Nat.sub_le _ _)]
  unfold ThickPoint.regularRadius
  have hexponent : (q : ℝ) - (q - decorrelationPadding q : ℕ) =
      (decorrelationPadding q : ℝ) := by
    rw [Nat.cast_sub hpad]
    ring
  rw [hexponent]
  calc
    Real.exp (decorrelationPadding q : ℝ) * (q : ℝ) ^ 9 ≤
        (3 * (q : ℝ) ^ 3) * (q : ℝ) ^ 9 :=
      mul_le_mul_of_nonneg_right hexpPad (by positivity)
    _ = 3 * (q : ℝ) ^ 12 := by ring
    _ ≤ 3 * ((q : ℝ) + 1) ^ 12 := by
      gcongr
      linarith

/-- All cutoff geometry needed by the far/near pair split holds eventually
at the selected Proposition 1.3 scale. -/
theorem eventually_decorrelationCutoff_mem_scaleIndices {delta : ℝ} :
    ∀ᶠ n : ℕ in atTop,
      decorrelationCutoff (scaleIndex delta n) ∈
        scaleIndices (scaleIndex delta n) := by
  have hscaleNat : Tendsto (scaleIndex delta) atTop atTop :=
    tendsto_natCast_atTop_iff.mp (tendsto_scaleIndex_atTop delta)
  have hp := hscaleNat.eventually eventually_decorrelationPadding_lt
  filter_upwards [hp] with n hn
  simp only [scaleIndices, Finset.mem_Icc, decorrelationCutoff]
  omega

theorem eventually_cutoff_scaleRadius_le_three_mul_pow12 {delta : ℝ} :
    ∀ᶠ n : ℕ in atTop,
      ThickPoint.scaleRadius (scaleIndex delta n)
          (decorrelationCutoff (scaleIndex delta n)) ≤
        3 * (scaleIndex delta n + 1 : ℝ) ^ (12 : ℕ) := by
  have hscaleNat : Tendsto (scaleIndex delta) atTop atTop :=
    tendsto_natCast_atTop_iff.mp (tendsto_scaleIndex_atTop delta)
  have hp := hscaleNat.eventually eventually_decorrelationPadding_lt
  filter_upwards [hp, eventually_scaleIndex_pos delta] with n hp hq
  exact cutoff_scaleRadius_le_three_mul_pow12 hq hp.le

theorem eventually_geometricCutoff_le_pairPrefixScale {delta : ℝ} :
    ∀ᶠ n : ℕ in atTop,
      ∀ l ∈ Finset.Icc 1 (decorrelationCutoff (scaleIndex delta n)),
        geometricCutoff ≤ pairPrefixScale (scaleIndex delta n) l := by
  have hscaleNat : Tendsto (scaleIndex delta) atTop atTop :=
    tendsto_natCast_atTop_iff.mp (tendsto_scaleIndex_atTop delta)
  have hpad := hscaleNat.eventually
    eventually_geometricCutoff_le_decorrelationPadding
  have hq := hscaleNat.eventually (eventually_ge_atTop geometricCutoff)
  filter_upwards [hpad, hq] with n hpad hq
  intro l _hl
  unfold pairPrefixScale
  apply le_min hq
  omega

theorem eventually_decorrelationPadding_le_scaleCost_share
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      2 + 2 * (decorrelationPadding (scaleIndex delta n) : ℝ) ≤
        3 * scaleCost delta n / 16 := by
  have hscaleNat : Tendsto (scaleIndex delta) atTop atTop :=
    tendsto_natCast_atTop_iff.mp (tendsto_scaleIndex_atTop delta)
  have h := hscaleNat.eventually
    (eventually_decorrelationPadding_budget_rpow (costExponent_pos hdelta))
  simpa only [scaleCost] using h

/-- The explicit HLOZ correlation envelope before the annular multiplicative
loss.  Well-separated pairs pay the inverse checked prefix probability;
close pairs use the one-point upper bound. -/
def prefixPairEnvelope (q : ℕ) (pointUpper : ℝ) (l : ℕ) : ℝ :=
  if l + decorrelationPadding q ≤ q then
    pointUpper ^ 2 / prefixProfileLower (pairPrefixScale q l)
  else pointUpper

lemma pairPrefixScale_eq_of_add_le {q l : ℕ}
    (h : l + decorrelationPadding q ≤ q) :
    pairPrefixScale q l = l + decorrelationPadding q := by
  simp [pairPrefixScale, h]

/-- Explicit candidate-square normalization for a regular separation
stratum.  The harmless `exp 2` shift comes from using radius `r_{q,l-1}`
for level `l`; it is retained as an additive budget rather than hidden in a
constant. -/
lemma levelPairCountBound_le_geometricEnvelope
    {q l : ℕ} (hq : 1 ≤ q) (hl : 1 ≤ l) (hlq : l ≤ q) :
    (levelPairCountBound (ThickPoint.candidateBox q) q l : ℝ) ≤
      256 * ((ThickPoint.candidateBox q).card : ℝ) ^ 2 *
        Real.exp (-2 * (l : ℝ) + 2) := by
  by_cases hlone : l = 1
  · subst l
    simp [levelPairCountBound]
    have hM : 0 ≤ ((ThickPoint.candidateBox q).card : ℝ) := Nat.cast_nonneg _
    nlinarith [sq_nonneg ((ThickPoint.candidateBox q).card : ℝ)]
  · have hl2 : 2 ≤ l := by omega
    have hlsub : l - 1 ≤ q := by omega
    have hsentinel : l ≠ q + 2 := by omega
    let r : ℝ := ThickPoint.scaleRadius q (l - 1)
    let r0 : ℝ := ThickPoint.regularRadius q 0
    let c : ℕ := ⌈2 * r⌉₊
    let S : ℕ := (ThickPoint.candidateInterval q).card
    let M : ℕ := (ThickPoint.candidateBox q).card
    have hqReal : (1 : ℝ) ≤ q := by exact_mod_cast hq
    have hexponent : (0 : ℝ) ≤ (q : ℝ) - (l - 1 : ℕ) := by
      apply sub_nonneg.mpr
      exact_mod_cast hlsub
    have hr1 : (1 : ℝ) ≤ r := by
      dsimp only [r]
      rw [ThickPoint.scaleRadius_of_le hlsub]
      unfold ThickPoint.regularRadius
      have he : 1 ≤ Real.exp ((q : ℝ) - (l - 1 : ℕ)) :=
        Real.one_le_exp_iff.mpr hexponent
      have hp : 1 ≤ (q : ℝ) ^ (9 : ℕ) := one_le_pow₀ hqReal
      nlinarith
    have hc : (c : ℝ) < 2 * r + 1 := by
      dsimp only [c]
      exact Nat.ceil_lt_add_one (by
        have := scaleRadius_nonneg q (l - 1)
        positivity)
    have hside : ((2 * c + 1 : ℕ) : ℝ) ≤ 7 * r := by
      push_cast
      linarith
    have harea : (((2 * c + 1) ^ 2 : ℕ) : ℝ) ≤ 49 * r ^ 2 := by
      push_cast
      have hsquare := pow_le_pow_left₀
        (by positivity : (0 : ℝ) ≤ (2 * c + 1 : ℕ)) hside 2
      nlinarith
    have hrrel : r = r0 * Real.exp (-(l - 1 : ℕ)) := by
      dsimp only [r, r0]
      rw [ThickPoint.scaleRadius_of_le hlsub]
      unfold ThickPoint.regularRadius
      push_cast
      rw [Real.exp_sub, Real.exp_neg]
      ring
    have hr0S : r0 ≤ 2 * S := by
      simpa [r0, S] using
        regularRadius_zero_le_two_mul_candidateInterval_card (by omega : 2 ≤ q)
    have hr00 : 0 ≤ r0 := by
      dsimp only [r0]
      unfold ThickPoint.regularRadius
      positivity
    have hr0sq : r0 ^ 2 ≤ 4 * (M : ℝ) := by
      have hsquare := pow_le_pow_left₀ hr00 hr0S 2
      calc
        r0 ^ 2 ≤ (2 * (S : ℝ)) ^ 2 := by simpa using hsquare
        _ = 4 * (M : ℝ) := by
          dsimp only [M, S]
          rw [ThickPoint.card_candidateBox]
          push_cast
          ring
    have hrSq : r ^ 2 ≤
        4 * (M : ℝ) * Real.exp (-2 * (l : ℝ) + 2) := by
      rw [hrrel]
      have he0 : 0 ≤ Real.exp (-(l - 1 : ℕ)) ^ 2 := by positivity
      calc
        (r0 * Real.exp (-(l - 1 : ℕ))) ^ 2 =
            r0 ^ 2 * Real.exp (-(l - 1 : ℕ)) ^ 2 := by ring
        _ ≤ (4 * (M : ℝ)) * Real.exp (-(l - 1 : ℕ)) ^ 2 :=
          mul_le_mul_of_nonneg_right hr0sq he0
        _ = 4 * (M : ℝ) * Real.exp (-2 * (l : ℝ) + 2) := by
          rw [← Real.exp_nat_mul]
          rw [Nat.cast_sub (by omega : 1 ≤ l)]
          congr 2
          ring
    have harea' : (((2 * c + 1) ^ 2 : ℕ) : ℝ) ≤
        196 * (M : ℝ) * Real.exp (-2 * (l : ℝ) + 2) := by
      calc
        (((2 * c + 1) ^ 2 : ℕ) : ℝ) ≤ 49 * r ^ 2 := harea
        _ ≤ 49 * (4 * (M : ℝ) * Real.exp (-2 * (l : ℝ) + 2)) :=
          mul_le_mul_of_nonneg_left hrSq (by norm_num)
        _ = _ := by ring
    have hM0 : 0 ≤ (M : ℝ) := Nat.cast_nonneg _
    unfold levelPairCountBound
    rw [if_neg hlone, if_neg hsentinel]
    change (((M * (2 * c + 1) ^ 2 : ℕ) : ℝ)) ≤ _
    rw [Nat.cast_mul]
    calc
      (M : ℝ) * (((2 * c + 1) ^ 2 : ℕ) : ℝ) ≤
          (M : ℝ) *
            (196 * (M : ℝ) * Real.exp (-2 * (l : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left harea' hM0
      _ ≤ 256 * (M : ℝ) ^ 2 * Real.exp (-2 * (l : ℝ) + 2) := by
        have he0 : 0 ≤ Real.exp (-2 * (l : ℝ) + 2) := Real.exp_nonneg _
        nlinarith [sq_nonneg (M : ℝ)]

/-- The finite exponential bookkeeping in one far separation stratum.
The hypotheses expose four genuinely distinct costs: the two one-point
upper errors, the fixed-prefix denominator error, the sequential Harnack
error, and the polynomial padding `exp (2 ceil(3 log q))`.  Once their sum
fits in the reserved quarter-budget, the exact level term has the envelope
used by `offDiagonalPairBound`. -/
theorem farLevelTerm_le_of_explicitBudgets
    {q l : ℕ} {pointUpper harnackFactor A B H C : ℝ}
    (hadd : l + decorrelationPadding q ≤ q)
    (hprefixCutoff : geometricCutoff ≤ pairPrefixScale q l)
    (hpoint0 : 0 ≤ pointUpper)
    (hpoint : pointUpper ≤ Real.exp (-2 * (q : ℝ) + A))
    (hharnack0 : 0 ≤ harnackFactor)
    (hharnack : harnackFactor ≤ Real.exp H)
    (hcount :
      (levelPairCountBound (ThickPoint.candidateBox q) q l : ℝ) ≤
        256 * ((ThickPoint.candidateBox q).card : ℝ) ^ 2 *
          Real.exp (-2 * (l : ℝ) + 2))
    (hprefixCost : prefixProfileCost (pairPrefixScale q l) ≤ B)
    (hbudget : 2 * A + B + H + 2 +
        2 * (decorrelationPadding q : ℝ) ≤ C / 4) :
    (levelPairCountBound (ThickPoint.candidateBox q) q l : ℝ) *
        (harnackFactor *
          (pointUpper ^ 2 / prefixProfileLower (pairPrefixScale q l))) ≤
      256 * ((ThickPoint.candidateBox q).card : ℝ) ^ 2 *
        Real.exp (-4 * (q : ℝ) + C / 4) := by
  have hpointSq : pointUpper ^ 2 ≤
      Real.exp (-4 * (q : ℝ) + 2 * A) := by
    calc
      pointUpper ^ 2 ≤ (Real.exp (-2 * (q : ℝ) + A)) ^ 2 :=
        pow_le_pow_left₀ hpoint0 hpoint 2
      _ = Real.exp (-4 * (q : ℝ) + 2 * A) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  have hdiv := div_prefixProfileLower_le_mul_exp
    hprefixCutoff (sq_nonneg pointUpper) hprefixCost
  have hdiv' : pointUpper ^ 2 / prefixProfileLower (pairPrefixScale q l) ≤
      Real.exp (-4 * (q : ℝ) + 2 * A) *
        Real.exp (2 * (pairPrefixScale q l : ℝ) + B) :=
    hdiv.trans (mul_le_mul_of_nonneg_right hpointSq (Real.exp_nonneg _))
  have hinner : harnackFactor *
        (pointUpper ^ 2 / prefixProfileLower (pairPrefixScale q l)) ≤
      Real.exp H *
        (Real.exp (-4 * (q : ℝ) + 2 * A) *
          Real.exp (2 * (pairPrefixScale q l : ℝ) + B)) := by
    calc
      harnackFactor *
          (pointUpper ^ 2 / prefixProfileLower (pairPrefixScale q l)) ≤
        Real.exp H *
          (pointUpper ^ 2 / prefixProfileLower (pairPrefixScale q l)) := by
            exact mul_le_mul_of_nonneg_right hharnack
              (div_nonneg (sq_nonneg _) (prefixProfileLower_nonneg _))
      _ ≤ _ := mul_le_mul_of_nonneg_left hdiv' (Real.exp_nonneg _)
  have hinner0 : 0 ≤ harnackFactor *
      (pointUpper ^ 2 / prefixProfileLower (pairPrefixScale q l)) := by
    exact mul_nonneg hharnack0
      (div_nonneg (sq_nonneg _) (prefixProfileLower_nonneg _))
  rw [pairPrefixScale_eq_of_add_le hadd] at hinner hinner0 ⊢
  have hexpCombine :
      Real.exp (-2 * (l : ℝ) + 2) *
          (Real.exp H *
            (Real.exp (-4 * (q : ℝ) + 2 * A) *
              Real.exp (2 * ((l + decorrelationPadding q : ℕ) : ℝ) + B))) =
        Real.exp (-4 * (q : ℝ) +
          (2 * A + B + H + 2 + 2 * (decorrelationPadding q : ℝ))) := by
    rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    push_cast
    ring
  calc
    (levelPairCountBound (ThickPoint.candidateBox q) q l : ℝ) *
          (harnackFactor *
            (pointUpper ^ 2 /
              prefixProfileLower (l + decorrelationPadding q))) ≤
        (256 * ((ThickPoint.candidateBox q).card : ℝ) ^ 2 *
          Real.exp (-2 * (l : ℝ) + 2)) *
          (Real.exp H *
            (Real.exp (-4 * (q : ℝ) + 2 * A) *
              Real.exp (2 * ((l + decorrelationPadding q : ℕ) : ℝ) + B))) :=
      mul_le_mul hcount hinner hinner0 (by positivity)
    _ = 256 * ((ThickPoint.candidateBox q).card : ℝ) ^ 2 *
        Real.exp (-4 * (q : ℝ) +
          (2 * A + B + H + 2 + 2 * (decorrelationPadding q : ℝ))) := by
      rw [show
        (256 * ((ThickPoint.candidateBox q).card : ℝ) ^ 2 *
            Real.exp (-2 * (l : ℝ) + 2)) *
            (Real.exp H *
              (Real.exp (-4 * (q : ℝ) + 2 * A) *
                Real.exp (2 * ((l + decorrelationPadding q : ℕ) : ℝ) + B))) =
          (256 * ((ThickPoint.candidateBox q).card : ℝ) ^ 2) *
            (Real.exp (-2 * (l : ℝ) + 2) *
              (Real.exp H *
                (Real.exp (-4 * (q : ℝ) + 2 * A) *
                  Real.exp (2 * ((l + decorrelationPadding q : ℕ) : ℝ) + B)))) by
          ring]
      rw [hexpCombine]
    _ ≤ 256 * ((ThickPoint.candidateBox q).card : ℝ) ^ 2 *
        Real.exp (-4 * (q : ℝ) + C / 4) := by
      apply mul_le_mul_of_nonneg_left
      · exact Real.exp_le_exp.mpr (by linarith)
      · positivity

/-- The same far-stratum estimate with its lattice pair count discharged by
the exact HLOZ radii and candidate-square normalization. -/
theorem farLevelTerm_le_of_analyticBudgets
    {q l : ℕ} {pointUpper harnackFactor A B H C : ℝ}
    (hq : 1 ≤ q) (hl : 1 ≤ l) (hlq : l ≤ q)
    (hadd : l + decorrelationPadding q ≤ q)
    (hprefixCutoff : geometricCutoff ≤ pairPrefixScale q l)
    (hpoint0 : 0 ≤ pointUpper)
    (hpoint : pointUpper ≤ Real.exp (-2 * (q : ℝ) + A))
    (hharnack0 : 0 ≤ harnackFactor)
    (hharnack : harnackFactor ≤ Real.exp H)
    (hprefixCost : prefixProfileCost (pairPrefixScale q l) ≤ B)
    (hbudget : 2 * A + B + H + 2 +
        2 * (decorrelationPadding q : ℝ) ≤ C / 4) :
    (levelPairCountBound (ThickPoint.candidateBox q) q l : ℝ) *
        (harnackFactor *
          (pointUpper ^ 2 / prefixProfileLower (pairPrefixScale q l))) ≤
      256 * ((ThickPoint.candidateBox q).card : ℝ) ^ 2 *
        Real.exp (-4 * (q : ℝ) + C / 4) := by
  exact farLevelTerm_le_of_explicitBudgets hadd hprefixCutoff hpoint0 hpoint
    hharnack0 hharnack
    (levelPairCountBound_le_geometricEnvelope hq hl hlq)
    hprefixCost hbudget

lemma prefixPairEnvelope_nonneg {q : ℕ} {pointUpper : ℝ}
    (hpoint : 0 ≤ pointUpper) (l : ℕ) :
    0 ≤ prefixPairEnvelope q pointUpper l := by
  unfold prefixPairEnvelope
  split
  · exact div_nonneg (sq_nonneg _) (prefixProfileLower_nonneg _)
  · exact hpoint

/-- Walk-facing pointwise annular comparison.  Unlike the old certificate
field, this does not assume a summed moment: it compares one ordered pair to
the explicit A.11/A.12 prefix denominator at its actual separation level. -/
structure AnnularPrefixPairComparison
    (blockCount blockLength q : ℕ) (profileDelta thickDelta : ℝ)
    (pointUpper harnackFactor : ℝ) : Prop where
  pointUpper_nonneg : 0 ≤ pointUpper
  harnackFactor_nonneg : 0 ≤ harnackFactor
  pair_le : ∀ (i : Fin blockCount) x,
    x ∈ ThickPoint.candidateBox q → ∀ y,
    y ∈ ThickPoint.candidateBox q →
    fairSteps.real
        (stoppedThickPointEvent ((i : ℕ) * blockLength)
            q profileDelta thickDelta x ∩
          stoppedThickPointEvent ((i : ℕ) * blockLength)
            q profileDelta thickDelta y) ≤
      harnackFactor *
        prefixPairEnvelope q pointUpper (separationLevel q x y)

/-- The pointwise annular/Markov comparison, the checked A.11/A.12 prefix,
and the exact lattice pair counts produce this explicit finite upper bound
for the literal stopped thick-point double sum. -/
theorem pairMoment_le_explicitPrefixSeparationSum
    {blockCount blockLength q : ℕ} {profileDelta thickDelta : ℝ}
    {pointUpper harnackFactor : ℝ}
    (hAnnular : AnnularPrefixPairComparison blockCount blockLength q
      profileDelta thickDelta pointUpper harnackFactor) :
    ∀ i : Fin blockCount,
      (∑ x ∈ ThickPoint.candidateBox q,
        ∑ y ∈ ThickPoint.candidateBox q,
          fairSteps.real
            (stoppedThickPointEvent ((i : ℕ) * blockLength)
                q profileDelta thickDelta x ∩
              stoppedThickPointEvent ((i : ℕ) * blockLength)
                q profileDelta thickDelta y)) ≤
        ∑ l ∈ Finset.Icc 1 (q + 2),
          (levelPairCountBound (ThickPoint.candidateBox q) q l : ℝ) *
            (harnackFactor * prefixPairEnvelope q pointUpper l) := by
  intro i
  apply pairSum_le_explicit_separationEnvelope
  · intro l hl
    exact mul_nonneg hAnnular.harnackFactor_nonneg
      (prefixPairEnvelope_nonneg hAnnular.pointUpper_nonneg l)
  · intro x hx y hy
    exact hAnnular.pair_le i x hx y hy

/-- The walk-facing assumptions in the exact A.5/A.6 form.  The far-pair
comparison is the annular Harnack/strong-Markov input.  The separate
one-point upper bound controls the complete close band by event inclusion;
it is not incorrectly identified with the first-moment lower bound. -/
structure AnnularFarNearPairComparison
    (blockCount blockLength q : ℕ) (profileDelta thickDelta : ℝ)
    (pointUpper harnackFactor : ℝ) : Prop where
  pointUpper_nonneg : 0 ≤ pointUpper
  harnackFactor_nonneg : 0 ≤ harnackFactor
  onePoint_le : ∀ (i : Fin blockCount) x,
    x ∈ ThickPoint.candidateBox q →
    fairSteps.real
        (stoppedThickPointEvent ((i : ℕ) * blockLength)
          q profileDelta thickDelta x) ≤ pointUpper
  farPair_le : ∀ (i : Fin blockCount) x,
    x ∈ ThickPoint.candidateBox q → ∀ y,
    y ∈ ThickPoint.candidateBox q →
    separationLevel q x y ≤ decorrelationCutoff q →
    fairSteps.real
        (stoppedThickPointEvent ((i : ℕ) * blockLength)
            q profileDelta thickDelta x ∩
          stoppedThickPointEvent ((i : ℕ) * blockLength)
            q profileDelta thickDelta y) ≤
      harnackFactor *
        (pointUpper ^ 2 /
          prefixProfileLower (pairPrefixScale q (separationLevel q x y)))

/-! ## Honest marked-skeleton upper disintegration -/

/-- Pointwise upper comparison for the joint terminal visit-count/exit-mark
kernel.  The exit mark is retained, so this comparison can be inserted into
an arbitrary complete complementary-skeleton weight. -/
def MarkedKernelUpper
    {Entrance Exit : Type*} {m : ℕ}
    (loss : Fin m → ℝ≥0∞)
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞)
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞) : Prop :=
  ∀ j u k z, markedKernel j u k z ≤
    loss j * referenceMass j k * skeletonKernel j u z

/-- The single-coordinate upper loss forced by the marked Poisson-kernel
algebra.  Positive visit atoms cost the product of the hit and exit Harnack
factors.  The zero atom costs the odds-amplified subtraction factor, and the
maximum handles both cases uniformly. -/
def markedPoissonUpperLoss (q hitError exitError : ℝ) : ℝ :=
  max ((1 + hitError) * (1 + exitError))
    (1 + (hitError + exitError - hitError * exitError) * q / (1 - q))

/-- When the reference hit probability is at most one half, the positive and
zero marked-atom losses are both bounded by a linear error. -/
lemma markedPoissonUpperLoss_le_one_add_two_errors
    {q hitError exitError : ℝ}
    (hq0 : 0 ≤ q) (hqHalf : q ≤ 1 / 2)
    (hhit0 : 0 ≤ hitError)
    (hexit0 : 0 ≤ exitError) (hexit1 : exitError ≤ 1) :
    markedPoissonUpperLoss q hitError exitError ≤
      1 + 2 * (hitError + exitError) := by
  have hdenom : 0 < 1 - q := by linarith
  have hratio0 : 0 ≤ q / (1 - q) := div_nonneg hq0 hdenom.le
  have hratio1 : q / (1 - q) ≤ 1 := by
    rw [div_le_one hdenom]
    linarith
  have hproduct0 : 0 ≤ hitError * exitError := mul_nonneg hhit0 hexit0
  have hcoeff0 : 0 ≤ hitError + exitError - hitError * exitError := by
    nlinarith
  apply max_le
  · nlinarith [mul_le_mul_of_nonneg_left hexit1 hhit0]
  · have hmul : (hitError + exitError - hitError * exitError) *
        (q / (1 - q)) ≤ hitError + exitError - hitError * exitError :=
      mul_le_of_le_one_right hcoeff0 hratio1
    have heq : (hitError + exitError - hitError * exitError) * q / (1 - q) =
        (hitError + exitError - hitError * exitError) * (q / (1 - q)) := by
      ring
    rw [heq]
    nlinarith

/-- The product of all marked Poisson losses is controlled by the
exponential of the sum of the first-hit and exit-kernel errors. -/
theorem prod_markedPoissonUpperLoss_toReal_le_exp
    {m : ℕ} (q hitError exitError : Fin m → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hqHalf : ∀ j, q j ≤ 1 / 2)
    (hhit0 : ∀ j, 0 ≤ hitError j)
    (hexit0 : ∀ j, 0 ≤ exitError j) (hexit1 : ∀ j, exitError j ≤ 1) :
    (∏ j, ENNReal.ofReal
      (markedPoissonUpperLoss (q j) (hitError j) (exitError j))).toReal ≤
      Real.exp (2 * ∑ j, (hitError j + exitError j)) := by
  rw [ENNReal.toReal_prod]
  have hloss0 (j : Fin m) : 0 ≤
      markedPoissonUpperLoss (q j) (hitError j) (exitError j) := by
    exact (mul_nonneg (by linarith [hhit0 j])
      (by linarith [hexit0 j])).trans (le_max_left _ _)
  simp_rw [ENNReal.toReal_ofReal (hloss0 _)]
  calc
    ∏ j, markedPoissonUpperLoss (q j) (hitError j) (exitError j) ≤
        ∏ j, Real.exp (2 * (hitError j + exitError j)) := by
      apply Finset.prod_le_prod
      · intro j _hj
        exact hloss0 j
      · intro j _hj
        exact (markedPoissonUpperLoss_le_one_add_two_errors
          (hq0 j) (hqHalf j) (hhit0 j) (hexit0 j) (hexit1 j)).trans
            (by simpa [add_comm] using (Real.add_one_le_exp
              (2 * (hitError j + exitError j))))
    _ = Real.exp (2 * ∑ j, (hitError j + exitError j)) := by
      rw [← Real.exp_sum]
      congr 2
      rw [Finset.mul_sum]

/-- Exact scale-budget specialization for the accumulated joint marked
Poisson loss. -/
theorem prod_markedPoissonUpperLoss_toReal_le_scaleCost
    {delta : ℝ} {n m : ℕ} (q hitError exitError : Fin m → ℝ)
    (hq0 : ∀ j, 0 ≤ q j) (hqHalf : ∀ j, q j ≤ 1 / 2)
    (hhit0 : ∀ j, 0 ≤ hitError j)
    (hexit0 : ∀ j, 0 ≤ exitError j) (hexit1 : ∀ j, exitError j ≤ 1)
    (hbudget : 2 * ∑ j, (hitError j + exitError j) ≤
      scaleCost delta n / 64) :
    (∏ j, ENNReal.ofReal
      (markedPoissonUpperLoss (q j) (hitError j) (exitError j))).toReal ≤
      Real.exp (scaleCost delta n / 64) :=
  (prod_markedPoissonUpperLoss_toReal_le_exp q hitError exitError
    hq0 hqHalf hhit0 hexit0 hexit1).trans (Real.exp_le_exp.mpr hbudget)

/-- A two-sided first-hit comparison and a two-sided pointwise exit-kernel
comparison imply the exact joint visit-count/exit-mark upper bound required
by the complete-skeleton disintegration.  This theorem includes the delicate
zero-visit atom, rather than treating all atoms as a positive geometric
factor. -/
theorem regeneratedMarkedKernel_markedKernelUpper
    {Entrance Exit : Type*} {m : ℕ}
    (outer : Fin m → Entrance → Exit → ℝ)
    (center : Fin m → Entrance)
    (hit : Fin m → Entrance → ℝ)
    (escape q hitError exitError : Fin m → ℝ)
    (hescape0 : ∀ j, 0 ≤ escape j)
    (hescape1 : ∀ j, escape j ≤ 1)
    (hq0 : ∀ j, 0 ≤ q j) (hq1 : ∀ j, q j < 1)
    (hhitError0 : ∀ j, 0 ≤ hitError j)
    (hexitError0 : ∀ j, 0 ≤ exitError j)
    (hhitLowerOne0 : ∀ j, 0 ≤ 1 - hitError j)
    (hhitLowerFactor0 : ∀ j, 0 ≤ (1 - hitError j) * q j)
    (hexitLowerFactor0 : ∀ j, 0 ≤ 1 - exitError j)
    (houter0 : ∀ j u z, 0 ≤ outer j u z)
    (hcenter0 : ∀ j z, 0 ≤ outer j (center j) z)
    (hhitLower : ∀ j u, (1 - hitError j) * q j ≤ hit j u)
    (hhitUpper : ∀ j u, hit j u ≤ (1 + hitError j) * q j)
    (hexitLower : ∀ j u z,
      (1 - exitError j) * outer j u z ≤ outer j (center j) z)
    (hexitUpper : ∀ j u z,
      outer j (center j) z ≤ (1 + exitError j) * outer j u z) :
    MarkedKernelUpper
      (fun j ↦ ENNReal.ofReal
        (markedPoissonUpperLoss (q j) (hitError j) (exitError j)))
      (fun j k ↦ ENNReal.ofReal (visitMass (q j) (escape j) k))
      (fun j u z ↦ ENNReal.ofReal (outer j u z))
      (fun j u k z ↦ ENNReal.ofReal
        (regeneratedMarkedKernel (outer j) (center j) (hit j) (escape j)
          u k z)) := by
  intro j u k z
  have hpositiveFactor0 : 0 ≤ (1 + hitError j) * (1 + exitError j) :=
    mul_nonneg (by linarith [hhitError0 j]) (by linarith [hexitError0 j])
  have hloss0 : 0 ≤ markedPoissonUpperLoss (q j) (hitError j) (exitError j) :=
    hpositiveFactor0.trans (le_max_left _ _)
  have hvisit0 (r : ℕ) : 0 ≤ visitMass (q j) (escape j) r :=
    visitMass_nonneg (hq0 j) (le_of_lt (hq1 j))
      (hescape0 j) (hescape1 j) r
  cases k with
  | zero =>
      have hzero := regeneratedMarkedKernel_zero_upper
        (escape := escape j)
        (houter0 j u z) (hcenter0 j z) (hhitLower j u)
        (hexitLower j u z) (hhitLowerFactor0 j) (hexitLowerFactor0 j)
        (hq1 j)
      have hfactor :
          1 + (hitError j + exitError j - hitError j * exitError j) *
              q j / (1 - q j) ≤
            markedPoissonUpperLoss (q j) (hitError j) (exitError j) :=
        le_max_right _ _
      have hreal :
          regeneratedMarkedKernel (outer j) (center j) (hit j) (escape j)
              u 0 z ≤
            markedPoissonUpperLoss (q j) (hitError j) (exitError j) *
              visitMass (q j) (escape j) 0 * outer j u z := by
        exact hzero.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hfactor (hvisit0 0)) (houter0 j u z))
      have hof := ENNReal.ofReal_le_ofReal hreal
      calc
        _ ≤ ENNReal.ofReal
            (markedPoissonUpperLoss (q j) (hitError j) (exitError j) *
              visitMass (q j) (escape j) 0 * outer j u z) := hof
        _ = _ := by
          rw [ENNReal.ofReal_mul (mul_nonneg hloss0 (hvisit0 0)),
            ENNReal.ofReal_mul hloss0]
  | succ k =>
      have hcompare := regeneratedMarkedKernel_succ_compare
        (hq0 j) (hescape0 j) (hescape1 j) (houter0 j u z)
        (hhitLower j u) (hhitUpper j u) (hexitLower j u z)
        (hexitUpper j u z) (hhitError0 j) (hexitError0 j)
        (hhitLowerOne0 j) (hexitLowerFactor0 j) k
      have hfactor : (1 + hitError j) * (1 + exitError j) ≤
          markedPoissonUpperLoss (q j) (hitError j) (exitError j) :=
        le_max_left _ _
      have hreal :
          regeneratedMarkedKernel (outer j) (center j) (hit j) (escape j)
              u (k + 1) z ≤
            markedPoissonUpperLoss (q j) (hitError j) (exitError j) *
              visitMass (q j) (escape j) (k + 1) * outer j u z := by
        exact hcompare.2.trans (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hfactor (hvisit0 (k + 1)))
          (houter0 j u z))
      have hof := ENNReal.ofReal_le_ofReal hreal
      calc
        _ ≤ ENNReal.ofReal
            (markedPoissonUpperLoss (q j) (hitError j) (exitError j) *
              visitMass (q j) (escape j) (k + 1) * outer j u z) := hof
        _ = _ := by
          rw [ENNReal.ofReal_mul (mul_nonneg hloss0 (hvisit0 (k + 1))),
            ENNReal.ofReal_mul hloss0]

/-- Exact bookkeeping required for an upper bound on a stopped pair event.
The successful-event identity keeps the full outer skeleton, while
`pair_le_marked` is the pathwise containment of the thick-pair event in the
truncated terminal visit-vector event. -/
structure MarkedStoppedDataUpperDecomposition
    {Omega Data Entrance Exit : Type*} [MeasurableSpace Omega] {m : ℕ}
    (mu : Measure Omega) (pairEvent successful : Set Omega)
    (skeletonWeight : Data →
      (Fin m → Entrance) → (Fin m → Exit) → ℝ≥0∞)
    (skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞)
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ)) : Prop where
  successful_eq :
    mu successful = successfulSkeletonMass skeletonWeight skeletonKernel
  pair_le_marked :
    mu pairEvent ≤ markedVisitEventMass skeletonWeight markedKernel visitEvent

lemma markedProduct_le_loss_reference_skeleton
    {Entrance Exit : Type*} {m : ℕ}
    {loss : Fin m → ℝ≥0∞}
    {referenceMass : Fin m → ℕ → ℝ≥0∞}
    {skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞}
    {markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞}
    (hupper : MarkedKernelUpper loss referenceMass skeletonKernel markedKernel)
    (entrance : Fin m → Entrance) (exit : Fin m → Exit)
    (visits : Fin m → ℕ) :
    markedProduct markedKernel entrance exit visits ≤
      (∏ j, loss j) * referenceProduct referenceMass visits *
        skeletonProduct skeletonKernel entrance exit := by
  rw [referenceProduct, skeletonProduct, markedProduct]
  calc
    ∏ j, markedKernel j (entrance j) (visits j) (exit j) ≤
        ∏ j, (loss j * referenceMass j (visits j) *
          skeletonKernel j (entrance j) (exit j)) :=
      Finset.prod_le_prod' fun j _hj ↦
        hupper j (entrance j) (visits j) (exit j)
    _ = _ := by simp only [Finset.prod_mul_distrib]

private lemma fixedSkeleton_marked_upper
    {Entrance Exit : Type*} {m : ℕ}
    {loss : Fin m → ℝ≥0∞}
    {referenceMass : Fin m → ℕ → ℝ≥0∞}
    {skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞}
    {markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞}
    (hupper : MarkedKernelUpper loss referenceMass skeletonKernel markedKernel)
    (visitEvent : Set (Fin m → ℕ))
    (weight : ℝ≥0∞) (entrance : Fin m → Entrance) (exit : Fin m → Exit) :
    (∑' visits, restrictedMarkedProduct markedKernel visitEvent
        weight entrance exit visits) ≤
      (∏ j, loss j) * referenceEventMass referenceMass visitEvent *
        (weight * skeletonProduct skeletonKernel entrance exit) := by
  classical
  rw [referenceEventMass, ← ENNReal.tsum_mul_left,
    ← ENNReal.tsum_mul_right]
  apply ENNReal.tsum_le_tsum
  intro visits
  by_cases hvisits : visits ∈ visitEvent
  · rw [restrictedReferenceProduct, restrictedMarkedProduct,
      if_pos hvisits, if_pos hvisits]
    have hproduct := markedProduct_le_loss_reference_skeleton
      hupper entrance exit visits
    calc
      weight * markedProduct markedKernel entrance exit visits ≤
          weight * ((∏ j, loss j) * referenceProduct referenceMass visits *
            skeletonProduct skeletonKernel entrance exit) :=
        mul_le_mul le_rfl hproduct bot_le bot_le
      _ = (∏ j, loss j) * referenceProduct referenceMass visits *
          (weight * skeletonProduct skeletonKernel entrance exit) := by ac_rfl
  · rw [restrictedReferenceProduct, restrictedMarkedProduct,
      if_neg hvisits, if_neg hvisits]
    simp

/-- The marked upper comparison can be summed through an arbitrary complete
complementary-skeleton weight.  This is the upper analogue of
`MarkedTerminalDisintegration.markedVisitEventMass_lower`. -/
theorem markedVisitEventMass_upper
    {Data Entrance Exit : Type*} {m : ℕ}
    (loss : Fin m → ℝ≥0∞)
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (skeletonWeight : Data →
      (Fin m → Entrance) → (Fin m → Exit) → ℝ≥0∞)
    (skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞)
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    (hupper : MarkedKernelUpper loss referenceMass skeletonKernel markedKernel) :
    markedVisitEventMass skeletonWeight markedKernel visitEvent ≤
      (∏ j, loss j) * referenceEventMass referenceMass visitEvent *
        successfulSkeletonMass skeletonWeight skeletonKernel := by
  rw [successfulSkeletonMass, markedVisitEventMass,
    ← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro data
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro entrance
  rw [← ENNReal.tsum_mul_left]
  apply ENNReal.tsum_le_tsum
  intro exit
  exact fixedSkeleton_marked_upper hupper visitEvent
    (skeletonWeight data entrance exit) entrance exit

/-- Event-level marked-skeleton upper bound.  No measurability of the pair
event at an early terminal entrance is asserted: the whole complementary
skeleton is retained in `skeletonWeight`. -/
theorem event_upper_of_markedStoppedData
    {Omega Data Entrance Exit : Type*} [MeasurableSpace Omega]
    {m : ℕ} (mu : Measure Omega) (pairEvent successful : Set Omega)
    (loss : Fin m → ℝ≥0∞)
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (skeletonWeight : Data →
      (Fin m → Entrance) → (Fin m → Exit) → ℝ≥0∞)
    (skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞)
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    (hupper : MarkedKernelUpper loss referenceMass skeletonKernel markedKernel)
    (hdecompose : MarkedStoppedDataUpperDecomposition mu pairEvent successful
      skeletonWeight skeletonKernel markedKernel visitEvent) :
    mu pairEvent ≤
      ((∏ j, loss j) * referenceEventMass referenceMass visitEvent) *
        mu successful := by
  rw [hdecompose.successful_eq]
  exact hdecompose.pair_le_marked.trans
    (markedVisitEventMass_upper loss referenceMass skeletonWeight
      skeletonKernel markedKernel visitEvent hupper)

/-- The coefficient in the marked upper bound is finite whenever every local
Harnack loss is finite and the reference event has mass at most one. -/
lemma markedUpperCoefficient_ne_top
    {m : ℕ} (loss : Fin m → ℝ≥0∞)
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    (hloss : ∀ j, loss j ≠ ⊤)
    (href : referenceEventMass referenceMass visitEvent ≤ 1) :
    (∏ j, loss j) * referenceEventMass referenceMass visitEvent ≠ ⊤ :=
  ENNReal.mul_ne_top
    (ENNReal.prod_ne_top fun j _hj ↦ hloss j)
    (ne_top_of_le_ne_top ENNReal.one_ne_top href)

/-- Real-probability form of the complete marked-skeleton upper bound. -/
theorem event_real_upper_of_markedStoppedData
    {Omega Data Entrance Exit : Type*} [MeasurableSpace Omega]
    {m : ℕ} (mu : Measure Omega) [IsFiniteMeasure mu]
    (pairEvent successful : Set Omega)
    (loss : Fin m → ℝ≥0∞)
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (skeletonWeight : Data →
      (Fin m → Entrance) → (Fin m → Exit) → ℝ≥0∞)
    (skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞)
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    (hupper : MarkedKernelUpper loss referenceMass skeletonKernel markedKernel)
    (hdecompose : MarkedStoppedDataUpperDecomposition mu pairEvent successful
      skeletonWeight skeletonKernel markedKernel visitEvent)
    (hcoefficient :
      (∏ j, loss j) * referenceEventMass referenceMass visitEvent ≠ ⊤) :
    mu.real pairEvent ≤
      (((∏ j, loss j) * referenceEventMass referenceMass visitEvent).toReal) *
        mu.real successful := by
  have h := event_upper_of_markedStoppedData mu pairEvent successful loss
    referenceMass skeletonWeight skeletonKernel markedKernel visitEvent hupper
    hdecompose
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top hcoefficient (measure_ne_top mu successful)) h
  simpa only [Measure.real, ENNReal.toReal_mul] using hreal

/-- Far-pair specialization of the marked-skeleton disintegration.  The
reference visit-vector mass remains multiplied by the probability of the
complete successful skeleton, exactly as in the conditional argument of
HLOZ (A.16)--(A.17). -/
theorem stoppedFarPair_le_of_markedStoppedData
    {blockLength scale : ℕ} {profileDelta thickDelta : ℝ}
    {i : ℕ} {x y : Point}
    {Data Entrance Exit : Type*} {m : ℕ}
    (successful : Set StepPath)
    (loss : Fin m → ℝ≥0∞)
    (referenceMass : Fin m → ℕ → ℝ≥0∞)
    (skeletonWeight : Data →
      (Fin m → Entrance) → (Fin m → Exit) → ℝ≥0∞)
    (skeletonKernel : Fin m → Entrance → Exit → ℝ≥0∞)
    (markedKernel : Fin m → Entrance → ℕ → Exit → ℝ≥0∞)
    (visitEvent : Set (Fin m → ℕ))
    {harnackFactor pointUpper : ℝ} {prefixScale : ℕ}
    (hupper : MarkedKernelUpper loss referenceMass skeletonKernel markedKernel)
    (hdecompose : MarkedStoppedDataUpperDecomposition fairSteps
      (stoppedThickPointEvent (i * blockLength)
          scale profileDelta thickDelta x ∩
        stoppedThickPointEvent (i * blockLength)
          scale profileDelta thickDelta y)
      successful skeletonWeight skeletonKernel markedKernel visitEvent)
    (hcoefficient :
      (∏ j, loss j) * referenceEventMass referenceMass visitEvent ≠ ⊤)
    (hloss : (∏ j, loss j).toReal ≤ harnackFactor)
    (hharnack0 : 0 ≤ harnackFactor)
    (href : (referenceEventMass referenceMass visitEvent).toReal *
        fairSteps.real successful ≤
      pointUpper ^ 2 / prefixProfileLower prefixScale) :
    fairSteps.real
        (stoppedThickPointEvent (i * blockLength)
            scale profileDelta thickDelta x ∩
          stoppedThickPointEvent (i * blockLength)
            scale profileDelta thickDelta y) ≤
      harnackFactor *
        (pointUpper ^ 2 / prefixProfileLower prefixScale) := by
  have hreal := event_real_upper_of_markedStoppedData fairSteps
    (stoppedThickPointEvent (i * blockLength)
        scale profileDelta thickDelta x ∩
      stoppedThickPointEvent (i * blockLength)
        scale profileDelta thickDelta y)
    successful loss referenceMass skeletonWeight skeletonKernel markedKernel
    visitEvent hupper hdecompose hcoefficient
  have href0 : 0 ≤ (referenceEventMass referenceMass visitEvent).toReal *
      fairSteps.real successful :=
    mul_nonneg ENNReal.toReal_nonneg measureReal_nonneg
  calc
    fairSteps.real
        (stoppedThickPointEvent (i * blockLength)
            scale profileDelta thickDelta x ∩
          stoppedThickPointEvent (i * blockLength)
            scale profileDelta thickDelta y) ≤
        (((∏ j, loss j) *
            referenceEventMass referenceMass visitEvent).toReal) *
          fairSteps.real successful := hreal
    _ = (∏ j, loss j).toReal *
          ((referenceEventMass referenceMass visitEvent).toReal *
            fairSteps.real successful) := by
      rw [ENNReal.toReal_mul]
      ring
    _ ≤ harnackFactor *
          ((referenceEventMass referenceMass visitEvent).toReal *
            fairSteps.real successful) :=
      mul_le_mul_of_nonneg_right hloss href0
    _ ≤ harnackFactor *
          (pointUpper ^ 2 / prefixProfileLower prefixScale) :=
      mul_le_mul_of_nonneg_left href hharnack0

/-- The product of the successive conditional kernels inside one complete
stopped-data atom.  The kernel is allowed to depend on the entire datum;
thus later factors may depend on all earlier stopping times, entrance points,
exit points, and profile information. -/
def sequentialProductKernel {Data Entrance : Type*} {m : ℕ}
    (kernel : Fin m → Data → Entrance → ℝ)
    (entranceData : Data → Fin m → Entrance) (d : Data) : ℝ :=
  ∏ j, kernel j d (entranceData d j)

/-- One-sided sequential factorization on each complete stopped-data atom.
This is deliberately an inequality: conditioning on exact exit times or the
whole excursion profile does not give a coarse entrance-vector product law. -/
def SequentialStoppedKernelUpper {Data Entrance : Type*} {m : ℕ}
    (entranceData : Data → Fin m → Entrance)
    (kernel : Fin m → Data → Entrance → ℝ)
    (weight actualKernel : Data → ℝ) : Prop :=
  ∀ d, actualKernel d ≤ weight d * sequentialProductKernel kernel entranceData d

/-- One-sided disintegration of the stopped pair event over complete stopped
data.  This is the upper-bound counterpart of
`TerminalExcursionDisintegration.StoppedDataDisintegrationLower`. -/
def StoppedPairDataDisintegrationUpper
    {Omega Data : Type*} [MeasurableSpace Omega] [MeasurableSpace Data]
    (mu : Measure Omega) (pairEvent : Set Omega)
    (dataLaw : Measure Data) (actualKernel : Data → ℝ) : Prop :=
  mu.real pairEvent ≤ ∫ d, actualKernel d ∂dataLaw

/-- Accumulating a nonnegative multiplicative one-step error over finitely
many stopped coordinates costs at most the exponential of the summed error. -/
lemma pow_one_add_le_exp_nat_mul {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (m : ℕ) :
    (1 + epsilon) ^ m ≤ Real.exp ((m : ℝ) * epsilon) := by
  calc
    (1 + epsilon) ^ m ≤ (Real.exp epsilon) ^ m := by
      gcongr
      simpa [add_comm] using Real.add_one_le_exp epsilon
    _ = Real.exp ((m : ℝ) * epsilon) := by
      rw [← Real.exp_nat_mul]

/-- Exact scalar bridge from the literal boundary-stopped radial error to
the exponential budget reserved by the pair-moment certificate. -/
lemma literalBoundary_harnack_power_le_exp
    {R rho m : ℕ} {lower H : ℝ}
    (hlower : 0 < lower)
    (hbudget : (m : ℝ) *
        BoundaryStoppedHarnack.literalBoundaryHitError R rho lower ≤ H) :
    (1 + BoundaryStoppedHarnack.literalBoundaryHitError R rho lower) ^ m ≤
      Real.exp H := by
  have hepsilon0 : 0 ≤
      BoundaryStoppedHarnack.literalBoundaryHitError R rho lower := by
    unfold BoundaryStoppedHarnack.literalBoundaryHitError
    exact div_nonneg
      (add_nonneg
        (mul_nonneg (by norm_num)
          (BoundaryStoppedHarnack.literalBoundaryError_nonneg R))
        (euclideanShellError_nonneg rho)) hlower.le
  exact (pow_one_add_le_exp_nat_mul hepsilon0 m).trans
    (Real.exp_le_exp.mpr hbudget)

/-- Scale-certificate specialization of
`literalBoundary_harnack_power_le_exp`. -/
lemma literalBoundary_harnack_power_le_scaleCost
    {delta : ℝ} {n R rho m : ℕ} {lower : ℝ}
    (hlower : 0 < lower)
    (hbudget : (m : ℝ) *
        BoundaryStoppedHarnack.literalBoundaryHitError R rho lower ≤
      scaleCost delta n / 64) :
    (1 + BoundaryStoppedHarnack.literalBoundaryHitError R rho lower) ^ m ≤
      Real.exp (scaleCost delta n / 64) :=
  literalBoundary_harnack_power_le_exp hlower hbudget

/-- A history-dependent Condition `(star)` comparison, applied one stopped
coordinate at a time, gives the required far-pair upper bound.  No product
law for a coarse fixed-horizon fibre is assumed: `actualKernel` is arbitrary,
and only its one-sided sequential domination on the complete stopped datum
is used.  The weight carries all duration and profile conditioning that is
unchanged by the entrance-point Harnack comparison. -/
theorem stoppedFarPair_le_of_sequential_conditionStar
    {blockLength q : ℕ} {profileDelta thickDelta : ℝ}
    {i : ℕ} {x y : Point}
    {Data Entrance : Type*} [MeasurableSpace Data] [Fintype Entrance] {m : ℕ}
    (dataLaw : Measure Data) [IsProbabilityMeasure dataLaw]
    {ε harnackFactor pointUpper : ℝ}
    (kernel : Fin m → Data → Entrance → ℝ)
    (entranceData referenceData : Data → Fin m → Entrance)
    (weight actualKernel : Data → ℝ)
    (hkernel0 : ∀ j d u, 0 ≤ kernel j d u)
    (hweight0 : ∀ d, 0 ≤ weight d)
    (hstar : ∀ j d, AppendixDecoupling.ConditionStar ε (kernel j d))
    (hactualIntegrable : Integrable actualKernel dataLaw)
    (hmodelIntegrable : Integrable
      (fun d ↦ weight d * sequentialProductKernel kernel entranceData d) dataLaw)
    (hrefIntegrable : Integrable
      (fun d ↦ weight d * sequentialProductKernel kernel referenceData d) dataLaw)
    (hε0 : 0 ≤ ε)
    (_hε : ε ≤ 1)
    (hharnack0 : 0 ≤ harnackFactor)
    (hharnack : (1 + ε) ^ m ≤ harnackFactor)
    {prefixScale : ℕ}
    (href : (∫ d, weight d *
        sequentialProductKernel kernel referenceData d ∂dataLaw) ≤
      pointUpper ^ 2 / prefixProfileLower prefixScale)
    (hsequential : SequentialStoppedKernelUpper
      entranceData kernel weight actualKernel)
    (hdisintegrate : StoppedPairDataDisintegrationUpper fairSteps
      (stoppedThickPointEvent (i * blockLength)
          q profileDelta thickDelta x ∩
        stoppedThickPointEvent (i * blockLength)
          q profileDelta thickDelta y)
      dataLaw actualKernel) :
    fairSteps.real
        (stoppedThickPointEvent (i * blockLength)
            q profileDelta thickDelta x ∩
          stoppedThickPointEvent (i * blockLength)
            q profileDelta thickDelta y) ≤
      harnackFactor *
        (pointUpper ^ 2 / prefixProfileLower prefixScale) := by
  have hfac0 : 0 ≤ 1 + ε := by linarith
  have hproduct (d : Data) :
      sequentialProductKernel kernel entranceData d ≤
        (1 + ε) ^ m * sequentialProductKernel kernel referenceData d := by
    unfold sequentialProductKernel
    calc
      ∏ j, kernel j d (entranceData d j) ≤
          ∏ j, (1 + ε) * kernel j d (referenceData d j) :=
        Finset.prod_le_prod
          (fun j _ ↦ hkernel0 j d (entranceData d j))
          (fun j _ ↦ (hstar j d (referenceData d j) (entranceData d j)).2)
      _ = (1 + ε) ^ m * ∏ j, kernel j d (referenceData d j) := by
        rw [Finset.prod_mul_distrib]
        simp
  have hmodelPoint (d : Data) :
      weight d * sequentialProductKernel kernel entranceData d ≤
        (1 + ε) ^ m *
          (weight d * sequentialProductKernel kernel referenceData d) := by
    calc
      weight d * sequentialProductKernel kernel entranceData d ≤
          weight d * ((1 + ε) ^ m *
            sequentialProductKernel kernel referenceData d) :=
        mul_le_mul_of_nonneg_left (hproduct d) (hweight0 d)
      _ = (1 + ε) ^ m *
          (weight d * sequentialProductKernel kernel referenceData d) := by ring
  have hrefPoint0 (d : Data) :
      0 ≤ weight d * sequentialProductKernel kernel referenceData d :=
    mul_nonneg (hweight0 d)
      (AppendixDecoupling.productKernel_nonneg
        (fun j u ↦ hkernel0 j d u) (referenceData d))
  have hfirst := integral_mono hactualIntegrable hmodelIntegrable hsequential
  have hsecond := integral_mono hmodelIntegrable
    (hrefIntegrable.const_mul ((1 + ε) ^ m)) hmodelPoint
  have hrefIntegral0 : 0 ≤ ∫ d, weight d *
      sequentialProductKernel kernel referenceData d ∂dataLaw :=
    integral_nonneg hrefPoint0
  calc
    fairSteps.real
        (stoppedThickPointEvent (i * blockLength)
            q profileDelta thickDelta x ∩
          stoppedThickPointEvent (i * blockLength)
            q profileDelta thickDelta y) ≤
        ∫ d, actualKernel d ∂dataLaw := hdisintegrate
    _ ≤ ∫ d, weight d *
        sequentialProductKernel kernel entranceData d ∂dataLaw := hfirst
    _ ≤ (1 + ε) ^ m * (∫ d, weight d *
        sequentialProductKernel kernel referenceData d ∂dataLaw) := by
      simpa only [integral_const_mul] using hsecond
    _ ≤ harnackFactor * (∫ d, weight d *
        sequentialProductKernel kernel referenceData d ∂dataLaw) :=
      mul_le_mul_of_nonneg_right hharnack hrefIntegral0
    _ ≤ harnackFactor *
        (pointUpper ^ 2 / prefixProfileLower prefixScale) :=
      mul_le_mul_of_nonneg_left href hharnack0

/-- Radial-potential specialization of
`stoppedFarPair_le_of_sequential_conditionStar`.  Geometry and the one-hit
Harnack estimate are discharged pointwise for every sequential history.
The remaining probabilistic premises are precisely the one-sided full-data
factorization/disintegration and the reference-profile integral bound. -/
theorem stoppedFarPair_le_of_euclideanShell_sequential
    {blockLength scale : ℕ} {profileDelta thickDelta : ℝ}
    {i : ℕ} {x y : Point}
    {Data Entrance : Type*} [MeasurableSpace Data] [Fintype Entrance] {m : ℕ}
    (dataLaw : Measure Data) [IsProbabilityMeasure dataLaw]
    (R rho : ℕ) {lower harnackFactor pointUpper : ℝ}
    (boundaryReference : Point)
    (entrancePoint : Fin m → Data → Entrance → Point)
    (entranceData referenceData : Data → Fin m → Entrance)
    (weight actualKernel : Data → ℝ)
    (hR : 4 ≤ R)
    (hq : boundaryReference ∈ Annulus.outerBoundary (Annulus.closedDisc R))
    (hinside : ∀ j d u, entrancePoint j d u ∈ Annulus.closedDisc R)
    (hrho : 4 ≤ rho)
    (hradius : ∀ j d u, (rho : ℝ) ≤
      PotentialEuclideanGeometry.euclideanRadius (entrancePoint j d u))
    (hgap : ∀ j d u v,
      |PotentialEuclideanGeometry.euclideanRadius (entrancePoint j d u) -
        PotentialEuclideanGeometry.euclideanRadius (entrancePoint j d v)| ≤ 1)
    (hlower : 0 < lower)
    (hlowerReference : ∀ j d u, lower ≤
      PotentialConvergence.planarPotentialKernel boundaryReference -
        PotentialConvergence.planarPotentialKernel (entrancePoint j d u) -
        euclideanShellError R)
    (hweight0 : ∀ d, 0 ≤ weight d)
    (hactualIntegrable : Integrable actualKernel dataLaw)
    (hmodelIntegrable : Integrable
      (fun d ↦ weight d * sequentialProductKernel
        (fun j d ↦ closedDiscHitKernel R (entrancePoint j d)) entranceData d)
      dataLaw)
    (hrefIntegrable : Integrable
      (fun d ↦ weight d * sequentialProductKernel
        (fun j d ↦ closedDiscHitKernel R (entrancePoint j d)) referenceData d)
      dataLaw)
    (hharnack0 : 0 ≤ harnackFactor)
    (hharnack : (1 + euclideanHitError R rho lower) ^ m ≤ harnackFactor)
    {prefixScale : ℕ}
    (href : (∫ d, weight d * sequentialProductKernel
        (fun j d ↦ closedDiscHitKernel R (entrancePoint j d)) referenceData d
          ∂dataLaw) ≤
      pointUpper ^ 2 / prefixProfileLower prefixScale)
    (hsequential : SequentialStoppedKernelUpper entranceData
      (fun j d ↦ closedDiscHitKernel R (entrancePoint j d)) weight actualKernel)
    (hdisintegrate : StoppedPairDataDisintegrationUpper fairSteps
      (stoppedThickPointEvent (i * blockLength)
          scale profileDelta thickDelta x ∩
        stoppedThickPointEvent (i * blockLength)
          scale profileDelta thickDelta y)
      dataLaw actualKernel)
    (hepsilon : euclideanHitError R rho lower ≤ 1) :
    fairSteps.real
        (stoppedThickPointEvent (i * blockLength)
            scale profileDelta thickDelta x ∩
          stoppedThickPointEvent (i * blockLength)
            scale profileDelta thickDelta y) ≤
      harnackFactor *
        (pointUpper ^ 2 / prefixProfileLower prefixScale) := by
  refine stoppedFarPair_le_of_sequential_conditionStar
    (dataLaw := dataLaw) (ε := euclideanHitError R rho lower)
    (kernel := fun j d ↦ closedDiscHitKernel R (entrancePoint j d))
    (entranceData := entranceData) (referenceData := referenceData)
    (weight := weight) (actualKernel := actualKernel)
    (hkernel0 := fun _ _ _ ↦ ENNReal.toReal_nonneg)
    (hweight0 := hweight0)
    (hstar := fun j d ↦
      conditionStar_closedDiscHitKernel_of_euclideanShells
        R rho boundaryReference (entrancePoint j d) hR hq
        (hinside j d) hrho (hradius j d) (hgap j d)
        hlower (hlowerReference j d))
    (hactualIntegrable := hactualIntegrable)
    (hmodelIntegrable := hmodelIntegrable)
    (hrefIntegrable := hrefIntegrable)
    (hε0 := by
      unfold euclideanHitError
      exact div_nonneg
        (add_nonneg (mul_nonneg (by norm_num) (euclideanShellError_nonneg R))
          (euclideanShellError_nonneg rho)) hlower.le)
    (_hε := hepsilon) (hharnack0 := hharnack0) (hharnack := hharnack)
    (href := href) (hsequential := hsequential)
    (hdisintegrate := hdisintegrate)

/-- Literal vertex-boundary version of the sequential far-pair comparison.
Unlike the closed-disc wrapper above, every local factor stops on the next
visit to `discBoundary center R`, exactly as the terminal excursion segments
in the stopped thick-point event do. -/
theorem stoppedFarPair_le_of_literalBoundary_sequential
    {blockLength scale : ℕ} {profileDelta thickDelta : ℝ}
    {i : ℕ} {x y : Point}
    {Data Entrance : Type*} [MeasurableSpace Data] [Fintype Entrance] {m : ℕ}
    (dataLaw : Measure Data) [IsProbabilityMeasure dataLaw]
    (R rho : ℕ) {lower harnackFactor pointUpper : ℝ}
    (center boundaryReference : Fin m → Data → Point)
    (entrancePoint : Fin m → Data → Entrance → Point)
    (entranceData referenceData : Data → Fin m → Entrance)
    (weight actualKernel : Data → ℝ)
    (hR : 5 ≤ R) (hseparated : rho + 2 ≤ R)
    (hq : ∀ j d, boundaryReference j d ∈
      ThickPoint.discBoundary (center j d) (R : ℝ))
    (hentrance : ∀ j d u, entrancePoint j d u ∈
      ThickPoint.discBoundary (center j d) ((rho : ℝ) + 1))
    (hrho : 4 ≤ rho) (hlower : 0 < lower)
    (hrefPotential : ∀ j d u, lower ≤
      PotentialConvergence.planarPotentialKernel
          (boundaryReference j d - center j d) -
        PotentialConvergence.planarPotentialKernel
          (entrancePoint j d u - center j d) -
        BoundaryStoppedHarnack.literalBoundaryError R)
    (hweight0 : ∀ d, 0 ≤ weight d)
    (hactualIntegrable : Integrable actualKernel dataLaw)
    (hmodelIntegrable : Integrable
      (fun d ↦ weight d * sequentialProductKernel
        (fun j d ↦ BoundaryStoppedHarnack.centeredBoundaryStoppedHitKernel
          R (center j d) (entrancePoint j d)) entranceData d) dataLaw)
    (hrefIntegrable : Integrable
      (fun d ↦ weight d * sequentialProductKernel
        (fun j d ↦ BoundaryStoppedHarnack.centeredBoundaryStoppedHitKernel
          R (center j d) (entrancePoint j d)) referenceData d) dataLaw)
    (hharnack0 : 0 ≤ harnackFactor)
    (hharnack : (1 + BoundaryStoppedHarnack.literalBoundaryHitError
      R rho lower) ^ m ≤ harnackFactor)
    {prefixScale : ℕ}
    (href : (∫ d, weight d * sequentialProductKernel
        (fun j d ↦ BoundaryStoppedHarnack.centeredBoundaryStoppedHitKernel
          R (center j d) (entrancePoint j d)) referenceData d ∂dataLaw) ≤
      pointUpper ^ 2 / prefixProfileLower prefixScale)
    (hsequential : SequentialStoppedKernelUpper entranceData
      (fun j d ↦ BoundaryStoppedHarnack.centeredBoundaryStoppedHitKernel
        R (center j d) (entrancePoint j d)) weight actualKernel)
    (hdisintegrate : StoppedPairDataDisintegrationUpper fairSteps
      (stoppedThickPointEvent (i * blockLength)
          scale profileDelta thickDelta x ∩
        stoppedThickPointEvent (i * blockLength)
          scale profileDelta thickDelta y)
      dataLaw actualKernel)
    (hepsilon : BoundaryStoppedHarnack.literalBoundaryHitError
      R rho lower ≤ 1) :
    fairSteps.real
        (stoppedThickPointEvent (i * blockLength)
            scale profileDelta thickDelta x ∩
          stoppedThickPointEvent (i * blockLength)
            scale profileDelta thickDelta y) ≤
      harnackFactor *
        (pointUpper ^ 2 / prefixProfileLower prefixScale) := by
  refine stoppedFarPair_le_of_sequential_conditionStar
    (dataLaw := dataLaw)
    (ε := BoundaryStoppedHarnack.literalBoundaryHitError R rho lower)
    (kernel := fun j d ↦
      BoundaryStoppedHarnack.centeredBoundaryStoppedHitKernel
        R (center j d) (entrancePoint j d))
    (entranceData := entranceData) (referenceData := referenceData)
    (weight := weight) (actualKernel := actualKernel)
    (hkernel0 := fun _ _ _ ↦ ENNReal.toReal_nonneg)
    (hweight0 := hweight0)
    (hstar := fun j d ↦
      BoundaryStoppedHarnack.conditionStar_centeredTerminalBoundaryStoppedHitKernel
        R rho (center j d) (boundaryReference j d) (entrancePoint j d)
        hR hseparated (hq j d) (hentrance j d) hrho hlower
        (hrefPotential j d))
    (hactualIntegrable := hactualIntegrable)
    (hmodelIntegrable := hmodelIntegrable)
    (hrefIntegrable := hrefIntegrable)
    (hε0 := by
      unfold BoundaryStoppedHarnack.literalBoundaryHitError
      exact div_nonneg
        (add_nonneg
          (mul_nonneg (by norm_num)
            (BoundaryStoppedHarnack.literalBoundaryError_nonneg R))
          (euclideanShellError_nonneg rho)) hlower.le)
    (_hε := hepsilon) (hharnack0 := hharnack0) (hharnack := hharnack)
    (href := href) (hsequential := hsequential)
    (hdisintegrate := hdisintegrate)

/-- **Concrete A.5 plus A.6 pair reduction.**  Far separation levels retain
their explicit prefix probability and count.  All levels above
`q - ceil(3 log q)` are counted once by the cutoff overlap area, which is the
source of HLOZ's `q^24 * M * Q_q` term. -/
theorem pairMoment_le_farPrefixSum_add_nearArea
    {blockCount blockLength q : ℕ} {profileDelta thickDelta : ℝ}
    {pointUpper harnackFactor : ℝ}
    (hcutoff : decorrelationCutoff q ∈ scaleIndices q)
    (hAnnular : AnnularFarNearPairComparison blockCount blockLength q
      profileDelta thickDelta pointUpper harnackFactor) :
    ∀ i : Fin blockCount,
      (∑ x ∈ ThickPoint.candidateBox q,
        ∑ y ∈ ThickPoint.candidateBox q,
          fairSteps.real
            (stoppedThickPointEvent ((i : ℕ) * blockLength)
                q profileDelta thickDelta x ∩
              stoppedThickPointEvent ((i : ℕ) * blockLength)
                q profileDelta thickDelta y)) ≤
        (∑ l ∈ Finset.Icc 1 (decorrelationCutoff q),
          (levelPairCountBound (ThickPoint.candidateBox q) q l : ℝ) *
            (harnackFactor *
              (pointUpper ^ 2 /
                prefixProfileLower (pairPrefixScale q l)))) +
        ((ThickPoint.candidateBox q).card : ℝ) *
          ((2 * ⌈2 * ThickPoint.scaleRadius q (decorrelationCutoff q)⌉₊ + 1) ^ 2 :
            ℕ) * pointUpper := by
  intro i
  apply pairSum_le_farEnvelope_add_nearArea
    (U := ThickPoint.candidateBox q) (n := q)
    (k := decorrelationCutoff q)
    (w := fun x y => fairSteps.real
      (stoppedThickPointEvent ((i : ℕ) * blockLength)
          q profileDelta thickDelta x ∩
        stoppedThickPointEvent ((i : ℕ) * blockLength)
          q profileDelta thickDelta y))
    (B := fun l => harnackFactor *
      (pointUpper ^ 2 / prefixProfileLower (pairPrefixScale q l)))
    (Q := pointUpper) hcutoff
  · intro l hl
    exact mul_nonneg hAnnular.harnackFactor_nonneg
      (div_nonneg (sq_nonneg _) (prefixProfileLower_nonneg _))
  · exact hAnnular.pointUpper_nonneg
  · intro x hx y hy hlevel
    exact hAnnular.farPair_le i x hx y hy hlevel
  · intro x hx y hy
    exact (measureReal_mono (inter_subset_left :
      stoppedThickPointEvent ((i : ℕ) * blockLength)
          q profileDelta thickDelta x ∩
        stoppedThickPointEvent ((i : ℕ) * blockLength)
          q profileDelta thickDelta y ⊆
      stoppedThickPointEvent ((i : ℕ) * blockLength)
          q profileDelta thickDelta x)).trans
      (hAnnular.onePoint_le i x hx)

/-- Exact `ScaleCertificate.pairMoment` endpoint after the only remaining
finite arithmetic comparison has put the explicit A.5/A.6 envelope below
the chosen diagonal-inclusive `pairUpper`. -/
theorem scaleCertificate_pairMoment_of_farNearComparison
    {blockCount blockLength q : ℕ} {profileDelta thickDelta : ℝ}
    {pointUpper harnackFactor pairUpper : ℝ}
    (hcutoff : decorrelationCutoff q ∈ scaleIndices q)
    (hAnnular : AnnularFarNearPairComparison blockCount blockLength q
      profileDelta thickDelta pointUpper harnackFactor)
    (hfinite :
      (∑ l ∈ Finset.Icc 1 (decorrelationCutoff q),
        (levelPairCountBound (ThickPoint.candidateBox q) q l : ℝ) *
          (harnackFactor *
            (pointUpper ^ 2 /
              prefixProfileLower (pairPrefixScale q l)))) +
      ((ThickPoint.candidateBox q).card : ℝ) *
        ((2 * ⌈2 * ThickPoint.scaleRadius q (decorrelationCutoff q)⌉₊ + 1) ^ 2 :
          ℕ) * pointUpper ≤ pairUpper) :
    ∀ i : Fin blockCount,
      (∑ x ∈ ThickPoint.candidateBox q,
        ∑ y ∈ ThickPoint.candidateBox q,
          fairSteps.real
            (stoppedThickPointEvent ((i : ℕ) * blockLength)
                q profileDelta thickDelta x ∩
              stoppedThickPointEvent ((i : ℕ) * blockLength)
                q profileDelta thickDelta y)) ≤ pairUpper := by
  intro i
  exact (pairMoment_le_farPrefixSum_add_nearArea hcutoff hAnnular i).trans hfinite

/-! ## Specialization to the corrected Proposition 1.3 scale -/

/-- The exact close-band lattice area fits the `256 (q+1)^24` term in the
corrected scale certificate. -/
lemma nearArea_le_diagonalPairBound
    {delta : ℝ} {n : ℕ} {pointUpper : ℝ}
    (hpoint0 : 0 ≤ pointUpper)
    (hpoint : pointUpper ≤ pointUpperBound delta n)
    (hR : ThickPoint.scaleRadius (scaleIndex delta n)
        (decorrelationCutoff (scaleIndex delta n)) ≤
      3 * (scaleIndex delta n + 1 : ℝ) ^ (12 : ℕ)) :
    ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) *
        ((2 * ⌈2 * ThickPoint.scaleRadius (scaleIndex delta n)
          (decorrelationCutoff (scaleIndex delta n))⌉₊ + 1) ^ 2 : ℕ) *
        pointUpper ≤ diagonalPairBound delta n := by
  have harea := latticeArea_le_256_mul_pow24 hR
  have hareaReal :
      ((((2 * ⌈2 * ThickPoint.scaleRadius (scaleIndex delta n)
          (decorrelationCutoff (scaleIndex delta n))⌉₊ + 1) ^ 2 : ℕ)) : ℝ) ≤
        256 * ((scaleIndex delta n + 1 : ℕ) : ℝ) ^ (24 : ℕ) := by
    exact_mod_cast harea
  push_cast at hareaReal
  unfold diagonalPairBound
  push_cast
  have hM0 : (0 : ℝ) ≤
      (ThickPoint.candidateBox (scaleIndex delta n)).card :=
    Nat.cast_nonneg _
  calc
    ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) *
          (2 * (⌈2 * ThickPoint.scaleRadius (scaleIndex delta n)
            (decorrelationCutoff (scaleIndex delta n))⌉₊ : ℝ) + 1) ^ 2 *
          pointUpper ≤
        ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) *
          (256 * (scaleIndex delta n + 1 : ℝ) ^ (24 : ℕ)) * pointUpper := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hareaReal hM0) hpoint0
    _ = 256 * (scaleIndex delta n + 1 : ℝ) ^ (24 : ℕ) *
          ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) *
          pointUpper := by ring
    _ ≤ 256 * (scaleIndex delta n + 1 : ℝ) ^ (24 : ℕ) *
          ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) *
          pointUpperBound delta n := by
      have hq0 : (0 : ℝ) ≤ scaleIndex delta n + 1 := by
        have hq : (0 : ℝ) ≤ (scaleIndex delta n : ℝ) := Nat.cast_nonneg _
        linarith
      have hfactor0 : 0 ≤
          256 * (scaleIndex delta n + 1 : ℝ) ^ (24 : ℕ) *
            ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) :=
        mul_nonneg
          (mul_nonneg (by norm_num) (pow_nonneg hq0 _))
          (Nat.cast_nonneg _)
      exact mul_le_mul_of_nonneg_left hpoint
        hfactor0

/-- Exact corrected `AnnularComparisons.pairMoment` field.  There is no
assumed summed second moment: the remaining far input is levelwise, and the
finite sum contributes precisely the `(q+1)` multiplier in
`offDiagonalPairBound`. -/
theorem annularComparisons_pairMoment_of_farNearComparison
    {delta : ℝ} {n : ℕ} {pointUpper harnackFactor : ℝ}
    (hcutoff : decorrelationCutoff (scaleIndex delta n) ∈
      scaleIndices (scaleIndex delta n))
    (hAnnular : AnnularFarNearPairComparison
      (chosenBlockCount delta n) (chosenBlockLength delta n)
      (scaleIndex delta n) chosenProfileDelta (chosenThickDelta delta)
      pointUpper harnackFactor)
    (hpoint : pointUpper ≤ pointUpperBound delta n)
    (hR : ThickPoint.scaleRadius (scaleIndex delta n)
        (decorrelationCutoff (scaleIndex delta n)) ≤
      3 * (scaleIndex delta n + 1 : ℝ) ^ (12 : ℕ))
    (hfarLevel : ∀ l ∈ Finset.Icc 1
        (decorrelationCutoff (scaleIndex delta n)),
      (levelPairCountBound
          (ThickPoint.candidateBox (scaleIndex delta n))
          (scaleIndex delta n) l : ℝ) *
        (harnackFactor *
          (pointUpper ^ 2 /
            prefixProfileLower
              (pairPrefixScale (scaleIndex delta n) l))) ≤
      256 *
        ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) ^ 2 *
        Real.exp (-4 * (scaleIndex delta n : ℝ) + scaleCost delta n / 4)) :
    ∀ i : Fin (chosenBlockCount delta n),
      (∑ x ∈ ThickPoint.candidateBox (scaleIndex delta n),
        ∑ y ∈ ThickPoint.candidateBox (scaleIndex delta n),
          fairSteps.real
            (stoppedThickPointEvent
                ((i : ℕ) * chosenBlockLength delta n)
                (scaleIndex delta n) chosenProfileDelta
                (chosenThickDelta delta) x ∩
              stoppedThickPointEvent
                ((i : ℕ) * chosenBlockLength delta n)
                (scaleIndex delta n) chosenProfileDelta
                (chosenThickDelta delta) y)) ≤ pairMomentBound delta n := by
  intro i
  have hraw := pairMoment_le_farPrefixSum_add_nearArea hcutoff hAnnular i
  let farBase : ℝ :=
    256 * ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) ^ 2 *
      Real.exp (-4 * (scaleIndex delta n : ℝ) + scaleCost delta n / 4)
  have hfarBase0 : 0 ≤ farBase := by dsimp [farBase]; positivity
  have hfar :
      (∑ l ∈ Finset.Icc 1 (decorrelationCutoff (scaleIndex delta n)),
        (levelPairCountBound
            (ThickPoint.candidateBox (scaleIndex delta n))
            (scaleIndex delta n) l : ℝ) *
          (harnackFactor *
            (pointUpper ^ 2 /
              prefixProfileLower
                (pairPrefixScale (scaleIndex delta n) l)))) ≤
        offDiagonalPairBound delta n := by
    calc
      _ ≤ ∑ _l ∈ Finset.Icc 1 (decorrelationCutoff (scaleIndex delta n)),
          farBase := by
        apply Finset.sum_le_sum
        intro l hl
        exact hfarLevel l hl
      _ = ((Finset.Icc 1
          (decorrelationCutoff (scaleIndex delta n))).card : ℝ) * farBase := by
        simp
      _ ≤ (scaleIndex delta n + 1 : ℝ) * farBase := by
        apply mul_le_mul_of_nonneg_right _ hfarBase0
        have hcardNat :
            (Finset.Icc 1
              (decorrelationCutoff (scaleIndex delta n))).card ≤
              scaleIndex delta n + 1 := by
          unfold decorrelationCutoff
          rw [Nat.card_Icc]
          omega
        exact_mod_cast hcardNat
      _ = offDiagonalPairBound delta n := by
        unfold offDiagonalPairBound
        dsimp [farBase]
        push_cast
        ring
  have hnear := nearArea_le_diagonalPairBound hAnnular.pointUpper_nonneg hpoint hR
  calc
    _ ≤ (∑ l ∈ Finset.Icc 1 (decorrelationCutoff (scaleIndex delta n)),
        (levelPairCountBound
            (ThickPoint.candidateBox (scaleIndex delta n))
            (scaleIndex delta n) l : ℝ) *
          (harnackFactor *
            (pointUpper ^ 2 /
              prefixProfileLower
                (pairPrefixScale (scaleIndex delta n) l)))) +
        ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) *
          ((2 * ⌈2 * ThickPoint.scaleRadius (scaleIndex delta n)
            (decorrelationCutoff (scaleIndex delta n))⌉₊ + 1) ^ 2 : ℕ) *
          pointUpper := hraw
    _ ≤ offDiagonalPairBound delta n + diagonalPairBound delta n :=
      add_le_add hfar hnear
    _ = pairMomentBound delta n := by
      unfold pairMomentBound
      ring

/-- Exact corrected `AnnularComparisons.pairMoment` endpoint with the
one-point upper envelope supplied by the complete constrained-profile
A.11/A.12 upper bound.  Thus the only levelwise analytic input left in this
form is the genuine far-pair sequential comparison. -/
theorem annularComparisons_pairMoment_of_profileWeightComparison
    {delta : ℝ} {n : ℕ} {harnackFactor : ℝ}
    (hq : ProfileWeightUpper.profileUpperTailStart ≤ scaleIndex delta n)
    (hcost : ProfileWeightUpper.profileUpperConstant *
        (scaleIndex delta n : ℝ) ^ (3 / 5 : ℝ) ≤ scaleCost delta n / 4)
    (hcutoff : decorrelationCutoff (scaleIndex delta n) ∈
      scaleIndices (scaleIndex delta n))
    (hAnnular : AnnularFarNearPairComparison
      (chosenBlockCount delta n) (chosenBlockLength delta n)
      (scaleIndex delta n) chosenProfileDelta (chosenThickDelta delta)
      (constrainedProfileWeight (scaleIndex delta n) chosenProfileDelta)
      harnackFactor)
    (hR : ThickPoint.scaleRadius (scaleIndex delta n)
        (decorrelationCutoff (scaleIndex delta n)) ≤
      3 * (scaleIndex delta n + 1 : ℝ) ^ (12 : ℕ))
    (hfarLevel : ∀ l ∈ Finset.Icc 1
        (decorrelationCutoff (scaleIndex delta n)),
      (levelPairCountBound
          (ThickPoint.candidateBox (scaleIndex delta n))
          (scaleIndex delta n) l : ℝ) *
        (harnackFactor *
          ((constrainedProfileWeight
              (scaleIndex delta n) chosenProfileDelta) ^ 2 /
            prefixProfileLower
              (pairPrefixScale (scaleIndex delta n) l))) ≤
      256 *
        ((ThickPoint.candidateBox (scaleIndex delta n)).card : ℝ) ^ 2 *
        Real.exp (-4 * (scaleIndex delta n : ℝ) + scaleCost delta n / 4)) :
    ∀ i : Fin (chosenBlockCount delta n),
      (∑ x ∈ ThickPoint.candidateBox (scaleIndex delta n),
        ∑ y ∈ ThickPoint.candidateBox (scaleIndex delta n),
          fairSteps.real
            (stoppedThickPointEvent
                ((i : ℕ) * chosenBlockLength delta n)
                (scaleIndex delta n) chosenProfileDelta
                (chosenThickDelta delta) x ∩
              stoppedThickPointEvent
                ((i : ℕ) * chosenBlockLength delta n)
                (scaleIndex delta n) chosenProfileDelta
                (chosenThickDelta delta) y)) ≤ pairMomentBound delta n := by
  exact annularComparisons_pairMoment_of_farNearComparison
    hcutoff hAnnular
    (constrainedProfileWeight_le_pointUpperBound hq hcost) hR hfarLevel

/-- **Concrete Proposition-A.3(2) pair assembly.**  The complete profile
upper, fixed-prefix A.11/A.12 lower, exact separation-level lattice count,
near-band area, and corrected diagonal-inclusive scale bound are all
combined here.  No summed moment or level-envelope inequality is assumed.

The remaining walk input is `hAnnular`; its far field can be constructed by
`stoppedFarPair_le_of_euclideanShell_sequential`.  The scalar `H` is the
accumulated sequential Harnack exponent. -/
theorem annularComparisons_pairMoment_of_explicitAnalyticBudgets
    {delta : ℝ} {n : ℕ} {harnackFactor A B H : ℝ}
    (hqOne : 1 ≤ scaleIndex delta n)
    (hqTail : ProfileWeightUpper.profileUpperTailStart ≤ scaleIndex delta n)
    (hcutoff : decorrelationCutoff (scaleIndex delta n) ∈
      scaleIndices (scaleIndex delta n))
    (hAnnular : AnnularFarNearPairComparison
      (chosenBlockCount delta n) (chosenBlockLength delta n)
      (scaleIndex delta n) chosenProfileDelta (chosenThickDelta delta)
      (constrainedProfileWeight (scaleIndex delta n) chosenProfileDelta)
      harnackFactor)
    (hR : ThickPoint.scaleRadius (scaleIndex delta n)
        (decorrelationCutoff (scaleIndex delta n)) ≤
      3 * (scaleIndex delta n + 1 : ℝ) ^ (12 : ℕ))
    (hA0 : 0 ≤ A) (hB0 : 0 ≤ B) (hH0 : 0 ≤ H)
    (hprofileBudget : ProfileWeightUpper.profileUpperConstant *
        (scaleIndex delta n : ℝ) ^ (3 / 5 : ℝ) ≤ A)
    (hprefixBudget : geometricProfileCostCoefficient geometricCutoff *
        (scaleIndex delta n : ℝ) ^ (3 / 5 : ℝ) ≤ B)
    (hharnack : harnackFactor ≤ Real.exp H)
    (hprefixCutoff : ∀ l ∈ Finset.Icc 1
        (decorrelationCutoff (scaleIndex delta n)),
      geometricCutoff ≤ pairPrefixScale (scaleIndex delta n) l)
    (hbudget : 2 * A + B + H + 2 +
        2 * (decorrelationPadding (scaleIndex delta n) : ℝ) ≤
      scaleCost delta n / 4) :
    ∀ i : Fin (chosenBlockCount delta n),
      (∑ x ∈ ThickPoint.candidateBox (scaleIndex delta n),
        ∑ y ∈ ThickPoint.candidateBox (scaleIndex delta n),
          fairSteps.real
            (stoppedThickPointEvent
                ((i : ℕ) * chosenBlockLength delta n)
                (scaleIndex delta n) chosenProfileDelta
                (chosenThickDelta delta) x ∩
              stoppedThickPointEvent
                ((i : ℕ) * chosenBlockLength delta n)
                (scaleIndex delta n) chosenProfileDelta
                (chosenThickDelta delta) y)) ≤ pairMomentBound delta n := by
  let q := scaleIndex delta n
  have hprofileRaw := ProfileWeightUpper.constrainedProfileWeight_le_exp hqTail
  have hprofile : constrainedProfileWeight q chosenProfileDelta ≤
      Real.exp (-2 * (q : ℝ) + A) := by
    have hraw : constrainedProfileWeight q chosenProfileDelta ≤
        Real.exp (-(2 * (q : ℝ)) +
          ProfileWeightUpper.profileUpperConstant *
            (q : ℝ) ^ (3 / 5 : ℝ)) := by
      simpa [q, ProfileWeightUpper.profileUpperDelta, chosenProfileDelta]
        using hprofileRaw
    exact hraw.trans (Real.exp_le_exp.mpr (by linarith))
  have hpointBound : constrainedProfileWeight q chosenProfileDelta ≤
      pointUpperBound delta n := by
    apply hprofile.trans
    unfold pointUpperBound
    apply Real.exp_le_exp.mpr
    dsimp only [q]
    have hAle : A ≤ scaleCost delta n / 4 := by linarith
    linarith
  apply annularComparisons_pairMoment_of_farNearComparison
    hcutoff hAnnular hpointBound hR
  intro l hl
  have hlIcc := Finset.mem_Icc.mp hl
  have hadd : l + decorrelationPadding q ≤ q := by
    have hle : l ≤ q - decorrelationPadding q := by
      simpa [q, decorrelationCutoff] using hlIcc.2
    omega
  have hlq : l ≤ q := hlIcc.2.trans (Nat.sub_le _ _)
  have hprefixCost : prefixProfileCost (pairPrefixScale q l) ≤ B :=
    prefixProfileCost_pairPrefixScale_le_of_budget
      (by simpa [q] using hprefixCutoff l hl) hprefixBudget
  exact farLevelTerm_le_of_analyticBudgets hqOne hlIcc.1 hlq hadd
    (by simpa [q] using hprefixCutoff l hl)
    (constrainedProfileWeight_nonneg _ _)
    hprofile hAnnular.harnackFactor_nonneg hharnack hprefixCost hbudget

/-- A fixed allocation of the corrected scale budget: two profile-upper
errors, one prefix-denominator error, and the accumulated radial Harnack loss
each receive `scaleCost/64`; the padding and the `l-1` radius shift receive
the remaining `3 scaleCost/16`. -/
theorem annularComparisons_pairMoment_of_sixtyFourthBudgets
    {delta : ℝ} {n : ℕ} {harnackFactor : ℝ}
    (hqOne : 1 ≤ scaleIndex delta n)
    (hqTail : ProfileWeightUpper.profileUpperTailStart ≤ scaleIndex delta n)
    (hcutoff : decorrelationCutoff (scaleIndex delta n) ∈
      scaleIndices (scaleIndex delta n))
    (hAnnular : AnnularFarNearPairComparison
      (chosenBlockCount delta n) (chosenBlockLength delta n)
      (scaleIndex delta n) chosenProfileDelta (chosenThickDelta delta)
      (constrainedProfileWeight (scaleIndex delta n) chosenProfileDelta)
      harnackFactor)
    (hR : ThickPoint.scaleRadius (scaleIndex delta n)
        (decorrelationCutoff (scaleIndex delta n)) ≤
      3 * (scaleIndex delta n + 1 : ℝ) ^ (12 : ℕ))
    (hprofileBudget : ProfileWeightUpper.profileUpperConstant *
        (scaleIndex delta n : ℝ) ^ (3 / 5 : ℝ) ≤ scaleCost delta n / 64)
    (hprefixBudget : geometricProfileCostCoefficient geometricCutoff *
        (scaleIndex delta n : ℝ) ^ (3 / 5 : ℝ) ≤ scaleCost delta n / 64)
    (hharnack : harnackFactor ≤ Real.exp (scaleCost delta n / 64))
    (hprefixCutoff : ∀ l ∈ Finset.Icc 1
        (decorrelationCutoff (scaleIndex delta n)),
      geometricCutoff ≤ pairPrefixScale (scaleIndex delta n) l)
    (hpadding : 2 +
        2 * (decorrelationPadding (scaleIndex delta n) : ℝ) ≤
      3 * scaleCost delta n / 16) :
    ∀ i : Fin (chosenBlockCount delta n),
      (∑ x ∈ ThickPoint.candidateBox (scaleIndex delta n),
        ∑ y ∈ ThickPoint.candidateBox (scaleIndex delta n),
          fairSteps.real
            (stoppedThickPointEvent
                ((i : ℕ) * chosenBlockLength delta n)
                (scaleIndex delta n) chosenProfileDelta
                (chosenThickDelta delta) x ∩
              stoppedThickPointEvent
                ((i : ℕ) * chosenBlockLength delta n)
                (scaleIndex delta n) chosenProfileDelta
                (chosenThickDelta delta) y)) ≤ pairMomentBound delta n := by
  have hcost0 : 0 ≤ scaleCost delta n := by
    unfold scaleCost
    positivity
  apply annularComparisons_pairMoment_of_explicitAnalyticBudgets
    hqOne hqTail hcutoff hAnnular hR
    (A := scaleCost delta n / 64)
    (B := scaleCost delta n / 64)
    (H := scaleCost delta n / 64)
  · positivity
  · positivity
  · positivity
  · exact hprofileBudget
  · exact hprefixBudget
  · exact hharnack
  · exact hprefixCutoff
  · nlinarith

/-- **Fully discharged scale arithmetic for the pair field.**  Eventually,
the profile upper, fixed-prefix lower, lattice separation counts, near-band
radius, and every logarithmic/polynomial budget are automatic.  The two
remaining arguments are exactly probabilistic: the literal one-point/far
pair comparison and its accumulated sequential Harnack factor. -/
theorem eventually_annularComparisons_pairMoment_of_farNearComparison
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop, ∀ harnackFactor : ℝ,
      AnnularFarNearPairComparison
          (chosenBlockCount delta n) (chosenBlockLength delta n)
          (scaleIndex delta n) chosenProfileDelta (chosenThickDelta delta)
          (constrainedProfileWeight (scaleIndex delta n) chosenProfileDelta)
          harnackFactor →
      harnackFactor ≤ Real.exp (scaleCost delta n / 64) →
      ∀ i : Fin (chosenBlockCount delta n),
        (∑ x ∈ ThickPoint.candidateBox (scaleIndex delta n),
          ∑ y ∈ ThickPoint.candidateBox (scaleIndex delta n),
            fairSteps.real
              (stoppedThickPointEvent
                  ((i : ℕ) * chosenBlockLength delta n)
                  (scaleIndex delta n) chosenProfileDelta
                  (chosenThickDelta delta) x ∩
                stoppedThickPointEvent
                  ((i : ℕ) * chosenBlockLength delta n)
                  (scaleIndex delta n) chosenProfileDelta
                  (chosenThickDelta delta) y)) ≤ pairMomentBound delta n := by
  have htail := (tendsto_scaleIndex_atTop delta).eventually
    (eventually_ge_atTop (ProfileWeightUpper.profileUpperTailStart : ℝ))
  filter_upwards
      [eventually_scaleIndex_pos delta, htail,
       eventually_decorrelationCutoff_mem_scaleIndices,
       eventually_cutoff_scaleRadius_le_three_mul_pow12,
       eventually_profileUpperCost_le_sixtyFourth_scaleCost hdelta,
       eventually_geometricPrefixCost_le_sixtyFourth_scaleCost hdelta,
       eventually_geometricCutoff_le_pairPrefixScale,
       eventually_decorrelationPadding_le_scaleCost_share hdelta]
      with n hqOne hqTail hcutoff hR hprofile hprefix hprefixCutoff hpadding
  intro harnackFactor hAnnular hharnack
  apply annularComparisons_pairMoment_of_sixtyFourthBudgets
    hqOne (by exact_mod_cast hqTail) hcutoff hAnnular hR hprofile hprefix
    hharnack hprefixCutoff hpadding

/-- Exact `ScaleCertificate.pairMoment` shape obtained from the local
annular comparison after a purely deterministic verification of the
displayed explicit finite separation sum.  The latter contains only HLOZ
radii, integer lattice counts, and the checked A.11/A.12 prefix quantity. -/
theorem scaleCertificate_pairMoment_of_annularPrefixComparison
    {blockCount blockLength q : ℕ} {profileDelta thickDelta : ℝ}
    {pointUpper harnackFactor pairUpper : ℝ}
    (hAnnular : AnnularPrefixPairComparison blockCount blockLength q
      profileDelta thickDelta pointUpper harnackFactor)
    (hfinite :
      (∑ l ∈ Finset.Icc 1 (q + 2),
        (levelPairCountBound (ThickPoint.candidateBox q) q l : ℝ) *
          (harnackFactor * prefixPairEnvelope q pointUpper l)) ≤ pairUpper) :
    ∀ i : Fin blockCount,
      (∑ x ∈ ThickPoint.candidateBox q,
        ∑ y ∈ ThickPoint.candidateBox q,
          fairSteps.real
            (stoppedThickPointEvent ((i : ℕ) * blockLength)
                q profileDelta thickDelta x ∩
              stoppedThickPointEvent ((i : ℕ) * blockLength)
                q profileDelta thickDelta y)) ≤ pairUpper := by
  intro i
  exact (pairMoment_le_explicitPrefixSeparationSum hAnnular i).trans hfinite

/-- Specialization to the exact pair field in
`Proposition13Scales.AnnularComparisons`. -/
theorem annularComparisons_pairMoment_of_prefixComparison
    {delta : ℝ} {n : ℕ} {pointUpper harnackFactor : ℝ}
    (hAnnular : AnnularPrefixPairComparison
      (chosenBlockCount delta n) (chosenBlockLength delta n)
      (scaleIndex delta n) chosenProfileDelta (chosenThickDelta delta)
      pointUpper harnackFactor)
    (hfinite :
      (∑ l ∈ Finset.Icc 1 (scaleIndex delta n + 2),
        (levelPairCountBound
            (ThickPoint.candidateBox (scaleIndex delta n))
            (scaleIndex delta n) l : ℝ) *
          (harnackFactor *
            prefixPairEnvelope (scaleIndex delta n) pointUpper l)) ≤
        pairMomentBound delta n) :
    ∀ i : Fin (chosenBlockCount delta n),
      (∑ x ∈ ThickPoint.candidateBox (scaleIndex delta n),
        ∑ y ∈ ThickPoint.candidateBox (scaleIndex delta n),
          fairSteps.real
            (stoppedThickPointEvent
                ((i : ℕ) * chosenBlockLength delta n)
                (scaleIndex delta n) chosenProfileDelta
                (chosenThickDelta delta) x ∩
              stoppedThickPointEvent
                ((i : ℕ) * chosenBlockLength delta n)
                (scaleIndex delta n) chosenProfileDelta
                (chosenThickDelta delta) y)) ≤
        pairMomentBound delta n :=
  scaleCertificate_pairMoment_of_annularPrefixComparison hAnnular hfinite

end

end Erdos1165.AppendixPairMoment
