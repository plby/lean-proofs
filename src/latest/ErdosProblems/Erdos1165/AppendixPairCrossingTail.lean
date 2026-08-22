/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.AppendixPairReferenceMass
import ErdosProblems.Erdos1165.ProfileConditionalTailUpper

/-!
# Crossing-count mixtures in the far-pair estimate

The conditioning in HLOZ (A.16)--(A.17) is on the single number of
crossings of the separation annulus.  It is not conditioning on a complete
profile prefix.  This file records the finite, one-sided calculation needed
at that point.

There are two logically separate steps.

* A probability decomposed over crossing counts is bounded by a uniform
  conditional-tail envelope.  No lower bound on an individual crossing
  atom is used.
* Remark A.9 obtains that envelope by comparing the largest conditional
  tail with the smallest admissible conditional tail, then multiplying the
  latter by a lower bound for the aggregate low-scale event.

The comparison factor is retained explicitly.  In the spatial proof it is
an `exp (o(scaleCost))` factor and must be combined with the marked-kernel
loss budget; setting it silently to one would be stronger than the cited
argument.
-/

open Filter MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos1165.AppendixPairCrossingTail

open AppendixFirstMoment AppendixPairMoment AppendixPairReferenceMass
open AppendixA11A12Numerical GaussianBlockFactorization
open GaussianGeometricCutoff GaussianGeometricSchedule
open MarkedTerminalDisintegration Proposition13Assembly Proposition13Scales
open ProfileA11Assembly ProfileConditionalTailUpper ProfileWeightUpper

noncomputable section

/-- A finite mixture over the crossing count (and, if necessary, any
finite retained boundary-state label paired with that count). -/
def crossingMixture {Crossing : Type*}
    (counts : Finset Crossing) (prefixMass tailMass : Crossing → ℝ) : ℝ :=
  ∑ m ∈ counts, prefixMass m * tailMass m

lemma crossingMixture_nonneg
    {Crossing : Type*} [DecidableEq Crossing]
    {counts : Finset Crossing} {prefixMass tailMass : Crossing → ℝ}
    (hprefix : ∀ m ∈ counts, 0 ≤ prefixMass m)
    (htail : ∀ m ∈ counts, 0 ≤ tailMass m) :
    0 ≤ crossingMixture counts prefixMass tailMass := by
  unfold crossingMixture
  exact Finset.sum_nonneg fun m hm ↦
    mul_nonneg (hprefix m hm) (htail m hm)

/-- Summing the actual prefix weights before using a uniform tail bound.
This is the elementary mixture step in (A.16). -/
theorem crossingMixture_le_tailEnvelope
    {Crossing : Type*} [DecidableEq Crossing]
    {counts : Finset Crossing} {prefixMass tailMass : Crossing → ℝ}
    {tailEnvelope : ℝ}
    (hprefix : ∀ m ∈ counts, 0 ≤ prefixMass m)
    (henvelope0 : 0 ≤ tailEnvelope)
    (hsum : ∑ m ∈ counts, prefixMass m ≤ 1)
    (htail : ∀ m ∈ counts, tailMass m ≤ tailEnvelope) :
    crossingMixture counts prefixMass tailMass ≤ tailEnvelope := by
  calc
    crossingMixture counts prefixMass tailMass ≤
        ∑ m ∈ counts, prefixMass m * tailEnvelope := by
      unfold crossingMixture
      exact Finset.sum_le_sum fun m hm ↦
        mul_le_mul_of_nonneg_left (htail m hm) (hprefix m hm)
    _ = (∑ m ∈ counts, prefixMass m) * tailEnvelope := by
      rw [Finset.sum_mul]
    _ ≤ 1 * tailEnvelope :=
      mul_le_mul_of_nonneg_right hsum henvelope0
    _ = tailEnvelope := one_mul _

/-- The same mixture calculation when the retained prefix kernel has total
mass at most an explicit comparison coefficient.  This is the form used
after multiplying the endpoint-integrated A.6 row errors. -/
theorem crossingMixture_le_coefficient_mul_tailEnvelope
    {Crossing : Type*} [DecidableEq Crossing]
    {counts : Finset Crossing} {prefixMass tailMass : Crossing → ℝ}
    {coefficient tailEnvelope : ℝ}
    (hprefix : ∀ m ∈ counts, 0 ≤ prefixMass m)
    (henvelope : 0 ≤ tailEnvelope)
    (hsum : ∑ m ∈ counts, prefixMass m ≤ coefficient)
    (htail : ∀ m ∈ counts, tailMass m ≤ tailEnvelope) :
    crossingMixture counts prefixMass tailMass ≤
      coefficient * tailEnvelope := by
  calc
    crossingMixture counts prefixMass tailMass ≤
        ∑ m ∈ counts, prefixMass m * tailEnvelope := by
      unfold crossingMixture
      exact Finset.sum_le_sum fun m hm ↦
        mul_le_mul_of_nonneg_left (htail m hm) (hprefix m hm)
    _ = (∑ m ∈ counts, prefixMass m) * tailEnvelope := by
      rw [Finset.sum_mul]
    _ ≤ coefficient * tailEnvelope :=
      mul_le_mul_of_nonneg_right hsum henvelope

/-- One-sided walk-to-mixture form, allowing the spatial A.6 construction
to provide an inclusion/upper comparison rather than an artificial exact
factorization. -/
theorem referenceEventMass_le_coefficient_mul_tailEnvelope_of_crossingMixtureUpper
    {Crossing : Type*} [DecidableEq Crossing] {coordinates : ℕ}
    (referenceMass : Fin coordinates → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin coordinates → ℕ))
    (counts : Finset Crossing) (prefixMass tailMass : Crossing → ℝ)
    {coefficient tailEnvelope : ℝ}
    (hfactor : (referenceEventMass referenceMass visitEvent).toReal ≤
      crossingMixture counts prefixMass tailMass)
    (hprefix : ∀ m ∈ counts, 0 ≤ prefixMass m)
    (henvelope : 0 ≤ tailEnvelope)
    (hsum : ∑ m ∈ counts, prefixMass m ≤ coefficient)
    (htail : ∀ m ∈ counts, tailMass m ≤ tailEnvelope) :
    (referenceEventMass referenceMass visitEvent).toReal ≤
      coefficient * tailEnvelope := by
  exact hfactor.trans
    (crossingMixture_le_coefficient_mul_tailEnvelope
      hprefix henvelope hsum htail)

/-- Source-facing version of the preceding mixture calculation. -/
theorem referenceEventMass_le_of_crossingMixture
    {Crossing : Type*} [DecidableEq Crossing] {coordinates : ℕ}
    (referenceMass : Fin coordinates → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin coordinates → ℕ))
    (counts : Finset Crossing) (prefixMass tailMass : Crossing → ℝ)
    {tailEnvelope : ℝ}
    (hfactor :
      (referenceEventMass referenceMass visitEvent).toReal =
        crossingMixture counts prefixMass tailMass)
    (hprefix : ∀ m ∈ counts, 0 ≤ prefixMass m)
    (henvelope0 : 0 ≤ tailEnvelope)
    (hsum : ∑ m ∈ counts, prefixMass m ≤ 1)
    (htail : ∀ m ∈ counts, tailMass m ≤ tailEnvelope) :
    (referenceEventMass referenceMass visitEvent).toReal ≤ tailEnvelope := by
  rw [hfactor]
  exact crossingMixture_le_tailEnvelope hprefix henvelope0 hsum htail

/-- Explicit A.11/A.12 envelope for a mixture over exact profile-prefix
fibres.  Refining the source's crossing-count partition to complete prefix
fibres is harmless here: the actual prefix probabilities are summed before
the common uniform continuation bound is applied. -/
theorem referenceEventMass_le_exp_of_profilePrefixMixture
    {coordinates n start : ℕ}
    (referenceMass : Fin coordinates → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin coordinates → ℕ))
    (prefixMass : Profile start → ℝ)
    (htailStart : profileUpperTailStart ≤ start)
    (hstartn : start ≤ n)
    (hfactor :
      (referenceEventMass referenceMass visitEvent).toReal =
        crossingMixture (constrainedProfiles start profileUpperDelta)
          prefixMass
          (fun pref ↦ constrainedProfileTailWeight n start
            ((show 2 ≤ profileUpperTailStart by
              norm_num [profileUpperTailStart]).trans htailStart)
            hstartn pref profileUpperDelta))
    (hprefix : ∀ pref ∈ constrainedProfiles start profileUpperDelta,
      0 ≤ prefixMass pref)
    (hsum : ∑ pref ∈ constrainedProfiles start profileUpperDelta,
      prefixMass pref ≤ 1) :
    (referenceEventMass referenceMass visitEvent).toReal ≤
      Real.exp (-(2 * (n - start : ℕ) : ℝ) +
        a11ErrorCoefficient profileUpperDelta 2 1 11 *
          (n : ℝ) ^ (3 * profileUpperDelta) + 4 +
        ∑ j ∈ Finset.Ico start n, 1 / (j : ℝ)) := by
  apply referenceEventMass_le_of_crossingMixture
    referenceMass visitEvent
      (constrainedProfiles start profileUpperDelta) prefixMass
      (fun pref ↦ constrainedProfileTailWeight n start
        ((show 2 ≤ profileUpperTailStart by
          norm_num [profileUpperTailStart]).trans htailStart)
        hstartn pref profileUpperDelta)
      hfactor hprefix (Real.exp_nonneg _) hsum
  intro pref hpref
  exact constrainedProfileTailWeight_le_exp htailStart hstartn pref

/-- The raw fixed-prefix estimate with its harmonic term absorbed into the
same explicit coefficient used by the complete one-point upper bound. -/
theorem constrainedProfileTailWeight_le_profileUpperEnvelope
    {n start : ℕ}
    (htailStart : profileUpperTailStart ≤ start)
    (hstartn : start ≤ n) (pref : Profile start) :
    constrainedProfileTailWeight n start
        ((show 2 ≤ profileUpperTailStart by
          norm_num [profileUpperTailStart]).trans htailStart)
        hstartn pref profileUpperDelta ≤
      Real.exp (-(2 * (n - start : ℕ) : ℝ) +
        profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ)) := by
  have hraw := constrainedProfileTailWeight_le_exp
    htailStart hstartn pref
  have hnOne : 1 ≤ n := by
    exact (show 1 ≤ profileUpperTailStart by
      norm_num [profileUpperTailStart]).trans (htailStart.trans hstartn)
  have hsubset : Finset.Ico start n ⊆
      Finset.Ico profileUpperTailStart n := by
    intro j hj
    rw [Finset.mem_Ico] at hj ⊢
    exact ⟨htailStart.trans hj.1, hj.2⟩
  have hsum : (∑ j ∈ Finset.Ico start n, 1 / (j : ℝ)) ≤
      3 * (n : ℝ) ^ (3 / 5 : ℝ) := by
    exact (Finset.sum_le_sum_of_subset_of_nonneg hsubset
      (fun j _hj _hnot ↦ by positivity)).trans
        (harmonicTail_le_three_rpow hnOne)
  have hpowOne : (1 : ℝ) ≤ (n : ℝ) ^ (3 / 5 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast hnOne) (by norm_num)
  have ha11 : 0 ≤
      a11ErrorCoefficient profileUpperDelta 2 1 11 :=
    a11ErrorCoefficient_nonneg
      (by norm_num [profileUpperDelta]) (by norm_num) (by norm_num) (by norm_num)
  have hlog : 0 ≤ Real.log
      ((constrainedProfiles profileUpperTailStart profileUpperDelta).card + 1) := by
    apply Real.log_nonneg
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega :
      (constrainedProfiles profileUpperTailStart
        profileUpperDelta).card + 1 ≠ 0)
  apply hraw.trans
  apply Real.exp_le_exp.mpr
  have hexponent : 3 * profileUpperDelta = (3 / 5 : ℝ) := by
    norm_num [profileUpperDelta]
  rw [hexponent]
  unfold profileUpperConstant profileUpperCoreConstant
  have hstart0 : (0 : ℝ) ≤ profileUpperTailStart := Nat.cast_nonneg _
  nlinarith

/-- Mixture-level version with the common explicit one-point upper
coefficient. -/
theorem referenceEventMass_le_profileUpperEnvelope_of_profilePrefixMixture
    {coordinates n start : ℕ}
    (referenceMass : Fin coordinates → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin coordinates → ℕ))
    (prefixMass : Profile start → ℝ)
    (htailStart : profileUpperTailStart ≤ start)
    (hstartn : start ≤ n)
    (hfactor :
      (referenceEventMass referenceMass visitEvent).toReal =
        crossingMixture (constrainedProfiles start profileUpperDelta)
          prefixMass
          (fun pref ↦ constrainedProfileTailWeight n start
            ((show 2 ≤ profileUpperTailStart by
              norm_num [profileUpperTailStart]).trans htailStart)
            hstartn pref profileUpperDelta))
    (hprefix : ∀ pref ∈ constrainedProfiles start profileUpperDelta,
      0 ≤ prefixMass pref)
    (hsum : ∑ pref ∈ constrainedProfiles start profileUpperDelta,
      prefixMass pref ≤ 1) :
    (referenceEventMass referenceMass visitEvent).toReal ≤
      Real.exp (-(2 * (n - start : ℕ) : ℝ) +
        profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ)) := by
  apply referenceEventMass_le_of_crossingMixture
    referenceMass visitEvent
      (constrainedProfiles start profileUpperDelta) prefixMass
      (fun pref ↦ constrainedProfileTailWeight n start
        ((show 2 ≤ profileUpperTailStart by
          norm_num [profileUpperTailStart]).trans htailStart)
        hstartn pref profileUpperDelta)
      hfactor hprefix (Real.exp_nonneg _) hsum
  intro pref hpref
  exact constrainedProfileTailWeight_le_profileUpperEnvelope
    htailStart hstartn pref

/-- Exact exponent arithmetic turning the absolute conditional-tail upper
bound into an explicit one-point envelope divided by the checked prefix
lower.  Unlike the stronger quotient by the *actual* full mass, this needs
no sup/inf tail-comparability theorem. -/
theorem profileUpperTailEnvelope_le_exp_div_prefixProfileLower
    {n start : ℕ} {A : ℝ}
    (hstartn : start ≤ n)
    (hcutoff : GaussianGeometricCutoff.geometricCutoff ≤ start)
    (hbudget : profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ) ≤
      A + prefixProfileCost start) :
    Real.exp (-(2 * (n - start : ℕ) : ℝ) +
        profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ)) ≤
      Real.exp (-2 * (n : ℝ) + A) / prefixProfileLower start := by
  rw [prefixProfileLower_eq_exp hcutoff, ← Real.exp_sub]
  apply Real.exp_le_exp.mpr
  rw [Nat.cast_sub hstartn]
  linarith

/-- The only possibly negative summand in the canonical prefix cost is the
fixed centered-prefix reserve.  This lower bound is uniform in the terminal
scale. -/
lemma centeredPrefixReserve_le_prefixProfileCost (q : ℕ) :
    centeredPrefixReserve geometricCutoff ≤ prefixProfileCost q := by
  have hstart : ∀ b ∈
      geometricSchedule geometricCutoff
        (geometricDepth geometricCutoff q) q,
      0 < b.start := by
    intro b hb
    exact lt_of_lt_of_le geometricCutoff_pos
      (geometricSchedule_start_ge
        (show 1 ≤ geometricCutoff by exact geometricCutoff_pos) b hb)
  have hradius : ∀ b ∈
      geometricSchedule geometricCutoff
        (geometricDepth geometricCutoff q) q,
      0 < b.radius := by
    intro b hb
    rw [geometricSchedule_radius_eq b hb]
    have hsb : 32 ≤ b.start :=
      geometricCutoff_ge_thirty_two.trans
        (geometricSchedule_start_ge
          (show 1 ≤ geometricCutoff by exact geometricCutoff_pos) b hb)
    have hlower := geometricRadius_lower hsb
    have hpositive : (0 : ℝ) < geometricRadius b.start :=
      lt_of_lt_of_le (by positivity) hlower
    exact_mod_cast hpositive
  have hblocks := gaussianBlockTotalCost_nonneg
    (geometricSchedule geometricCutoff
      (geometricDepth geometricCutoff q) q) hstart hradius
  have ha11 : 0 ≤
      a11ErrorCoefficient chosenProfileDelta 2 1 10 :=
    a11ErrorCoefficient_nonneg
      (by norm_num [chosenProfileDelta]) (by norm_num) (by norm_num) (by norm_num)
  have hpow : 0 ≤ (q : ℝ) ^ (3 * chosenProfileDelta) := by positivity
  unfold prefixProfileCost multiblockProfileCost
  nlinarith

/-- A nonnegative fixed constant compensating for the sign of the finite
centered-prefix reserve. -/
def prefixProfileCostDeficit : ℝ :=
  max (-centeredPrefixReserve geometricCutoff) 0

lemma prefixProfileCost_add_deficit_nonneg (q : ℕ) :
    0 ≤ prefixProfileCost q + prefixProfileCostDeficit := by
  have hcost := centeredPrefixReserve_le_prefixProfileCost q
  have hdeficit : -centeredPrefixReserve geometricCutoff ≤
      prefixProfileCostDeficit := le_max_left _ _
  linarith

/-- The available prefix budget is already at least one at every positive
scale.  This elementary strengthening is useful for absorbing the
`exp (O(n⁻³))` endpoint-integrated A.6 row loss. -/
lemma one_le_prefixProfileCost_add_deficit {q : ℕ} (hq : 1 ≤ q) :
    1 ≤ prefixProfileCost q + prefixProfileCostDeficit := by
  have hstart : ∀ b ∈
      geometricSchedule geometricCutoff
        (geometricDepth geometricCutoff q) q,
      0 < b.start := by
    intro b hb
    exact lt_of_lt_of_le geometricCutoff_pos
      (geometricSchedule_start_ge
        (show 1 ≤ geometricCutoff by exact geometricCutoff_pos) b hb)
  have hradius : ∀ b ∈
      geometricSchedule geometricCutoff
        (geometricDepth geometricCutoff q) q,
      0 < b.radius := by
    intro b hb
    rw [geometricSchedule_radius_eq b hb]
    have hsb : 32 ≤ b.start :=
      geometricCutoff_ge_thirty_two.trans
        (geometricSchedule_start_ge
          (show 1 ≤ geometricCutoff by exact geometricCutoff_pos) b hb)
    have hlower := geometricRadius_lower hsb
    have hpositive : (0 : ℝ) < geometricRadius b.start :=
      lt_of_lt_of_le (by positivity) hlower
    exact_mod_cast hpositive
  have hblocks := gaussianBlockTotalCost_nonneg
    (geometricSchedule geometricCutoff
      (geometricDepth geometricCutoff q) q) hstart hradius
  have ha11 : 1 ≤
      a11ErrorCoefficient chosenProfileDelta 2 1 10 := by
    norm_num [a11ErrorCoefficient, ProfileTaylor.parabolicTaylorCoefficient,
      chosenProfileDelta]
  have hpow : (1 : ℝ) ≤ (q : ℝ) ^ (3 * chosenProfileDelta) := by
    apply Real.one_le_rpow
    · exact_mod_cast hq
    · norm_num [chosenProfileDelta]
  have hdeficit : -centeredPrefixReserve geometricCutoff ≤
      prefixProfileCostDeficit := le_max_left _ _
  unfold prefixProfileCost multiblockProfileCost
  nlinarith

lemma coefficient_le_exp_prefixProfileCost_add_deficit_of_le_exp_one
    {q : ℕ} {coefficient : ℝ} (hq : 1 ≤ q)
    (hcoefficient : coefficient ≤ Real.exp 1) :
    coefficient ≤
      Real.exp (prefixProfileCost q + prefixProfileCostDeficit) :=
  hcoefficient.trans (Real.exp_le_exp.mpr
    (one_le_prefixProfileCost_add_deficit hq))

lemma prefixProfileCostDeficit_nonneg : 0 ≤ prefixProfileCostDeficit := by
  unfold prefixProfileCostDeficit
  exact le_max_right _ _

/-- The complete conditional-tail envelope, including the fixed reserve
deficit, fits in the same eventual `1/64` profile share. -/
theorem eventually_profileUpperCost_add_deficit_le_sixtyFourth_scaleCost
    {delta : ℝ} (hdelta : 0 < delta) :
    ∀ᶠ n : ℕ in atTop,
      profileUpperConstant *
          (scaleIndex delta n : ℝ) ^ (3 / 5 : ℝ) +
        prefixProfileCostDeficit ≤ scaleCost delta n / 64 := by
  have hexp : (3 / 5 : ℝ) < costExponent delta := by
    unfold costExponent
    linarith [scaleSlack_pos hdelta]
  have hprofileReal := eventually_const_mul_rpow_le_half_rpow
    (C := 64 * profileUpperConstant) hexp
    (mul_nonneg (by norm_num) profileUpperConstant_nonneg)
  have hprofile := (tendsto_scaleIndex_atTop delta).eventually hprofileReal
  have hdeficitTop :=
    ((tendsto_rpow_atTop (costExponent_pos hdelta)).comp
      (tendsto_scaleIndex_atTop delta)).eventually
        (eventually_ge_atTop (128 * prefixProfileCostDeficit))
  filter_upwards [hprofile, hdeficitTop] with n hp hd
  simp only [Function.comp_apply] at hd
  unfold scaleCost
  nlinarith

/-- At the eventual scales, the fixed-prefix tail exponent fits the
deficit-corrected one-point envelope divided by the canonical prefix lower. -/
theorem profileUpperTailEnvelope_le_pairEnvelope_div_prefix
    {n start : ℕ}
    (hstartn : start ≤ n) (hcutoff : geometricCutoff ≤ start) :
    Real.exp
        (-(2 * (n - start : ℕ) : ℝ) +
          profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ)) ≤
      Real.exp
          (-2 * (n : ℝ) +
            (profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ) +
              prefixProfileCostDeficit)) /
        prefixProfileLower start := by
  apply profileUpperTailEnvelope_le_exp_div_prefixProfileLower
    hstartn hcutoff
  have hnonneg := prefixProfileCost_add_deficit_nonneg start
  linarith

/-- A positive A.6 comparison coefficient can be charged to the actual
prefix cost before the aggregate prefix lower is divided out.  This is the
coefficient-bearing version needed by the literal radial-label-word
construction. -/
theorem coefficient_mul_profileUpperTailEnvelope_le_pairEnvelope_div_prefix
    {n start : ℕ} {coefficient : ℝ}
    (hstartn : start ≤ n) (hcutoff : geometricCutoff ≤ start)
    (hcoefficient : coefficient ≤
      Real.exp (prefixProfileCost start + prefixProfileCostDeficit)) :
    coefficient *
        Real.exp (-(2 * (n - start : ℕ) : ℝ) +
          profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ)) ≤
      Real.exp
          (-2 * (n : ℝ) +
            (profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ) +
              prefixProfileCostDeficit)) /
        prefixProfileLower start := by
  have hmul :
      coefficient *
          Real.exp (-(2 * (n - start : ℕ) : ℝ) +
            profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ)) ≤
        Real.exp (prefixProfileCost start + prefixProfileCostDeficit) *
          Real.exp (-(2 * (n - start : ℕ) : ℝ) +
            profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ)) :=
    mul_le_mul_of_nonneg_right hcoefficient (Real.exp_nonneg _)
  rw [prefixProfileLower_eq_exp hcutoff, ← Real.exp_sub]
  rw [← Real.exp_add] at hmul
  apply hmul.trans_eq
  congr 1
  rw [Nat.cast_sub hstartn]
  ring

/-- Walk-to-mixture upper comparison with the accumulated A.6 coefficient
kept explicit.  Prefix probabilities are normalized before the uniform
A.11 continuation bound is applied; no individual prefix is divided by an
aggregate lower bound. -/
theorem referenceEventMass_le_exp_add_prefixDeficit_div_of_profilePrefixMixtureUpper
    {coordinates n start : ℕ}
    (referenceMass : Fin coordinates → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin coordinates → ℕ))
    (prefixMass : Profile start → ℝ) (coefficient : ℝ)
    (htailStart : profileUpperTailStart ≤ start)
    (hstartn : start ≤ n)
    (hcutoff : geometricCutoff ≤ start)
    (hfactor :
      (referenceEventMass referenceMass visitEvent).toReal ≤
        coefficient *
          crossingMixture (constrainedProfiles start profileUpperDelta)
            prefixMass
            (fun pref ↦ constrainedProfileTailWeight n start
              ((show 2 ≤ profileUpperTailStart by
                norm_num [profileUpperTailStart]).trans htailStart)
              hstartn pref profileUpperDelta))
    (hcoefficient0 : 0 ≤ coefficient)
    (hcoefficient : coefficient ≤
      Real.exp (prefixProfileCost start + prefixProfileCostDeficit))
    (hprefix : ∀ pref ∈ constrainedProfiles start profileUpperDelta,
      0 ≤ prefixMass pref)
    (hsum : ∑ pref ∈ constrainedProfiles start profileUpperDelta,
      prefixMass pref ≤ 1) :
    (referenceEventMass referenceMass visitEvent).toReal ≤
      Real.exp (-2 * (n : ℝ) +
        (profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ) +
          prefixProfileCostDeficit)) /
        prefixProfileLower start := by
  have hmixture :
      crossingMixture (constrainedProfiles start profileUpperDelta)
          prefixMass
          (fun pref ↦ constrainedProfileTailWeight n start
            ((show 2 ≤ profileUpperTailStart by
              norm_num [profileUpperTailStart]).trans htailStart)
            hstartn pref profileUpperDelta) ≤
        Real.exp (-(2 * (n - start : ℕ) : ℝ) +
          profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ)) := by
    apply crossingMixture_le_tailEnvelope hprefix (Real.exp_nonneg _) hsum
    intro pref _hpref
    exact constrainedProfileTailWeight_le_profileUpperEnvelope
      htailStart hstartn pref
  exact hfactor.trans ((mul_le_mul_of_nonneg_left hmixture hcoefficient0).trans
    (coefficient_mul_profileUpperTailEnvelope_le_pairEnvelope_div_prefix
      hstartn hcutoff hcoefficient))

/-- Scalar two-stage form of the preceding estimate.  The radial-profile
tail is kept separate from the terminal marked visit kernel: the former is
the coefficient times this prefix mixture, while the latter is normalized
independently.  This is the source-correct A.16 interface for the asymmetric
far-pair atom. -/
theorem coefficient_mul_profilePrefixMixture_le_exp_add_prefixDeficit_div
    {n start : ℕ}
    (prefixMass : Profile start → ℝ) (coefficient : ℝ)
    (htailStart : profileUpperTailStart ≤ start)
    (hstartn : start ≤ n)
    (hcutoff : geometricCutoff ≤ start)
    (hcoefficient0 : 0 ≤ coefficient)
    (hcoefficient : coefficient ≤
      Real.exp (prefixProfileCost start + prefixProfileCostDeficit))
    (hprefix : ∀ pref ∈ constrainedProfiles start profileUpperDelta,
      0 ≤ prefixMass pref)
    (hsum : ∑ pref ∈ constrainedProfiles start profileUpperDelta,
      prefixMass pref ≤ 1) :
    coefficient *
        crossingMixture (constrainedProfiles start profileUpperDelta)
          prefixMass
          (fun pref ↦ constrainedProfileTailWeight n start
            ((show 2 ≤ profileUpperTailStart by
              norm_num [profileUpperTailStart]).trans htailStart)
            hstartn pref profileUpperDelta) ≤
      Real.exp (-2 * (n : ℝ) +
        (profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ) +
          prefixProfileCostDeficit)) /
        prefixProfileLower start := by
  have hmixture :
      crossingMixture (constrainedProfiles start profileUpperDelta)
          prefixMass
          (fun pref ↦ constrainedProfileTailWeight n start
            ((show 2 ≤ profileUpperTailStart by
              norm_num [profileUpperTailStart]).trans htailStart)
            hstartn pref profileUpperDelta) ≤
        Real.exp (-(2 * (n - start : ℕ) : ℝ) +
          profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ)) := by
    apply crossingMixture_le_tailEnvelope hprefix (Real.exp_nonneg _) hsum
    intro pref _hpref
    exact constrainedProfileTailWeight_le_profileUpperEnvelope
      htailStart hstartn pref
  exact (mul_le_mul_of_nonneg_left hmixture hcoefficient0).trans
    (coefficient_mul_profileUpperTailEnvelope_le_pairEnvelope_div_prefix
      hstartn hcutoff hcoefficient)

/-- Walk-facing conditional-tail certificate obtained from a literal
prefix-fibre mixture and explicit exponent arithmetic.  This is the direct
replacement for an unjustified quotient by the exact full profile mass. -/
theorem referenceEventMass_le_exp_div_prefixProfileLower_of_profilePrefixMixture
    {coordinates n start : ℕ} {A : ℝ}
    (referenceMass : Fin coordinates → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin coordinates → ℕ))
    (prefixMass : Profile start → ℝ)
    (htailStart : profileUpperTailStart ≤ start)
    (hstartn : start ≤ n)
    (hcutoff : GaussianGeometricCutoff.geometricCutoff ≤ start)
    (hbudget : profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ) ≤
      A + prefixProfileCost start)
    (hfactor :
      (referenceEventMass referenceMass visitEvent).toReal =
        crossingMixture (constrainedProfiles start profileUpperDelta)
          prefixMass
          (fun pref ↦ constrainedProfileTailWeight n start
            ((show 2 ≤ profileUpperTailStart by
              norm_num [profileUpperTailStart]).trans htailStart)
            hstartn pref profileUpperDelta))
    (hprefix : ∀ pref ∈ constrainedProfiles start profileUpperDelta,
      0 ≤ prefixMass pref)
    (hsum : ∑ pref ∈ constrainedProfiles start profileUpperDelta,
      prefixMass pref ≤ 1) :
    (referenceEventMass referenceMass visitEvent).toReal ≤
      Real.exp (-2 * (n : ℝ) + A) / prefixProfileLower start := by
  exact (referenceEventMass_le_profileUpperEnvelope_of_profilePrefixMixture
    referenceMass visitEvent prefixMass htailStart hstartn hfactor
    hprefix hsum).trans
      (profileUpperTailEnvelope_le_exp_div_prefixProfileLower
        hstartn hcutoff hbudget)

/-- The complete one-point profile mass is bounded by the same
deficit-corrected explicit envelope used for the conditional tail. -/
theorem constrainedProfileWeight_le_exp_add_prefixDeficit
    {n : ℕ} (hn : profileUpperTailStart ≤ n) :
    constrainedProfileWeight n profileUpperDelta ≤
      Real.exp (-2 * (n : ℝ) +
        (profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ) +
          prefixProfileCostDeficit)) := by
  exact (constrainedProfileWeight_le_exp hn).trans
    (Real.exp_le_exp.mpr (by
      have hdeficit := prefixProfileCostDeficit_nonneg
      linarith))

/-- Fully explicit scalar conditional-tail field from the literal finite
prefix mixture.  All analytic work is discharged; the remaining premises
are only the exact walk-to-mixture equality, nonnegativity of its prefix
weights, and their subprobability normalization. -/
theorem referenceEventMass_le_exp_add_prefixDeficit_div_of_profilePrefixMixture
    {coordinates n start : ℕ}
    (referenceMass : Fin coordinates → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin coordinates → ℕ))
    (prefixMass : Profile start → ℝ)
    (htailStart : profileUpperTailStart ≤ start)
    (hstartn : start ≤ n)
    (hcutoff : geometricCutoff ≤ start)
    (hfactor :
      (referenceEventMass referenceMass visitEvent).toReal =
        crossingMixture (constrainedProfiles start profileUpperDelta)
          prefixMass
          (fun pref ↦ constrainedProfileTailWeight n start
            ((show 2 ≤ profileUpperTailStart by
              norm_num [profileUpperTailStart]).trans htailStart)
            hstartn pref profileUpperDelta))
    (hprefix : ∀ pref ∈ constrainedProfiles start profileUpperDelta,
      0 ≤ prefixMass pref)
    (hsum : ∑ pref ∈ constrainedProfiles start profileUpperDelta,
      prefixMass pref ≤ 1) :
    (referenceEventMass referenceMass visitEvent).toReal ≤
      Real.exp (-2 * (n : ℝ) +
        (profileUpperConstant * (n : ℝ) ^ (3 / 5 : ℝ) +
          prefixProfileCostDeficit)) /
        prefixProfileLower start := by
  exact (referenceEventMass_le_profileUpperEnvelope_of_profilePrefixMixture
    referenceMass visitEvent prefixMass htailStart hstartn hfactor
    hprefix hsum).trans
      (profileUpperTailEnvelope_le_pairEnvelope_div_prefix
        hstartn hcutoff)

/-- The exact `sup tail / inf tail` calculation of Remark A.9.  The
low-scale mass is aggregate: it is multiplied by one common lower-tail
value, never asserted to be below every individual prefix atom. -/
theorem tailEnvelope_le_comparison_mul_div
    {tailEnvelope tailFloor prefixLower pointMass comparison : ℝ}
    (hprefix : 0 < prefixLower)
    (hcomparison : 0 ≤ comparison)
    (hcompare : tailEnvelope ≤ comparison * tailFloor)
    (hfullLower : prefixLower * tailFloor ≤ pointMass) :
    tailEnvelope ≤ comparison * (pointMass / prefixLower) := by
  have hfloor : tailFloor ≤ pointMass / prefixLower :=
    (le_div_iff₀ hprefix).2 (by simpa [mul_comm] using hfullLower)
  exact hcompare.trans
    (mul_le_mul_of_nonneg_left hfloor hcomparison)

/-- Complete finite crossing-count form of (A.16)--(A.17), before the
sublinear comparison loss is absorbed into the far-pair budget. -/
theorem referenceEventMass_le_comparison_mul_div
    {Crossing : Type*} [DecidableEq Crossing] {coordinates prefixScale : ℕ}
    (referenceMass : Fin coordinates → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin coordinates → ℕ))
    (counts : Finset Crossing) (prefixMass tailMass : Crossing → ℝ)
    {tailEnvelope tailFloor pointMass comparison : ℝ}
    (hprefixMass : ∀ m ∈ counts, 0 ≤ prefixMass m)
    (htailEnvelope0 : 0 ≤ tailEnvelope)
    (hsum : ∑ m ∈ counts, prefixMass m ≤ 1)
    (htail : ∀ m ∈ counts, tailMass m ≤ tailEnvelope)
    (hfactor :
      (referenceEventMass referenceMass visitEvent).toReal =
        crossingMixture counts prefixMass tailMass)
    (hcomparison : 0 ≤ comparison)
    (hcompare : tailEnvelope ≤ comparison * tailFloor)
    (hfullLower :
      prefixProfileLower prefixScale * tailFloor ≤ pointMass) :
    (referenceEventMass referenceMass visitEvent).toReal ≤
      comparison * (pointMass / prefixProfileLower prefixScale) := by
  exact (referenceEventMass_le_of_crossingMixture
      referenceMass visitEvent counts prefixMass tailMass hfactor
      hprefixMass htailEnvelope0 hsum htail).trans
    (tailEnvelope_le_comparison_mul_div
      (prefixProfileLower_pos prefixScale) hcomparison
      hcompare hfullLower)

/-- The retained outside mass and the conditional-tail comparison yield
the pair envelope with the comparison factor kept visible. -/
theorem referenceEventMass_mul_successful_le_comparison_mul_pairEnvelope
    {coordinates prefixScale : ℕ}
    (referenceMass : Fin coordinates → ℕ → ℝ≥0∞)
    (visitEvent : Set (Fin coordinates → ℕ))
    (successful : Set StepPath)
    {pointMass comparison : ℝ}
    (hpoint : 0 ≤ pointMass)
    (hcomparison : 0 ≤ comparison)
    (hsuccessful : fairSteps.real successful ≤ pointMass)
    (htail : (referenceEventMass referenceMass visitEvent).toReal ≤
      comparison * (pointMass / prefixProfileLower prefixScale)) :
    (referenceEventMass referenceMass visitEvent).toReal *
        fairSteps.real successful ≤
      comparison * (pointMass ^ 2 / prefixProfileLower prefixScale) := by
  have htail0 : 0 ≤
      (referenceEventMass referenceMass visitEvent).toReal :=
    ENNReal.toReal_nonneg
  have hprefix0 : 0 ≤ prefixProfileLower prefixScale :=
    prefixProfileLower_nonneg prefixScale
  calc
    (referenceEventMass referenceMass visitEvent).toReal *
          fairSteps.real successful ≤
        (comparison * (pointMass / prefixProfileLower prefixScale)) *
          pointMass :=
      mul_le_mul htail hsuccessful measureReal_nonneg
        (mul_nonneg hcomparison (div_nonneg hpoint hprefix0))
    _ = comparison *
          (pointMass ^ 2 / prefixProfileLower prefixScale) := by ring

end

end Erdos1165.AppendixPairCrossingTail
