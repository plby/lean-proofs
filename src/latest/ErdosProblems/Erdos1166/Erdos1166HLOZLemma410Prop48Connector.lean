/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZStoppedMapLawReduced
import ErdosProblems.Erdos1166.Erdos1166HLOZPrimedOddRightWinner
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47NamedEstimateBridges
import ErdosProblems.Erdos1166.Erdos1166HLOZEquation447
import ErdosProblems.Erdos1166.Erdos1166HLOZNearCriticalBridge
import ErdosProblems.Erdos1166.Erdos1166HLOZTerminalParityWinner
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Lemma411412Connector
import ErdosProblems.Erdos1166.Erdos1166HLOZProp45SourceAbsorption
import ErdosProblems.Erdos1166.Erdos1166HLOZProp47Prop45Connector

/-!
# The stopped-profile reduction in HLOZ Lemma 4.10

This file connects the literal stopped active-free law to the high-band
estimate of Proposition 4.8.  In particular, the product law is not a field
of the source-facing input: it is derived from
`unprimedEven_activeFreeWinning_capped_map_law_reduced`.  Its public atom
data are now the literal source conditions: cardinality of the creation set,
the off-base mixed condition, membership of the terminal base, and
nonemptiness of the admissible stopped-vector event.  The grouped-event
identity, mixed-coordinate positivity, and stopped-history premises are all
discharged by the reduced stopped-map-law interface.

There are two honest limitations of the currently checked source API.

* Exact stopped map laws are available for all four horizontal cases:
  unprimed-even, unprimed-odd terminal, primed-odd, and primed-even terminal.
  The deterministic global event cover by those literal atoms, and the
  independent column tilings, remain separate source obligations.
* Lemma 4.10 invokes Proposition 4.8 only through exponent `7/10`.  Above
  `7/10` the source argument is instead the deterministic spatial-cardinality
  comparison (4.973)--(4.980); no extension of Proposition 4.8 is intended.

The theorems below prove the complete reduction on every atom and band for
which those four checked map-law interfaces apply. They deliberately do not replace
either missing item by a candidate-tail assumption.
-/

namespace Erdos1166.HLOZLemma410Prop48Connector

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal BigOperators ProbabilityTheory Topology

open HLOZDecomposition HLOZActualStopped HLOZPrimedStopped
  HLOZReconstruction HLOZIncompleteStoppedBlocks
  HLOZMixedCreationBlocks HLOZStoppedSourcePartition
  HLOZStoppedMixedReconstruction HLOZStoppedMapLaw
  HLOZStoppedMapLawReduced HLOZPrimedOddMixedReconstruction
  HLOZPrimedOddRightWinner
  HLOZSourceInstantiation
  HLOZSourceInstantiation
  HLOZPairing
  HLOZProp48SourceBands HLOZProp48Truncated HLOZLemma411
  HLOZLemma411Recursion HLOZLemma412Windows HLOZBandRatios
  HLOZProp47Parameters HLOZProp47SourceAssembly
  HLOZLemma410SourceBands HLOZLemma410SourceAbsorption
  HLOZProp47NamedEstimateBridges HLOZEquation447
  HLOZTerminalParityWinner HLOZProp47Lemma411412Connector
  HLOZProp45SourceClock HLOZProp45SourceInterval HLOZProp45SourceMirrors
  HLOZProp45SourceEndpoints
  HLOZProp45SourceAbsorption HLOZProp47Prop45Connector

/-! ## The exact checked low-band Proposition 4.8 consequence -/

/-- Converting the unshifted logarithmic-square rate in the checked
Proposition 4.8 theorem to the `(m+1)` normalization used by Lemma 4.10.
The factor four is exactly the cost of
`log (m+1) <= 2 log m`. -/
theorem eventually_prop48Rate_le_sourceBetaCandidateTail
    {rate d : ℝ} (hd : 0 < d) (hcompare : 4 * d ≤ rate) :
    ∀ᶠ m : ℕ in atTop,
      ENNReal.ofReal
          (Real.exp (-rate * Real.log (m : ℝ) ^ 2)) ≤
        sourceBetaCandidateTail d m := by
  filter_upwards [eventually_ge_atTop 2] with m hm
  have hmpos : (0 : ℝ) < m := by positivity
  have hm1pos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hm1le : (m : ℝ) + 1 ≤ (m : ℝ) ^ 2 := by
    exact_mod_cast (show m + 1 ≤ m ^ 2 by nlinarith)
  have hlog : Real.log ((m : ℝ) + 1) ≤ 2 * Real.log (m : ℝ) := by
    calc
      Real.log ((m : ℝ) + 1) ≤ Real.log ((m : ℝ) ^ 2) :=
        Real.log_le_log hm1pos hm1le
      _ = 2 * Real.log (m : ℝ) := by rw [Real.log_pow]; norm_num
  have hlog0 : 0 ≤ Real.log ((m : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  have hmLog0 : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ m by omega))
  have hsquare : Real.log ((m : ℝ) + 1) ^ 2 ≤
      4 * Real.log (m : ℝ) ^ 2 := by nlinarith
  apply ENNReal.ofReal_le_ofReal
  apply Real.exp_le_exp.mpr
  nlinarith

/-- A fixed two-branch union does not change the logarithmic-square rate.
We spend half of the requested exponent on each parity branch, and absorb
the numerical factor two once `m` is large. -/
theorem eventually_two_mul_sourceBetaCandidateTail_two_mul_le
    {d : ℝ} (hd : 0 < d) :
    ∀ᶠ m : ℕ in atTop,
      (2 : ℝ≥0∞) * sourceBetaCandidateTail (2 * d) m ≤
        sourceBetaCandidateTail d m := by
  have hcast : Tendsto (fun m : ℕ ↦ (m : ℝ) + 1) atTop atTop := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (tendsto_atTop_add_const_right atTop (1 : ℝ)
        (tendsto_natCast_atTop_atTop (R := ℝ)))
  have hlog : Tendsto (fun m : ℕ ↦ Real.log ((m : ℝ) + 1)) atTop atTop :=
    Real.tendsto_log_atTop.comp hcast
  filter_upwards
      [hlog.eventually_ge_atTop (max 1 (Real.log 2 / d))] with m hm
  let L := Real.log ((m : ℝ) + 1)
  have hLone : 1 ≤ L := (le_max_left _ _).trans hm
  have hLratio : Real.log 2 / d ≤ L := (le_max_right _ _).trans hm
  have hLnonneg : 0 ≤ L := by linarith
  have hLsq : L ≤ L ^ 2 := by nlinarith
  have hlogTwo : Real.log 2 ≤ d * L ^ 2 := by
    have hmul : d * (Real.log 2 / d) ≤ d * L ^ 2 := by
      exact mul_le_mul_of_nonneg_left (hLratio.trans hLsq) hd.le
    calc
      Real.log 2 = d * (Real.log 2 / d) := by field_simp
      _ ≤ d * L ^ 2 := hmul
  have htwoExp : (2 : ℝ) ≤ Real.exp (d * L ^ 2) :=
    (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 2)).mp hlogTwo
  have hreal :
      2 * Real.exp (-(2 * d) * L ^ 2) ≤
        Real.exp (-d * L ^ 2) := by
    calc
      2 * Real.exp (-(2 * d) * L ^ 2) =
          Real.exp (-(2 * d) * L ^ 2) * 2 := by ring
      _ ≤ Real.exp (-(2 * d) * L ^ 2) * Real.exp (d * L ^ 2) :=
        mul_le_mul_of_nonneg_left htwoExp (Real.exp_nonneg _)
      _ = Real.exp (-d * L ^ 2) := by
        rw [← Real.exp_add]
        congr 1
        ring
  unfold sourceBetaCandidateTail
  change (2 : ℝ≥0∞) * ENNReal.ofReal
      (Real.exp (-(2 * d) * L ^ 2)) ≤
    ENNReal.ofReal (Real.exp (-d * L ^ 2))
  rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul (by norm_num)]
  exact ENNReal.ofReal_le_ofReal hreal

/-- The polynomial number of interval-level Proposition-4.5 errors is still
negligible on the logarithmic-square scale of a Proposition-4.8 candidate
tail.  This is the numerical absorption needed by the banded path-space
transport below. -/
theorem eventually_intervalCount_mul_sourceProp45Error_le_candidateTail
    {d : ℝ} (hd : 0 < d) :
    ∀ᶠ m : ℕ in atTop, ∀ alpha : ℝ, alpha ≤ (4 : ℝ) / 5 →
      (sourceAlphaIntervalCount m alpha : ℝ≥0∞) *
          sourceProp45FourBranchError m ≤ sourceBetaCandidateTail d m := by
  have hrate := eventually_const_mul_log_add_one_sq_le_nat_rpow
    (c := 2 * d) (a := (8 : ℝ) / 25) (by positivity) (by norm_num)
      (by norm_num)
  have hpoly := (tendsto_add_atTop_nat 1).eventually
    (eventually_three_rpow_mul_exp_neg_log_sq_le
      (c := 2 * d) (b := (2 : ℝ)) (by positivity) (by norm_num))
  filter_upwards [hrate, hpoly, eventually_sourceIntervalIndex,
      eventually_ge_atTop 1] with m hrateM hpolyM hindices hm
  intro alpha hAlpha
  let L := sourceAlphaIntervalCount m alpha
  have hL : 1 ≤ L := by
    dsimp [L]
    unfold sourceAlphaIntervalCount
    omega
  have hLcut : L ≤ sourceIntervalCutoff m :=
    sourceAlphaIntervalCount_le_cutoff m hm hAlpha
  have hLindex : SourceIntervalIndex m L := hindices L hL hLcut
  have hwidth : 0 < sourceCellWidth m := sourceCellWidth_pos m hm
  have hLm : L ≤ m := by
    calc
      L ≤ L * sourceCellWidth m := Nat.le_mul_of_pos_right L hwidth
      _ ≤ 2 * L * sourceCellWidth m := by
        simpa only [mul_assoc] using
          (Nat.le_mul_of_pos_left (L * sourceCellWidth m) (by omega : 0 < 2))
      _ ≤ m := hLindex.2
  have hrateEq : sourceRate m = (m : ℝ) ^ ((8 : ℝ) / 25) := by
    rw [sourceRate, sourceRateExponent_eq]
  have hdom : 2 * d * Real.log ((m : ℝ) + 1) ^ 2 ≤ sourceRate m := by
    simpa only [hrateEq] using hrateM
  have hsqrtRate : sourceRate m ≤ Real.sqrt (m : ℝ) := by
    rw [hrateEq, Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hm)
      (by norm_num)
  have hsqrtExp : ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ))) ≤
      ENNReal.ofReal (Real.exp (-sourceRate m)) := by
    apply ENNReal.ofReal_le_ofReal
    exact Real.exp_le_exp.mpr (neg_le_neg hsqrtRate)
  let e : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-sourceRate m))
  have herror : sourceProp45FourBranchError m ≤ 6 * e := by
    rw [sourceProp45FourBranchError]
    change (e + ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ)))) + e +
        (e + ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ)))) + e ≤ 6 * e
    calc
      (e + ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ)))) + e +
          (e + ENNReal.ofReal (Real.exp (-Real.sqrt (m : ℝ)))) + e ≤
          (e + e) + e + (e + e) + e := by gcongr
      _ = 6 * e := by ring
  have hfactor : (L : ℝ) * 6 ≤
      3 * (((m + 1 : ℕ) : ℝ) ^ (2 : ℝ)) := by
    rw [Real.rpow_two]
    have hLcast : (L : ℝ) ≤ m := by exact_mod_cast hLm
    have hm0 : (0 : ℝ) ≤ m := by positivity
    norm_num only [Nat.cast_add, Nat.cast_one]
    nlinarith
  have hreal : (L : ℝ) * (6 * Real.exp (-sourceRate m)) ≤
      Real.exp (-d * Real.log ((m : ℝ) + 1) ^ 2) := by
    calc
      (L : ℝ) * (6 * Real.exp (-sourceRate m)) =
          ((L : ℝ) * 6) * Real.exp (-sourceRate m) := by ring
      _ ≤ (3 * (((m + 1 : ℕ) : ℝ) ^ (2 : ℝ))) *
          Real.exp (-(2 * d) * Real.log ((m : ℝ) + 1) ^ 2) := by
        apply mul_le_mul hfactor
        · apply Real.exp_le_exp.mpr
          nlinarith [hdom]
        · exact Real.exp_nonneg _
        · positivity
      _ ≤ Real.exp (-((2 * d) / 2) *
          Real.log ((m : ℝ) + 1) ^ 2) := by
        simpa only [Nat.cast_add, Nat.cast_one, add_comm] using hpolyM
      _ = Real.exp (-d * Real.log ((m : ℝ) + 1) ^ 2) := by ring_nf
  calc
    (sourceAlphaIntervalCount m alpha : ℝ≥0∞) *
        sourceProp45FourBranchError m ≤ (L : ℝ≥0∞) * (6 * e) := by
      dsimp only [L]
      gcongr
    _ = ENNReal.ofReal ((L : ℝ) *
        (6 * Real.exp (-sourceRate m))) := by
      dsimp [e]
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity)]
      norm_num
    _ ≤ ENNReal.ofReal
        (Real.exp (-d * Real.log ((m : ℝ) + 1) ^ 2)) :=
      ENNReal.ofReal_le_ofReal hreal
    _ = sourceBetaCandidateTail d m := rfl

/-- The checked capped-profile Proposition 4.8 theorem, in exactly the
ENNReal/shifted normalization required by the candidate tail.  This is a
fixed-profile statement; no stopped product law is assumed here. -/
theorem eventually_sourceCappedProfile_prop48_band_bound_shifted
    {ι : Type*} [Fintype ι] (c : ℕ) {cBase cTheta a d : ℝ}
    (hcBase : 0 < cBase) (hcTheta : 0 < cTheta) (ha : 0 < a)
    (hd : 0 < d)
    (hcompare : 4 * d ≤
      min cBase
        (imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c))) / 2) :
    ∀ᶠ m : ℕ in atTop, ∀ (alpha : ℝ) (profile capProfile : ι → ℕ)
      (mu : Measure (ι → ℕ)),
      kappaOne ≤ alpha → alpha ≤ (4 : ℝ) / 5 →
      (∀ x, profile x < m) →
      (∀ x, capProfile x = profile x) →
      mu = sourceCappedProfileMeasure m profile capProfile →
      mu.real (sourceProfileQEvent m 1 profile (Real.log (m : ℝ) ^ 2)) ≤
        Real.exp (-cBase * Real.log (m : ℝ) ^ 2) →
      (∀ l, 2 ≤ l → l ≤ sourceAlphaIntervalCount m alpha →
        mu.real (sourceProfileThetaBad c m l profile) ≤
          Real.exp (-cTheta * (m : ℝ) ^ a)) →
      mu (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor c) (sourceAlphaIntervalCount m alpha))) ≤
        sourceBetaCandidateTail d m := by
  have hProp48 := eventually_sourceCappedProfile_prop48_band_bound
    ( ι := ι) c hcBase hcTheta ha
  have hshift := eventually_prop48Rate_le_sourceBetaCandidateTail hd hcompare
  filter_upwards [hProp48, hshift] with m hm hshiftM
  intro alpha profile capProfile mu halpha hAlpha hprofile hwinning hLaw
    hbase hTheta
  have hreal := hm alpha profile capProfile mu halpha hAlpha hprofile
    hwinning hLaw hbase hTheta
  have hcapEq : sourceCappedProfileMeasure m profile capProfile =
      sourceTruncatedProfileMeasure m profile :=
    sourceCappedProfileMeasure_eq_truncated m profile capProfile hwinning
  letI (x : ι) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (profile x)) :=
    cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (profile x) (hprofile x))
  letI : IsProbabilityMeasure (sourceTruncatedProfileMeasure m profile) := by
    unfold sourceTruncatedProfileMeasure
    infer_instance
  have hfinite : mu (sourceProfileQEvent m
      (sourceAlphaIntervalCount m alpha) profile
      (geometricThreshold (Real.log (m : ℝ) ^ 2)
        (sourceLemma411GrowthFactor c)
        (sourceAlphaIntervalCount m alpha))) ≠ ∞ := by
    rw [hLaw, hcapEq]
    exact measure_ne_top _ _
  calc
    mu (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor c)
          (sourceAlphaIntervalCount m alpha))) =
        ENNReal.ofReal (mu.real (sourceProfileQEvent m
          (sourceAlphaIntervalCount m alpha) profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor c)
            (sourceAlphaIntervalCount m alpha)))) := by
      rw [measureReal_def, ENNReal.ofReal_toReal hfinite]
    _ ≤ ENNReal.ofReal
        (Real.exp (-(min cBase
          (imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c))) / 2) *
            Real.log (m : ℝ) ^ 2)) := ENNReal.ofReal_le_ofReal hreal
    _ ≤ sourceBetaCandidateTail d m := hshiftM

/-- All `m`-dependent hypotheses used by the proof of the capped-profile
Proposition 4.8 theorem.  Crucially, this record contains no coordinate
type, profile, event, measure, or probability estimate.  It exposes the
uniformity in the finite stopped coordinate type which is hidden by the
quantifier order of the original theorem. -/
structure SourceProp48NumericalAt
    (c m : ℕ) (cBase cTheta thetaPower : ℝ) : Prop where
  growth : SourceWindowGrowth c m
  intervalIndex : ∀ l, 1 ≤ l → l ≤ sourceIntervalCutoff m →
    SourceIntervalIndex m l
  m_pos : 1 ≤ m
  assembly : ∀ (q : ℕ → ℝ) (n : ℕ) (rho : ℝ),
    Real.log (m : ℝ) ^ 2 ≤ rho →
    (((n + 1 : ℕ) : ℝ) ≤ (m : ℝ) ^ (1 : ℝ)) →
    q 1 ≤ Real.exp (-min cBase
      (imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c))) *
        Real.log (m : ℝ) ^ 2) →
    (∀ z < n,
      q (z + 2) ≤ q (z + 1) +
        Real.exp (-min cBase
          (imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c))) *
            geometricThreshold rho (sourceLemma411GrowthFactor c) (z + 2)) +
        Real.exp (-cTheta * (m : ℝ) ^ thetaPower)) →
    q (n + 1) ≤ Real.exp (-(min cBase
      (imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c))) / 2) *
        Real.log (m : ℝ) ^ 2)

/-- The numerical good-`m` record holds eventually, uniformly in every
finite coordinate type and every stopped profile. -/
theorem eventually_sourceProp48NumericalAt
    (c : ℕ) {cBase cTheta thetaPower : ℝ}
    (hcBase : 0 < cBase) (hcTheta : 0 < cTheta)
    (hthetaPower : 0 < thetaPower) :
    ∀ᶠ m : ℕ in atTop,
      SourceProp48NumericalAt c m cBase cTheta thetaPower := by
  let r := imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c))
  let cAssembly := min cBase r
  let R := sourceLemma411GrowthFactor c
  have hr : 0 < r := imbalanceRate_pos (Real.one_le_exp (by positivity))
  have hcAssembly : 0 < cAssembly := lt_min hcBase hr
  have hR : 1 ≤ R := sourceLemma411GrowthFactor_one_le c
  have hassembly := eventually_hloz_lemma_4_11_assembly
    hcAssembly hcTheta hthetaPower (show (0 : ℝ) ≤ 1 by norm_num) hR
  filter_upwards [eventually_sourceWindowGrowth c,
    eventually_sourceIntervalIndex, hassembly, eventually_ge_atTop 1] with
      m hgrowth hindices hassemblyM hm
  refine ⟨hgrowth, hindices, hm, ?_⟩
  simpa only [cAssembly, r, R] using hassemblyM

/-- Pointwise version of the checked capped-profile Proposition 4.8
recursion.  Unlike the original eventual theorem, its numerical hypothesis
is independent of `ι`; hence it can be applied simultaneously to every
member of a countable stopped-atom family. -/
theorem sourceCappedProfile_prop48_band_bound_at
    {ι : Type*} [Fintype ι] {c m : ℕ}
    {cBase cTheta thetaPower : ℝ}
    (G : SourceProp48NumericalAt c m cBase cTheta thetaPower)
    (alpha : ℝ) (profile capProfile : ι → ℕ)
    (mu : Measure (ι → ℕ))
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hprofile : ∀ x, profile x < m)
    (hwinning : ∀ x, capProfile x = profile x)
    (hLaw : mu = sourceCappedProfileMeasure m profile capProfile)
    (hBase : mu.real
      (sourceProfileQEvent m 1 profile (Real.log (m : ℝ) ^ 2)) ≤
        Real.exp (-cBase * Real.log (m : ℝ) ^ 2))
    (hTheta : ∀ l, 2 ≤ l → l ≤ sourceAlphaIntervalCount m alpha →
      mu.real (sourceProfileThetaBad c m l profile) ≤
        Real.exp (-cTheta * (m : ℝ) ^ thetaPower)) :
    mu.real (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) profile
      (geometricThreshold (Real.log (m : ℝ) ^ 2)
        (sourceLemma411GrowthFactor c) (sourceAlphaIntervalCount m alpha))) ≤
      Real.exp (-(min cBase
        (imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c))) / 2) *
          Real.log (m : ℝ) ^ 2) := by
  let r := imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c))
  let cAssembly := min cBase r
  let R := sourceLemma411GrowthFactor c
  have hr : 0 < r := imbalanceRate_pos (Real.one_le_exp (by positivity))
  have hR : 1 ≤ R := sourceLemma411GrowthFactor_one_le c
  let L := sourceAlphaIntervalCount m alpha
  let rho := Real.log (m : ℝ) ^ 2
  let q : ℕ → ℝ := fun l ↦ mu.real
    (sourceProfileQEvent m l profile (geometricThreshold rho R l))
  have hL : 1 ≤ L := by
    dsimp [L]
    unfold sourceAlphaIntervalCount
    omega
  have hLcut : L ≤ sourceIntervalCutoff m :=
    sourceAlphaIntervalCount_le_cutoff m G.m_pos hAlpha
  have hLindex : SourceIntervalIndex m L :=
    G.intervalIndex L hL hLcut
  have hwidth : 0 < sourceCellWidth m :=
    sourceCellWidth_pos m G.m_pos
  have hLm : L ≤ m := by
    calc
      L ≤ L * sourceCellWidth m := Nat.le_mul_of_pos_right L hwidth
      _ ≤ 2 * L * sourceCellWidth m := by
        simpa only [mul_assoc] using
          (Nat.le_mul_of_pos_left (L * sourceCellWidth m) (by omega : 0 < 2))
      _ ≤ m := hLindex.2
  have hlevels : ((((L - 1) + 1 : ℕ) : ℝ) ≤ (m : ℝ) ^ (1 : ℝ)) := by
    rw [Nat.sub_add_cancel hL, Real.rpow_one]
    exact_mod_cast hLm
  have hrho : Real.log (m : ℝ) ^ 2 ≤ rho := le_rfl
  have hrho0 : 0 ≤ rho := sq_nonneg _
  have hqone : q 1 ≤
      Real.exp (-cAssembly * Real.log (m : ℝ) ^ 2) := by
    rw [show q 1 = mu.real
      (sourceProfileQEvent m 1 profile (Real.log (m : ℝ) ^ 2)) by
        simp [q, rho, geometricThreshold_one]]
    exact hBase.trans (Real.exp_le_exp.mpr (by
      have hcLe : cAssembly ≤ cBase := min_le_left _ _
      nlinarith [sq_nonneg (Real.log (m : ℝ))]))
  have hstep : ∀ z < L - 1,
      q (z + 2) ≤ q (z + 1) +
        Real.exp (-cAssembly * geometricThreshold rho R (z + 2)) +
        Real.exp (-cTheta * (m : ℝ) ^ thetaPower) := by
    intro z hz
    have hlevel : z + 2 ≤ L := by omega
    have hlevelCut : z + 2 ≤ sourceIntervalCutoff m := hlevel.trans hLcut
    have hindex := G.intervalIndex (z + 2) (by omega) hlevelCut
    have hthreshold : geometricThreshold rho R (z + 2) =
        2 * Real.exp (sourceAdjacentComparisonExponent c) *
          geometricThreshold rho R (z + 1) := by
      rw [geometricThreshold_succ rho R (show 1 ≤ z + 1 by omega)]
      rfl
    have hrec := sourceCappedProfile_one_step_recursion c m (z + 2)
      profile capProfile mu hprofile hwinning hLaw hindex G.growth (by omega)
      (hrho0.trans (geometricThreshold_le rho R hrho0 hR (by omega)))
      (le_of_eq hthreshold.symm)
      (hTheta (z + 2) (by omega) hlevel)
    have hweaken : Real.exp (-r * geometricThreshold rho R (z + 2)) ≤
        Real.exp (-cAssembly * geometricThreshold rho R (z + 2)) := by
      apply Real.exp_le_exp.mpr
      have ht0 := geometricThreshold_le rho R hrho0 hR
        (show 1 ≤ z + 2 by omega)
      have hcLe : cAssembly ≤ r := min_le_right _ _
      nlinarith
    dsimp [q, r] at hrec ⊢
    exact hrec.trans (by gcongr)
  have hfinal := G.assembly q (L - 1) rho hrho hlevels hqone hstep
  simpa only [q, L, R, cAssembly, rho, r, Nat.sub_add_cancel hL] using hfinal

/-- ENNReal form of the pointwise uniform theorem, with an arbitrary larger
tail.  This is the form consumed by the stopped-atom aggregation. -/
theorem sourceCappedProfile_prop48_band_bound_at_ennreal
    {ι : Type*} [Fintype ι] {c m : ℕ}
    {cBase cTheta thetaPower : ℝ}
    (G : SourceProp48NumericalAt c m cBase cTheta thetaPower)
    (alpha : ℝ) (profile capProfile : ι → ℕ)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hprofile : ∀ x, profile x < m)
    (hwinning : ∀ x, capProfile x = profile x)
    (hBase : (sourceCappedProfileMeasure m profile capProfile).real
      (sourceProfileQEvent m 1 profile (Real.log (m : ℝ) ^ 2)) ≤
        Real.exp (-cBase * Real.log (m : ℝ) ^ 2))
    (hTheta : ∀ l, 2 ≤ l → l ≤ sourceAlphaIntervalCount m alpha →
      (sourceCappedProfileMeasure m profile capProfile).real
        (sourceProfileThetaBad c m l profile) ≤
          Real.exp (-cTheta * (m : ℝ) ^ thetaPower))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c))) / 2) *
        Real.log (m : ℝ) ^ 2)) ≤ tail) :
    sourceCappedProfileMeasure m profile capProfile
      (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor c)
          (sourceAlphaIntervalCount m alpha))) ≤ tail := by
  let mu := sourceCappedProfileMeasure m profile capProfile
  have hreal := sourceCappedProfile_prop48_band_bound_at G alpha profile
    capProfile mu halpha hAlpha hprofile hwinning rfl hBase hTheta
  have hcapEq : sourceCappedProfileMeasure m profile capProfile =
      sourceTruncatedProfileMeasure m profile :=
    sourceCappedProfileMeasure_eq_truncated m profile capProfile hwinning
  letI (x : ι) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (profile x)) :=
    cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (profile x) (hprofile x))
  letI : IsProbabilityMeasure (sourceTruncatedProfileMeasure m profile) := by
    unfold sourceTruncatedProfileMeasure
    infer_instance
  let Q := sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) profile
    (geometricThreshold (Real.log (m : ℝ) ^ 2)
      (sourceLemma411GrowthFactor c) (sourceAlphaIntervalCount m alpha))
  have hfinite : sourceCappedProfileMeasure m profile capProfile Q ≠ ∞ := by
    rw [hcapEq]
    exact measure_ne_top _ _
  calc
    sourceCappedProfileMeasure m profile capProfile Q =
        ENNReal.ofReal
          ((sourceCappedProfileMeasure m profile capProfile).real Q) := by
      rw [measureReal_def, ENNReal.ofReal_toReal hfinite]
    _ ≤ ENNReal.ofReal (Real.exp (-(min cBase
        (imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c))) / 2) *
          Real.log (m : ℝ) ^ 2)) := ENNReal.ofReal_le_ofReal hreal
    _ ≤ tail := hshift

/-- Truncated-profile specialization of the pointwise Proposition 4.8
bound.  This is the form supplied by the canonical left-winner stopped atom,
so no cap/shape equality is exposed downstream. -/
theorem sourceTruncatedProfile_prop48_band_bound_at_ennreal
    {ι : Type*} [Fintype ι] {c m : ℕ}
    {cBase cTheta thetaPower : ℝ}
    (G : SourceProp48NumericalAt c m cBase cTheta thetaPower)
    (alpha : ℝ) (profile : ι → ℕ)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hprofile : ∀ x, profile x < m)
    (hBase : (sourceTruncatedProfileMeasure m profile).real
      (sourceProfileQEvent m 1 profile (Real.log (m : ℝ) ^ 2)) ≤
        Real.exp (-cBase * Real.log (m : ℝ) ^ 2))
    (hTheta : ∀ l, 2 ≤ l → l ≤ sourceAlphaIntervalCount m alpha →
      (sourceTruncatedProfileMeasure m profile).real
        (sourceProfileThetaBad c m l profile) ≤
          Real.exp (-cTheta * (m : ℝ) ^ thetaPower))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c))) / 2) *
        Real.log (m : ℝ) ^ 2)) ≤ tail) :
    sourceTruncatedProfileMeasure m profile
      (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor c)
          (sourceAlphaIntervalCount m alpha))) ≤ tail := by
  have hEq : sourceCappedProfileMeasure m profile profile =
      sourceTruncatedProfileMeasure m profile :=
    sourceCappedProfileMeasure_eq_truncated m profile profile fun _ ↦ rfl
  rw [← hEq] at hBase hTheta ⊢
  exact sourceCappedProfile_prop48_band_bound_at_ennreal G alpha profile
    profile halpha hAlpha hprofile (fun _ ↦ rfl) hBase hTheta tail hshift

/-! ### Removing the profile exception before the Proposition 4.8 recursion

The source proof does not need a conditional probability estimate for every
`Theta` event on every stopped atom.  Proposition 4.5 pays for those path
events globally.  On their complement, the deterministic one-step cover in
Proposition 4.8 contains only the preceding `Q` event and the categorical
imbalance event.  The next definitions and theorems isolate that exact
theta-free recursion. -/

/-- The union of the profile exceptions encountered through level `L` of
the Proposition 4.8 recursion.  Writing it as a finite `Fin L` union keeps
the event measurable without any additional hypotheses. -/
noncomputable def sourceProfileThetaUpTo {ι : Type*} [Fintype ι]
    (c m L : ℕ) (profile : ι → ℕ) : Set (ι → ℕ) :=
  ⋃ l : Fin L, sourceProfileThetaBad c m (l + 1) profile

lemma sourceProfileThetaBad_subset_thetaUpTo
    {ι : Type*} [Fintype ι] {c m L l : ℕ} {profile : ι → ℕ}
    (hl : 1 ≤ l) (hlL : l ≤ L) :
    sourceProfileThetaBad c m l profile ⊆
      sourceProfileThetaUpTo c m L profile := by
  intro lazy hlazy
  have hlt : l - 1 < L := by omega
  let j : Fin L := ⟨l - 1, hlt⟩
  apply Set.mem_iUnion.mpr
  refine ⟨j, ?_⟩
  have hj : (j : ℕ) + 1 = l := by
    dsimp [j]
    omega
  simpa only [hj] using hlazy

/-- One theta-free transition in the fixed-profile recursion. -/
theorem sourceProfile_good_one_step_cover
    {ι : Type*} [Fintype ι] (c m L l : ℕ) (profile : ι → ℕ)
    (D : Set (ι → ℕ))
    (hl : 2 ≤ l) (hlL : l ≤ L) (hfit : l * sourceCellWidth m ≤ m)
    {rhoPrev rhoCur : ℝ} (hrhoCur : 0 ≤ rhoCur)
    (hgrow : 2 * Real.exp (sourceAdjacentComparisonExponent c) * rhoPrev ≤
      rhoCur) :
    (sourceProfileQEvent m l profile rhoCur ∩ D) \
        sourceProfileThetaUpTo c m L profile ⊆
      ((sourceProfileQEvent m (l - 1) profile rhoPrev ∩ D) \
          sourceProfileThetaUpTo c m L profile) ∪
        sourceProfileImbalanceEvent c m l profile rhoCur := by
  intro lazy hlazy
  rcases sourceProfile_one_step_cover c m l profile hl hfit hrhoCur hgrow
      hlazy.1.1 with (hprev | htheta) | himbalance
  · exact Or.inl ⟨⟨hprev, hlazy.1.2⟩, hlazy.2⟩
  · exact (hlazy.2
      (sourceProfileThetaBad_subset_thetaUpTo (by omega) hlL htheta)).elim
  · exact Or.inr himbalance

/-- Probability recursion on the complement of every profile exception up
to the terminal level.  In contrast to
`sourceTruncatedProfile_one_step_recursion`, there is no probabilistic
`Theta` premise or additive theta error. -/
theorem sourceTruncatedProfile_good_one_step_recursion
    {ι : Type*} [Fintype ι] (c m L l : ℕ) (profile : ι → ℕ)
    (D : Set (ι → ℕ))
    (hprofile : ∀ x, profile x < m)
    (hindex : SourceIntervalIndex m l) (hgrowth : SourceWindowGrowth c m)
    (hl : 2 ≤ l) (hlL : l ≤ L) {rhoPrev rhoCur : ℝ}
    (hrhoCur : 0 ≤ rhoCur)
    (hgrow : 2 * Real.exp (sourceAdjacentComparisonExponent c) * rhoPrev ≤
      rhoCur) :
    (sourceTruncatedProfileMeasure m profile).real
        ((sourceProfileQEvent m l profile rhoCur ∩ D) \
          sourceProfileThetaUpTo c m L profile) ≤
      (sourceTruncatedProfileMeasure m profile).real
          ((sourceProfileQEvent m (l - 1) profile rhoPrev ∩ D) \
            sourceProfileThetaUpTo c m L profile) +
        Real.exp (-imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent c)) * rhoCur) := by
  classical
  letI (x : ι) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (profile x)) :=
    cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (profile x) (hprofile x))
  letI : IsProbabilityMeasure (sourceTruncatedProfileMeasure m profile) := by
    unfold sourceTruncatedProfileMeasure
    infer_instance
  have hfit : l * sourceCellWidth m ≤ m := by
    calc
      l * sourceCellWidth m ≤ 2 * l * sourceCellWidth m := by
        exact Nat.mul_le_mul_right (sourceCellWidth m) (by omega)
      _ ≤ m := hindex.2
  have hcover := sourceProfile_good_one_step_cover c m L l profile D hl hlL
    hfit hrhoCur hgrow
  have himbalance := sourceTruncatedProfileImbalance_real_le_threshold
    c m l profile hprofile hl hindex hgrowth rhoCur
  calc
    (sourceTruncatedProfileMeasure m profile).real
        ((sourceProfileQEvent m l profile rhoCur ∩ D) \
          sourceProfileThetaUpTo c m L profile) ≤
      (sourceTruncatedProfileMeasure m profile).real
        (((sourceProfileQEvent m (l - 1) profile rhoPrev ∩ D) \
            sourceProfileThetaUpTo c m L profile) ∪
          sourceProfileImbalanceEvent c m l profile rhoCur) :=
      measureReal_mono hcover (measure_ne_top _ _)
    _ ≤ (sourceTruncatedProfileMeasure m profile).real
          ((sourceProfileQEvent m (l - 1) profile rhoPrev ∩ D) \
            sourceProfileThetaUpTo c m L profile) +
        (sourceTruncatedProfileMeasure m profile).real
          (sourceProfileImbalanceEvent c m l profile rhoCur) :=
      measureReal_union_le _ _
    _ ≤ (sourceTruncatedProfileMeasure m profile).real
          ((sourceProfileQEvent m (l - 1) profile rhoPrev ∩ D) \
            sourceProfileThetaUpTo c m L profile) +
        Real.exp (-imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent c)) * rhoCur) := by
      gcongr

/-- Pointwise Proposition 4.8 recursion after all profile exceptions have
been removed.  The numerical record is reused with harmless dummy theta
parameters; its extra positive summand only weakens the theta-free
recurrence. -/
theorem sourceTruncatedProfile_prop48_good_band_bound_at
    {ι : Type*} [Fintype ι] {c m : ℕ} {cBase : ℝ}
    (G : SourceProp48NumericalAt c m cBase 1 1)
    (alpha : ℝ) (profile : ι → ℕ) (D : Set (ι → ℕ))
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hprofile : ∀ x, profile x < m)
    (hBase : (sourceTruncatedProfileMeasure m profile).real
      ((sourceProfileQEvent m 1 profile (Real.log (m : ℝ) ^ 2) ∩ D) \
        sourceProfileThetaUpTo c m (sourceAlphaIntervalCount m alpha)
          profile) ≤
        Real.exp (-cBase * Real.log (m : ℝ) ^ 2)) :
    (sourceTruncatedProfileMeasure m profile).real
      ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor c)
            (sourceAlphaIntervalCount m alpha)) ∩ D) \
        sourceProfileThetaUpTo c m (sourceAlphaIntervalCount m alpha)
          profile) ≤
      Real.exp (-(min cBase
        (imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c))) / 2) *
          Real.log (m : ℝ) ^ 2) := by
  let r := imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c))
  let cAssembly := min cBase r
  let R := sourceLemma411GrowthFactor c
  let L := sourceAlphaIntervalCount m alpha
  let rho := Real.log (m : ℝ) ^ 2
  let theta := sourceProfileThetaUpTo c m L profile
  let q : ℕ → ℝ := fun l ↦ (sourceTruncatedProfileMeasure m profile).real
    ((sourceProfileQEvent m l profile (geometricThreshold rho R l) ∩ D) \
      theta)
  have hR : 1 ≤ R := sourceLemma411GrowthFactor_one_le c
  have hL : 1 ≤ L := by
    dsimp [L]
    unfold sourceAlphaIntervalCount
    omega
  have hLcut : L ≤ sourceIntervalCutoff m :=
    sourceAlphaIntervalCount_le_cutoff m G.m_pos hAlpha
  have hLindex : SourceIntervalIndex m L :=
    G.intervalIndex L hL hLcut
  have hwidth : 0 < sourceCellWidth m :=
    sourceCellWidth_pos m G.m_pos
  have hLm : L ≤ m := by
    calc
      L ≤ L * sourceCellWidth m := Nat.le_mul_of_pos_right L hwidth
      _ ≤ 2 * L * sourceCellWidth m := by
        simpa only [mul_assoc] using
          (Nat.le_mul_of_pos_left (L * sourceCellWidth m) (by omega : 0 < 2))
      _ ≤ m := hLindex.2
  have hlevels : ((((L - 1) + 1 : ℕ) : ℝ) ≤ (m : ℝ) ^ (1 : ℝ)) := by
    rw [Nat.sub_add_cancel hL, Real.rpow_one]
    exact_mod_cast hLm
  have hrho : Real.log (m : ℝ) ^ 2 ≤ rho := le_rfl
  have hrho0 : 0 ≤ rho := sq_nonneg _
  have hqone : q 1 ≤
      Real.exp (-cAssembly * Real.log (m : ℝ) ^ 2) := by
    rw [show q 1 = (sourceTruncatedProfileMeasure m profile).real
      ((sourceProfileQEvent m 1 profile (Real.log (m : ℝ) ^ 2) ∩ D) \
        sourceProfileThetaUpTo c m L profile) by
        simp [q, rho, R, theta, geometricThreshold_one]]
    exact hBase.trans (Real.exp_le_exp.mpr (by
      have hcLe : cAssembly ≤ cBase := min_le_left _ _
      nlinarith [sq_nonneg (Real.log (m : ℝ))]))
  have hstep : ∀ z < L - 1,
      q (z + 2) ≤ q (z + 1) +
        Real.exp (-cAssembly * geometricThreshold rho R (z + 2)) +
        Real.exp (-(1 : ℝ) * (m : ℝ) ^ (1 : ℝ)) := by
    intro z hz
    have hlevel : z + 2 ≤ L := by omega
    have hlevelCut : z + 2 ≤ sourceIntervalCutoff m := hlevel.trans hLcut
    have hindex := G.intervalIndex (z + 2) (by omega) hlevelCut
    have hthreshold : geometricThreshold rho R (z + 2) =
        2 * Real.exp (sourceAdjacentComparisonExponent c) *
          geometricThreshold rho R (z + 1) := by
      rw [geometricThreshold_succ rho R (show 1 ≤ z + 1 by omega)]
      rfl
    have hrec := sourceTruncatedProfile_good_one_step_recursion
      c m L (z + 2) profile D hprofile hindex G.growth (by omega) hlevel
      (hrho0.trans (geometricThreshold_le rho R hrho0 hR (by omega)))
      (le_of_eq hthreshold.symm)
    have hweaken :
        Real.exp (-r * geometricThreshold rho R (z + 2)) ≤
          Real.exp (-cAssembly * geometricThreshold rho R (z + 2)) := by
      apply Real.exp_le_exp.mpr
      have ht0 := geometricThreshold_le rho R hrho0 hR
        (show 1 ≤ z + 2 by omega)
      have hcLe : cAssembly ≤ r := min_le_right _ _
      nlinarith
    dsimp [q, theta, r] at hrec ⊢
    exact hrec.trans (by
      have hdummy : 0 ≤ Real.exp (-(1 : ℝ) * (m : ℝ) ^ (1 : ℝ)) :=
        Real.exp_nonneg _
      nlinarith)
  have hfinal := G.assembly q (L - 1) rho hrho hlevels hqone hstep
  simpa only [q, L, R, cAssembly, rho, r, theta,
    Nat.sub_add_cancel hL] using hfinal

/-- ENNReal form of the theta-free fixed-profile Proposition 4.8 bound. -/
theorem sourceTruncatedProfile_prop48_good_band_bound_at_ennreal
    {ι : Type*} [Fintype ι] {c m : ℕ} {cBase : ℝ}
    (G : SourceProp48NumericalAt c m cBase 1 1)
    (alpha : ℝ) (profile : ι → ℕ) (D : Set (ι → ℕ))
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hprofile : ∀ x, profile x < m)
    (hBase : (sourceTruncatedProfileMeasure m profile).real
      ((sourceProfileQEvent m 1 profile (Real.log (m : ℝ) ^ 2) ∩ D) \
        sourceProfileThetaUpTo c m (sourceAlphaIntervalCount m alpha)
          profile) ≤
        Real.exp (-cBase * Real.log (m : ℝ) ^ 2))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c))) / 2) *
        Real.log (m : ℝ) ^ 2)) ≤ tail) :
    sourceTruncatedProfileMeasure m profile
      ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor c)
            (sourceAlphaIntervalCount m alpha)) ∩ D) \
        sourceProfileThetaUpTo c m (sourceAlphaIntervalCount m alpha)
          profile) ≤ tail := by
  classical
  letI (x : ι) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (profile x)) :=
    cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (profile x) (hprofile x))
  letI : IsProbabilityMeasure (sourceTruncatedProfileMeasure m profile) := by
    unfold sourceTruncatedProfileMeasure
    infer_instance
  let Q := (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) profile
      (geometricThreshold (Real.log (m : ℝ) ^ 2)
        (sourceLemma411GrowthFactor c) (sourceAlphaIntervalCount m alpha)) ∩ D) \
    sourceProfileThetaUpTo c m (sourceAlphaIntervalCount m alpha) profile
  have hreal := sourceTruncatedProfile_prop48_good_band_bound_at G alpha
    profile D halpha hAlpha hprofile hBase
  calc
    sourceTruncatedProfileMeasure m profile Q =
        ENNReal.ofReal ((sourceTruncatedProfileMeasure m profile).real Q) := by
      rw [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
    _ ≤ ENNReal.ofReal (Real.exp (-(min cBase
        (imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c))) / 2) *
          Real.log (m : ℝ) ^ 2)) := ENNReal.ofReal_le_ofReal hreal
    _ ≤ tail := hshift

/-- Proposition 4.8 with its first-band estimate supplied by the literal
deleted-path switch used in equation (4.47).

The path-switch branch may be stated at any weaker threshold `rho`.  Once
`rho ≤ log(m)^2`, its fixed-profile bound controls the first band required
by the adjacent-band recursion.  Thus the later recursion does not require
a second same-history categorical package. -/
theorem
    stoppedEquation447PathWitnessBranchAtom_prop48_good_band_bound_at_ennreal
    {cWindow m : ℕ} {c cBase alpha rho : ℝ}
    {failure : Set (ℕ → Site)}
    (A : StoppedEquation447PathWitnessBranchAtom
      cWindow m c failure rho)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hc : 0 < c)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hrho : rho ≤ Real.log (m : ℝ) ^ 2)
    (hbaseAbsorb :
      4 * (Real.exp (-c * rho) * (1 - Real.exp (-c))⁻¹) ≤
        Real.exp (-cBase * Real.log (m : ℝ) ^ 2))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
        Real.log (m : ℝ) ^ 2)) ≤ tail) :
    let _ : Fintype A.Coord := A.coordFintype
    sourceTruncatedProfileMeasure m A.profile
      ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) A.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha)) ∩ A.D) \
        sourceProfileThetaUpTo cWindow m
          (sourceAlphaIntervalCount m alpha) A.profile) ≤ tail := by
  letI : Fintype A.Coord := A.coordFintype
  letI (x : A.Coord) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (A.profile x)) :=
    cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (A.profile x) (A.profile_lt x))
  letI : IsProbabilityMeasure
      (sourceTruncatedProfileMeasure m A.profile) := by
    unfold sourceTruncatedProfileMeasure
    infer_instance
  let L := sourceAlphaIntervalCount m alpha
  have hL : 1 ≤ L := by
    dsimp [L]
    unfold sourceAlphaIntervalCount
    omega
  have hpathBase :=
    stoppedEquation447PathWitnessBranchAtom_profile_good_base_bound A hc
  have hsubset :
      ((sourceProfileQEvent m 1 A.profile (Real.log (m : ℝ) ^ 2) ∩ A.D) \
          sourceProfileThetaUpTo cWindow m L A.profile) ⊆
        ((sourceProfileQEvent m 1 A.profile rho ∩ A.D) \
          sourceProfileThetaBad cWindow m 1 A.profile) := by
    intro lazy hlazy
    refine ⟨⟨⟨hlazy.1.1.1, ?_⟩, hlazy.1.2⟩, ?_⟩
    · exact lt_of_le_of_lt hrho hlazy.1.1.2
    · intro htheta
      exact hlazy.2
        (sourceProfileThetaBad_subset_thetaUpTo (l := 1)
          (by omega) hL htheta)
  have hbase :
      (sourceTruncatedProfileMeasure m A.profile).real
          ((sourceProfileQEvent m 1 A.profile (Real.log (m : ℝ) ^ 2) ∩ A.D) \
            sourceProfileThetaUpTo cWindow m L A.profile) ≤
        Real.exp (-cBase * Real.log (m : ℝ) ^ 2) := by
    exact (measureReal_mono hsubset).trans (hpathBase.trans hbaseAbsorb)
  simpa only [L] using
    sourceTruncatedProfile_prop48_good_band_bound_at_ennreal
      G alpha A.profile A.D halpha hAlpha A.profile_lt hbase tail hshift

/-- Equation (4.47) supplies the sole base estimate needed by the theta-free
Proposition 4.8 recursion.  All higher profile exceptions have already been
removed, so no per-level probability estimate remains in this interface. -/
theorem stoppedEquation447BranchAtom_prop48_good_band_bound_at_ennreal
    {c m : ℕ} {C cBase alpha : ℝ} {failure : Set (ℕ → Site)}
    (A : StoppedEquation447BranchAtom c m C failure
      (Real.log (m : ℝ) ^ 2))
    (G : SourceProp48NumericalAt c m cBase 1 1)
    (hC : 0 < C)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hbaseAbsorb :
      let d := Real.log ((C + 1) / C)
      let K := (1 - Real.exp (-d))⁻¹
      4 * (Real.exp (-d *
          (Nat.ceil (Real.log (m : ℝ) ^ 2) : ℝ)) * K) ≤
        Real.exp (-(cBase * Real.log (m : ℝ) ^ 2)))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate (Real.exp (sourceAdjacentComparisonExponent c))) / 2) *
        Real.log (m : ℝ) ^ 2)) ≤ tail) :
    let _ : Fintype A.Coord := A.coordFintype
    sourceTruncatedProfileMeasure m A.profile
      ((sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) A.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor c)
            (sourceAlphaIntervalCount m alpha)) ∩ A.D) \
        sourceProfileThetaUpTo c m (sourceAlphaIntervalCount m alpha)
          A.profile) ≤ tail := by
  letI : Fintype A.Coord := A.coordFintype
  letI (x : A.Coord) : IsProbabilityMeasure
      (sourceTruncatedNegBinMeasure m (A.profile x)) :=
    cond_isProbabilityMeasure
      (negBinMeasure_sourceBelowSet_ne_zero m (A.profile x) (A.profile_lt x))
  letI : IsProbabilityMeasure
      (sourceTruncatedProfileMeasure m A.profile) := by
    unfold sourceTruncatedProfileMeasure
    infer_instance
  let L := sourceAlphaIntervalCount m alpha
  have hL : 1 ≤ L := by
    dsimp [L]
    unfold sourceAlphaIntervalCount
    omega
  have hbaseOne :
      (sourceTruncatedProfileMeasure m A.profile).real
          ((sourceProfileQEvent m 1 A.profile (Real.log (m : ℝ) ^ 2) ∩ A.D) \
            sourceProfileThetaBad c m 1 A.profile) ≤
        Real.exp (-cBase * Real.log (m : ℝ) ^ 2) := by
    simpa only [neg_mul] using
      (stoppedEquation447BranchAtom_profile_good_base_bound_of_absorb
        A hC hbaseAbsorb)
  have hsubset :
      ((sourceProfileQEvent m 1 A.profile (Real.log (m : ℝ) ^ 2) ∩ A.D) \
          sourceProfileThetaUpTo c m L A.profile) ⊆
        ((sourceProfileQEvent m 1 A.profile (Real.log (m : ℝ) ^ 2) ∩ A.D) \
          sourceProfileThetaBad c m 1 A.profile) := by
    intro lazy hlazy
    refine ⟨hlazy.1, ?_⟩
    intro htheta
    exact hlazy.2
      (sourceProfileThetaBad_subset_thetaUpTo (l := 1) (by omega) hL htheta)
  have hbase :
      (sourceTruncatedProfileMeasure m A.profile).real
          ((sourceProfileQEvent m 1 A.profile (Real.log (m : ℝ) ^ 2) ∩ A.D) \
            sourceProfileThetaUpTo c m L A.profile) ≤
        Real.exp (-cBase * Real.log (m : ℝ) ^ 2) :=
    (measureReal_mono hsubset (measure_ne_top _ _)).trans hbaseOne
  exact sourceTruncatedProfile_prop48_good_band_bound_at_ennreal
    G alpha A.profile A.D halpha hAlpha A.profile_lt
      (by simpa only [L] using hbase) tail hshift

/-- Transport a theta-free fixed-profile estimate back to one stopped path
atom.  This is deliberately generic in the stopped construction: the four
horizontal parity/winner laws and the two column laws all instantiate the
same statement with their already-checked map law.  The profile-exception
pullback is required only on `failure ∩ atom`, which is the exact set used
below; asking for it on the whole coarse atom would incorrectly force the
stage history on paths outside the candidate failure. -/
theorem stoppedProfileGoodEvent_local_bound
    {ι : Type*} [Fintype ι] {m : ℕ}
    (profile : ι → ℕ)
    (atom failure thetaPath : Set (ℕ → Site))
    (statistic : (ℕ → Site) → (ι → ℕ) × Direction)
    (Q theta : Set (ι → ℕ))
    (hmeasurable : Measurable statistic)
    (hmap : (simpleRandomWalkLaw.restrict atom).map statistic =
      simpleRandomWalkLaw atom •
        ((sourceTruncatedProfileMeasure m profile).prod directionLaw))
    (hfailure : failure ∩ atom ⊆ statistic ⁻¹'
      (Q ×ˢ (Set.univ : Set Direction)))
    (htheta : (failure ∩ atom) ∩ statistic ⁻¹'
      (theta ×ˢ (Set.univ : Set Direction)) ⊆ thetaPath)
    (tail : ℝ≥0∞)
    (hgood : sourceTruncatedProfileMeasure m profile (Q \ theta) ≤ tail) :
    simpleRandomWalkLaw ((failure \ thetaPath) ∩ atom) ≤
      tail * simpleRandomWalkLaw atom := by
  let B : Set ((ι → ℕ) × Direction) :=
    (Q \ theta) ×ˢ (Set.univ : Set Direction)
  have hB : MeasurableSet B := MeasurableSet.of_discrete
  have hprod :
      (sourceTruncatedProfileMeasure m profile).prod directionLaw B =
        sourceTruncatedProfileMeasure m profile (Q \ theta) := by
    dsimp [B]
    rw [Measure.prod_prod, measure_univ, mul_one]
  have hrestricted :
      simpleRandomWalkLaw (atom ∩ statistic ⁻¹' B) =
        simpleRandomWalkLaw atom *
          sourceTruncatedProfileMeasure m profile (Q \ theta) := by
    have hmeasure := congrArg
      (fun mu : Measure ((ι → ℕ) × Direction) ↦ mu B) hmap
    rw [Measure.map_apply hmeasurable hB,
      Measure.restrict_apply (hB.preimage hmeasurable),
      Measure.smul_apply, smul_eq_mul, hprod] at hmeasure
    simpa only [Set.inter_comm] using hmeasure
  have hsubset : (failure \ thetaPath) ∩ atom ⊆
      atom ∩ statistic ⁻¹' B := by
    intro path hpath
    have hQ := hfailure ⟨hpath.1.1, hpath.2⟩
    refine ⟨hpath.2, ⟨⟨hQ.1, ?_⟩, hQ.2⟩⟩
    intro hthetaLazy
    exact hpath.1.2
      (htheta ⟨⟨hpath.1.1, hpath.2⟩, hthetaLazy, hQ.2⟩)
  calc
    simpleRandomWalkLaw ((failure \ thetaPath) ∩ atom) ≤
        simpleRandomWalkLaw (atom ∩ statistic ⁻¹' B) := measure_mono hsubset
    _ = simpleRandomWalkLaw atom *
        sourceTruncatedProfileMeasure m profile (Q \ theta) := hrestricted
    _ ≤ simpleRandomWalkLaw atom * tail := by gcongr
    _ = tail * simpleRandomWalkLaw atom := mul_comm _ _

/-- Transport the changed-path fixed-profile bound through the checked
stopped map law.  The target failure and final path-space `Theta` event may
be narrower than the equation-(4.47) branch; only their two deterministic
preimage inclusions are required. -/
theorem stoppedEquation447PathWitnessBranchAtom_prop48_good_band_local_bound
    {cWindow m : ℕ} {c cBase alpha rho : ℝ}
    {branchFailure failure thetaPath : Set (ℕ → Site)}
    (A : StoppedEquation447PathWitnessBranchAtom
      cWindow m c branchFailure rho)
    (G : SourceProp48NumericalAt cWindow m cBase 1 1)
    (hc : 0 < c)
    (halpha : kappaOne ≤ alpha) (hAlpha : alpha ≤ (4 : ℝ) / 5)
    (hrho : rho ≤ Real.log (m : ℝ) ^ 2)
    (hfailure : failure ∩ A.pathAtom ⊆
      (fun s ↦ (A.lazyVector s, A.nextDirection s)) ⁻¹'
        (((@sourceProfileQEvent A.Coord A.coordFintype m
            (sourceAlphaIntervalCount m alpha) A.profile
            (geometricThreshold (Real.log (m : ℝ) ^ 2)
              (sourceLemma411GrowthFactor cWindow)
              (sourceAlphaIntervalCount m alpha)) ∩ A.D)) ×ˢ
          (Set.univ : Set Direction)))
    (htheta : (failure ∩ A.pathAtom) ∩
      (fun s ↦ (A.lazyVector s, A.nextDirection s)) ⁻¹'
        ((@sourceProfileThetaUpTo A.Coord A.coordFintype cWindow m
            (sourceAlphaIntervalCount m alpha) A.profile) ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPath)
    (hbaseAbsorb :
      4 * (Real.exp (-c * rho) * (1 - Real.exp (-c))⁻¹) ≤
        Real.exp (-cBase * Real.log (m : ℝ) ^ 2))
    (tail : ℝ≥0∞)
    (hshift : ENNReal.ofReal (Real.exp (-(min cBase
      (imbalanceRate (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2) *
        Real.log (m : ℝ) ^ 2)) ≤ tail) :
    simpleRandomWalkLaw ((failure \ thetaPath) ∩ A.pathAtom) ≤
      tail * simpleRandomWalkLaw A.pathAtom := by
  letI : Fintype A.Coord := A.coordFintype
  have hgood :=
    stoppedEquation447PathWitnessBranchAtom_prop48_good_band_bound_at_ennreal
      A G hc halpha hAlpha hrho hbaseAbsorb tail hshift
  apply stoppedProfileGoodEvent_local_bound A.profile A.pathAtom failure
    thetaPath (fun s ↦ (A.lazyVector s, A.nextDirection s))
    (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) A.profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor cWindow)
          (sourceAlphaIntervalCount m alpha)) ∩ A.D)
    (sourceProfileThetaUpTo cWindow m
      (sourceAlphaIntervalCount m alpha) A.profile)
    (A.measurable_lazyVector.prodMk A.measurable_nextDirection)
    A.map_law hfailure htheta tail
  exact hgood

/-- Add back a path-space exceptional event after applying the theta-free
fixed-profile estimate.  This elementary wrapper is useful because the
source Proposition 4.5 estimates the exceptional event on path space,
whereas Proposition 4.8 is run under the fixed-profile product law. -/
theorem stoppedProfileEvent_local_bound_with_theta
    {ι : Type*} [Fintype ι] {m : ℕ}
    (profile : ι → ℕ)
    (atom failure thetaPath : Set (ℕ → Site))
    (statistic : (ℕ → Site) → (ι → ℕ) × Direction)
    (Q theta : Set (ι → ℕ))
    (hmeasurable : Measurable statistic)
    (hmap : (simpleRandomWalkLaw.restrict atom).map statistic =
      simpleRandomWalkLaw atom •
        ((sourceTruncatedProfileMeasure m profile).prod directionLaw))
    (hfailure : failure ∩ atom ⊆ statistic ⁻¹'
      (Q ×ˢ (Set.univ : Set Direction)))
    (htheta : (failure ∩ atom) ∩ statistic ⁻¹'
      (theta ×ˢ (Set.univ : Set Direction)) ⊆ thetaPath)
    (goodTail thetaTail : ℝ≥0∞)
    (hgood : sourceTruncatedProfileMeasure m profile (Q \ theta) ≤ goodTail)
    (hthetaPath : simpleRandomWalkLaw (thetaPath ∩ atom) ≤
      thetaTail * simpleRandomWalkLaw atom) :
    simpleRandomWalkLaw (failure ∩ atom) ≤
      (goodTail + thetaTail) * simpleRandomWalkLaw atom := by
  have hsplit : failure ∩ atom ⊆
      ((failure \ thetaPath) ∩ atom) ∪ (thetaPath ∩ atom) := by
    intro path hpath
    by_cases hpathTheta : path ∈ thetaPath
    · exact Or.inr ⟨hpathTheta, hpath.2⟩
    · exact Or.inl ⟨⟨hpath.1, hpathTheta⟩, hpath.2⟩
  have hgoodPath := stoppedProfileGoodEvent_local_bound profile atom failure
    thetaPath statistic Q theta hmeasurable hmap hfailure htheta goodTail hgood
  calc
    simpleRandomWalkLaw (failure ∩ atom) ≤
        simpleRandomWalkLaw
          (((failure \ thetaPath) ∩ atom) ∪ (thetaPath ∩ atom)) :=
      measure_mono hsplit
    _ ≤ simpleRandomWalkLaw ((failure \ thetaPath) ∩ atom) +
        simpleRandomWalkLaw (thetaPath ∩ atom) := measure_union_le _ _
    _ ≤ goodTail * simpleRandomWalkLaw atom +
        thetaTail * simpleRandomWalkLaw atom := add_le_add hgoodPath hthetaPath
    _ = (goodTail + thetaTail) * simpleRandomWalkLaw atom := by
      rw [add_mul]

/-- A finite family of source Proposition-4.5 interval exceptions costs
exactly its cardinality.  This is the path-space union bound needed for the
successive interval recursion in Proposition 4.8. -/
theorem measure_iUnion_fin_inter_atom_le
    {L : ℕ} (atom : Set (ℕ → Site))
    (thetaPath : Fin L → Set (ℕ → Site)) (thetaTail : ℝ≥0∞)
    (hband : ∀ l, simpleRandomWalkLaw (thetaPath l ∩ atom) ≤
      thetaTail * simpleRandomWalkLaw atom) :
    simpleRandomWalkLaw ((⋃ l, thetaPath l) ∩ atom) ≤
      (L : ℝ≥0∞) * thetaTail * simpleRandomWalkLaw atom := by
  have hset : ((⋃ l, thetaPath l) ∩ atom) =
      ⋃ l, thetaPath l ∩ atom := by
    ext path
    simp only [Set.mem_inter_iff, Set.mem_iUnion]
    aesop
  rw [hset]
  calc
    simpleRandomWalkLaw (⋃ l, thetaPath l ∩ atom) ≤
        ∑' l : Fin L, simpleRandomWalkLaw (thetaPath l ∩ atom) :=
      measure_iUnion_le _
    _ ≤ ∑' _l : Fin L, thetaTail * simpleRandomWalkLaw atom := by
      exact ENNReal.tsum_le_tsum hband
    _ = (L : ℝ≥0∞) * thetaTail * simpleRandomWalkLaw atom := by
      simp [mul_assoc]

/-- Correct global aggregation order for recursive Proposition-4.5 bands.

The untruncated negative-binomial estimate is first applied on a coarse
external-profile partition, producing one global path event `thetaPath l`
for each recursive level.  The stopped atoms are used only for the
theta-free truncated-product estimate.  In particular, this theorem never
conditions an untruncated holding law on a stopped atom. -/
theorem stoppedProfileEvent_global_bound_of_banded_theta
    {L : ℕ} (target : Set (ℕ → Site))
    (atom : ℕ → Set (ℕ → Site))
    (thetaPath : Fin L → Set (ℕ → Site))
    (goodTail thetaTail : ℝ≥0∞)
    (cover : target ⊆ ⋃ n, atom n)
    (pairwise_disjoint : Pairwise fun n l ↦ Disjoint (atom n) (atom l))
    (measurable_atom : ∀ n, MeasurableSet (atom n))
    (local_good : ∀ n,
      simpleRandomWalkLaw
          ((target \ (⋃ l, thetaPath l)) ∩ atom n) ≤
        goodTail * simpleRandomWalkLaw (atom n))
    (band_bound : ∀ l,
      simpleRandomWalkLaw (thetaPath l) ≤ thetaTail) :
    simpleRandomWalkLaw target ≤
      goodTail + (L : ℝ≥0∞) * thetaTail := by
  let thetaUnion : Set (ℕ → Site) := ⋃ l, thetaPath l
  have hgood : simpleRandomWalkLaw (target \ thetaUnion) ≤ goodTail := by
    apply fixed_cardinality_of_disjoint_path_witnesses simpleRandomWalkLaw
      (target \ thetaUnion)
      (fun n ↦ (target \ thetaUnion) ∩ atom n) atom goodTail
    · intro path hpath
      rcases Set.mem_iUnion.mp (cover hpath.1) with ⟨n, hn⟩
      exact Set.mem_iUnion.mpr ⟨n, hpath, hn⟩
    · simpa only [thetaUnion] using local_good
    · exact pairwise_disjoint
    · exact measurable_atom
  have htheta : simpleRandomWalkLaw thetaUnion ≤
      (L : ℝ≥0∞) * thetaTail := by
    dsimp [thetaUnion]
    calc
      simpleRandomWalkLaw (⋃ l, thetaPath l) ≤
          ∑' l : Fin L, simpleRandomWalkLaw (thetaPath l) :=
        measure_iUnion_le _
      _ ≤ ∑' _l : Fin L, thetaTail := ENNReal.tsum_le_tsum band_bound
      _ = (L : ℝ≥0∞) * thetaTail := by simp
  have hsplit : target ⊆ (target \ thetaUnion) ∪ thetaUnion := by
    intro path hpath
    by_cases hthetaPath : path ∈ thetaUnion
    · exact Or.inr hthetaPath
    · exact Or.inl ⟨hpath, hthetaPath⟩
  calc
    simpleRandomWalkLaw target ≤
        simpleRandomWalkLaw ((target \ thetaUnion) ∪ thetaUnion) :=
      measure_mono hsplit
    _ ≤ simpleRandomWalkLaw (target \ thetaUnion) +
        simpleRandomWalkLaw thetaUnion := measure_union_le _ _
    _ ≤ goodTail + (L : ℝ≥0∞) * thetaTail := add_le_add hgood htheta

/-- Strong atom-conditioned banded version of the stopped-profile transport.

`sourceProfileThetaUpTo` is a union over all interval levels used by the
Proposition-4.8 recursion.  Consequently its pullback is matched here to a
separate path event at every level.  In particular, this theorem does not
identify those lower-level exceptions with the single top-band
`stoppedThetaEvent`.  Unlike
`stoppedProfileEvent_global_bound_of_banded_theta`, this theorem assumes a
relative band estimate under each stopped atom and is therefore not the
literal source connector. -/
theorem stoppedProfileGoodEvent_local_bound_of_banded_theta
    {ι : Type*} [Fintype ι] {c m L : ℕ}
    (profile : ι → ℕ)
    (atom failure : Set (ℕ → Site))
    (statistic : (ℕ → Site) → (ι → ℕ) × Direction)
    (Q : Set (ι → ℕ))
    (thetaPath : Fin L → Set (ℕ → Site))
    (hmeasurable : Measurable statistic)
    (hmap : (simpleRandomWalkLaw.restrict atom).map statistic =
      simpleRandomWalkLaw atom •
        ((sourceTruncatedProfileMeasure m profile).prod directionLaw))
    (hfailure : failure ∩ atom ⊆ statistic ⁻¹'
      (Q ×ˢ (Set.univ : Set Direction)))
    (htheta : ∀ l : Fin L,
      (failure ∩ atom) ∩ statistic ⁻¹'
          (sourceProfileThetaBad c m (l + 1) profile ×ˢ
            (Set.univ : Set Direction)) ⊆ thetaPath l)
    (goodTail thetaTail : ℝ≥0∞)
    (hgood : sourceTruncatedProfileMeasure m profile
      (Q \ sourceProfileThetaUpTo c m L profile) ≤ goodTail)
    (hband : ∀ l, simpleRandomWalkLaw (thetaPath l ∩ atom) ≤
      thetaTail * simpleRandomWalkLaw atom) :
    simpleRandomWalkLaw (failure ∩ atom) ≤
      (goodTail + (L : ℝ≥0∞) * thetaTail) *
        simpleRandomWalkLaw atom := by
  let thetaUnion : Set (ℕ → Site) := ⋃ l, thetaPath l
  have hthetaUnion : (failure ∩ atom) ∩ statistic ⁻¹'
      (sourceProfileThetaUpTo c m L profile ×ˢ
        (Set.univ : Set Direction)) ⊆ thetaUnion := by
    intro path hpath
    rcases Set.mem_iUnion.mp hpath.2.1 with ⟨l, hl⟩
    exact Set.mem_iUnion.mpr ⟨l, htheta l
      ⟨hpath.1, hl, hpath.2.2⟩⟩
  have hthetaMeasure : simpleRandomWalkLaw (thetaUnion ∩ atom) ≤
      ((L : ℝ≥0∞) * thetaTail) * simpleRandomWalkLaw atom := by
    simpa only [thetaUnion] using
      measure_iUnion_fin_inter_atom_le atom thetaPath thetaTail hband
  exact stoppedProfileEvent_local_bound_with_theta profile atom failure
    thetaUnion statistic Q (sourceProfileThetaUpTo c m L profile)
    hmeasurable hmap hfailure hthetaUnion goodTail
      ((L : ℝ≥0∞) * thetaTail) hgood hthetaMeasure

/-- A strong atom-conditioned package which pays every profile exception in
the Proposition-4.8 recursion by an arbitrary-interval Proposition-4.5
estimate.

The fixed-profile atom `atom` and contextual candidate event `failure` are
kept in the type.  Thus the interval input estimates exactly
`atom ∩ failure ∩ thetaPath l`; it does not require a lower-band event to be
constant on the whole stopped atom, nor identify it with the top-band
Proposition-4.7 event.  This is a valid abstract implication, but it is not
the literal HLOZ source cut: its negative-binomial laws are conditioned on
`atom`, whereas a complete stopped atom truncates those laws.  The final
source closure therefore uses the theta-free connector and pays the checked
global Proposition-4.5 event after reuniting the stopped atoms. -/
structure StoppedProfileBandedThetaInputs
    {ι : Type*} [Fintype ι]
    (c m k : ℕ) (alpha : ℝ) (profile : ι → ℕ)
    (atom failure : Set (ℕ → Site))
    (statistic : (ℕ → Site) → (ι → ℕ) × Direction) where
  thetaPath : Fin (sourceAlphaIntervalCount m alpha) → Set (ℕ → Site)
  theta_pullback : ∀ l : Fin (sourceAlphaIntervalCount m alpha),
    (failure ∩ atom) ∩ statistic ⁻¹'
        (sourceProfileThetaBad c m (l.1 + 1) profile ×ˢ
          (Set.univ : Set Direction)) ⊆ thetaPath l
  interval : ∀ l : Fin (sourceAlphaIntervalCount m alpha),
    FixedProfileIntervalAtomInputs
      m (sourceIntervalLower m (l.1 + 1))
        (sourceThetaIntervalUpper m (l.1 + 1)) k
      simpleRandomWalkLaw atom failure (thetaPath l)

/-- The banded source data above removes the former atomwise
`theta_bound` probability premise.  Each path exception is proved by the
checked arbitrary-endpoint Proposition-4.5 theorem, and the finite union is
paid with the exact interval count. -/
theorem stoppedProfileEvent_local_bound_of_source_banded_theta
    {ι : Type*} [Fintype ι] {c m k : ℕ} {alpha : ℝ}
    (profile : ι → ℕ)
    (atom failure : Set (ℕ → Site))
    (statistic : (ℕ → Site) → (ι → ℕ) × Direction)
    (Q : Set (ι → ℕ))
    (B : StoppedProfileBandedThetaInputs c m k alpha profile atom failure
      statistic)
    (hscales : ∀ l : Fin (sourceAlphaIntervalCount m alpha),
      SourceIntervalScale m (sourceIntervalLower m (l + 1)) ∧
        SourceUpperScale m (sourceThetaIntervalUpper m (l + 1)))
    (hmeasurable : Measurable statistic)
    (hmap : (simpleRandomWalkLaw.restrict atom).map statistic =
      simpleRandomWalkLaw atom •
        ((sourceTruncatedProfileMeasure m profile).prod directionLaw))
    (hfailure : failure ∩ atom ⊆ statistic ⁻¹'
      (Q ×ˢ (Set.univ : Set Direction)))
    (goodTail : ℝ≥0∞)
    (hgood : sourceTruncatedProfileMeasure m profile
      (Q \ sourceProfileThetaUpTo c m
        (sourceAlphaIntervalCount m alpha) profile) ≤ goodTail) :
    simpleRandomWalkLaw (failure ∩ atom) ≤
      (goodTail +
        (sourceAlphaIntervalCount m alpha : ℝ≥0∞) *
          sourceProp45FourBranchError m) * simpleRandomWalkLaw atom := by
  let contextualTheta : Fin (sourceAlphaIntervalCount m alpha) →
      Set (ℕ → Site) := fun l ↦ failure ∩ B.thetaPath l
  apply stoppedProfileGoodEvent_local_bound_of_banded_theta
    profile atom failure statistic Q contextualTheta hmeasurable hmap
    hfailure
  · intro l path hpath
    exact ⟨hpath.1.1, B.theta_pullback l hpath⟩
  · exact hgood
  · intro l
    have hinterval := (B.interval l).theta_measure_le_mul
      (hscales l).1 (hscales l).2
    simpa only [contextualTheta, Set.inter_assoc, Set.inter_left_comm,
      Set.inter_comm] using hinterval

/-! ## Literal unprimed-even stopped atoms -/

/-- Raw source data for one unprimed-even stopped atom.  There is no law,
grouped-event identity, external boundary profile, or coordinate-positivity
field: those are derived by `unprimedEven_activeFreeWinning_capped_map_law_reduced`
from these literal source conditions. -/
structure UnprimedEvenActiveFreeAtom (m k : ℕ) where
  q : ℕ
  creationSet : Finset Site
  labels : Fin q → IncrementPair
  labels_nondistinguished : ∀ i, labels i ≠ distinguishedIncrementPair
  creationSet_card : creationSet.card = k
  creationSet_free : HLOZPairing.PairFree
    (HLOZPairing.XPair HLOZPairing.east) creationSet
  offBase : UnprimedEvenOffBaseMixedCondition labels m creationSet
  terminal_mem : stoppedTerminalBase labels ∈ creationSet
  admissible_nonempty :
    (actualAdmissibleStoppedVectors m k labels
      (unprimedEvenSourceConstraint m k creationSet labels)).Nonempty
  candidateBases : Finset (StoppedExternalBase (0, 0) labels)

namespace UnprimedEvenActiveFreeAtom

variable {m k : ℕ} (A : UnprimedEvenActiveFreeAtom m k)

def incrementEvent : Set (ℕ → Direction) :=
  actualStoppedVectorEvent m k A.labels (stoppedRunVectorBox A.q m) ∩
    stoppedSourceCondition m k A.creationSet

def event : Set (ℕ → Site) := simpleRandomWalk '' A.incrementEvent

noncomputable def activeBases :
    Finset (StoppedExternalBase (0, 0) A.labels) :=
  unprimedEvenLeftWinnerBases A.labels A.candidateBases

abbrev Coord :=
  ActiveFreeStoppedBase (0, 0) A.labels A.creationSet A.activeBases

noncomputable def profile : A.Coord → ℕ :=
  activeFreeStoppedShape (0, 0) A.labels A.creationSet A.activeBases

noncomputable def lazyVector : (ℕ → Site) → A.Coord → ℕ :=
  unprimedEvenActiveFreePathLazy m k A.creationSet A.labels A.activeBases

noncomputable def nextDirection : (ℕ → Site) → Direction :=
  unprimedEvenActiveFreePathNext m k A.creationSet A.labels A.activeBases

noncomputable def statistic :
    (ℕ → Site) → (A.Coord → ℕ) × Direction :=
  fun s ↦ (A.lazyVector s, A.nextDirection s)

theorem measurableSet_event (hm : 0 < m) (hk : 0 < k) :
    MeasurableSet A.event := by
  have hIncrement : MeasurableSet A.incrementEvent := by
    rw [incrementEvent, unprimedEven_source_partition m k A.creationSet A.labels
      hm hk A.creationSet_free]
    exact measurableSet_actualStoppedVectorEvent _ _ _ _
  exact HLOZSourceInstantiation.measurableEmbedding_simpleRandomWalk
    |>.measurableSet_image.2 hIncrement

theorem measurable_statistic : Measurable A.statistic := by
  apply Measurable.prodMk
  · exact measurable_unprimedEvenActiveFreePathLazy m k A.creationSet
      A.labels A.labels_nondistinguished A.activeBases
  · exact measurable_unprimedEvenActiveFreePathNext m k A.creationSet
      A.labels A.labels_nondistinguished A.activeBases

/-- Exact unnormalized stopped-atom law.  The active coordinates are the
canonical left/even winners filtered from `candidateBases`, so the reduced
source theorem supplies the truncated product law directly. -/
theorem statistic_map_law (hm : 0 < m) (hk : 0 < k) :
    (simpleRandomWalkLaw.restrict A.event).map A.statistic =
      simpleRandomWalkLaw A.event •
        ((sourceTruncatedProfileMeasure m A.profile).prod directionLaw) := by
  exact unprimedEven_leftWinner_StoppedEquation447Atom_map_law
    m k A.creationSet A.labels A.labels_nondistinguished hm hk
    A.creationSet_card A.creationSet_free A.offBase A.terminal_mem
    A.admissible_nonempty A.candidateBases

theorem profile_lt (hm : 0 < m) : ∀ x, A.profile x < m :=
  unprimedEven_leftWinner_profile_lt_of_nonempty
    m k A.creationSet A.labels hm A.creationSet_card A.creationSet_free
      A.offBase A.terminal_mem A.admissible_nonempty A.candidateBases

end UnprimedEvenActiveFreeAtom

/-! ## Literal primed strict-right stopped atoms -/

/-- Raw source data for the primed/odd strict-right half of the horizontal
winner split.  As in the unprimed atom, the product law is a theorem rather
than an input field. -/
structure PrimedRightActiveFreeAtom (m k : ℕ) where
  q : ℕ
  creationSet : Finset Site
  first : Direction
  labels : Fin q → IncrementPair
  labels_nondistinguished :
    ∀ i, labels i ≠ primedDistinguishedIncrementPair
  creationSet_card : creationSet.card = k
  creationSet_free : HLOZPairing.PairFree
    (HLOZPairing.XPair HLOZPairing.east) creationSet
  offBase : PrimedOddOffBaseMixedCondition first labels m creationSet
  terminal_mem : primedStoppedTerminalSite first labels ∈ creationSet
  admissible_nonempty :
    (actualAdmissiblePrimedStoppedVectors m k first labels
      (primedOddSourceConstraint m k creationSet first labels)).Nonempty
  candidateBases : Finset
    (StoppedExternalBase (primedInitialBase first) labels)

namespace PrimedRightActiveFreeAtom

variable {m k : ℕ} (A : PrimedRightActiveFreeAtom m k)

def incrementEvent : Set (ℕ → Direction) :=
  actualPrimedStoppedVectorEvent m k A.first A.labels
      (stoppedRunVectorBox A.q m) ∩
    stoppedSourceCondition m k A.creationSet

def event : Set (ℕ → Site) := simpleRandomWalk '' A.incrementEvent

noncomputable def activeBases :
    Finset (StoppedExternalBase (primedInitialBase A.first) A.labels) :=
  primedOddStrictRightWinnerBases A.first A.labels A.candidateBases

abbrev Coord :=
  ActiveFreeStoppedBase (primedInitialBase A.first) A.labels A.creationSet
    A.activeBases

noncomputable def profile : A.Coord → ℕ :=
  activeFreeStoppedShape (primedInitialBase A.first) A.labels A.creationSet
    A.activeBases

noncomputable def lazyVector : (ℕ → Site) → A.Coord → ℕ :=
  primedOddActiveFreePathLazy m k A.creationSet A.first A.labels A.activeBases

noncomputable def nextDirection : (ℕ → Site) → Direction :=
  primedOddActiveFreePathNext m k A.creationSet A.first A.labels A.activeBases

noncomputable def statistic :
    (ℕ → Site) → (A.Coord → ℕ) × Direction :=
  fun s ↦ (A.lazyVector s, A.nextDirection s)

theorem measurableSet_event (hm : 0 < m) (hk : 0 < k) :
    MeasurableSet A.event := by
  have hIncrement : MeasurableSet A.incrementEvent := by
    rw [incrementEvent, primedOdd_source_partition m k A.creationSet
      A.first A.labels hm hk A.creationSet_free]
    unfold actualPrimedStoppedVectorEvent
    exact MeasurableSet.iUnion fun v ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_stoppedPrefixAtom
        (reconstructedPrimedStoppedPrefix A.first A.labels v)
  exact HLOZSourceInstantiation.measurableEmbedding_simpleRandomWalk
    |>.measurableSet_image.2 hIncrement

theorem measurable_statistic : Measurable A.statistic := by
  apply Measurable.prodMk
  · exact measurable_primedOddActiveFreePathLazy m k A.creationSet A.first
      A.labels A.labels_nondistinguished A.activeBases
  · exact measurable_primedOddActiveFreePathNext m k A.creationSet A.first
      A.labels A.labels_nondistinguished A.activeBases

/-- Exact unnormalized stopped-atom law for the strict-right branch. -/
theorem statistic_map_law (hm : 0 < m) (hk : 0 < k) :
    (simpleRandomWalkLaw.restrict A.event).map A.statistic =
      simpleRandomWalkLaw A.event •
        ((sourceTruncatedProfileMeasure m A.profile).prod directionLaw) := by
  exact primedOdd_strictRightWinner_StoppedEquation447Atom_map_law
    m k A.creationSet A.first A.labels A.labels_nondistinguished hm hk
    A.creationSet_card A.creationSet_free A.offBase A.terminal_mem
    A.admissible_nonempty A.candidateBases

theorem profile_lt (hm : 0 < m) : ∀ x, A.profile x < m :=
  primedOdd_strictRightWinner_profile_lt_of_nonempty
    m k A.creationSet A.first A.labels hm A.creationSet_card
      A.creationSet_free A.offBase A.terminal_mem A.admissible_nonempty
      A.candidateBases

end PrimedRightActiveFreeAtom

/-! ## Literal full-terminal stopped atoms

These two declarations close the parity cases omitted by the nonterminal
unprimed-even and primed-odd atoms above. Their path statistics retain the
first increment after the complete terminal pair, namely the direction at
the completion clock `T + 1`. -/

/-- Raw source data for the unprimed-odd terminal tie-left branch. -/
structure UnprimedOddTerminalActiveFreeAtom (m k : ℕ) where
  q : ℕ
  creationSet : Finset Site
  labels : Fin q → IncrementPair
  labels_nondistinguished : ∀ i, labels i ≠ distinguishedIncrementPair
  terminal : IncrementPair
  creationSet_card : creationSet.card = k
  creationSet_free : HLOZPairing.PairFree
    (HLOZPairing.XPair HLOZPairing.east) creationSet
  offBase : UnprimedOddOffBaseMixedCondition labels terminal m creationSet
  terminal_mem : stoppedTerminalBase labels +
    directionStep (terminal 0) ∈ creationSet
  admissible_nonempty :
    (actualAdmissibleOddStoppedVectors m k labels terminal
      (unprimedOddSourceConstraint m k creationSet labels terminal)).Nonempty
  candidateBases : Finset (StoppedExternalBase (0, 0) labels)

namespace UnprimedOddTerminalActiveFreeAtom

variable {m k : ℕ} (A : UnprimedOddTerminalActiveFreeAtom m k)

def incrementEvent : Set (ℕ → Direction) :=
  actualOddStoppedVectorEvent m k A.labels A.terminal
      (stoppedRunVectorBox A.q m) ∩
    stoppedSourceCondition m k A.creationSet

def event : Set (ℕ → Site) := simpleRandomWalk '' A.incrementEvent

noncomputable def activeBases :
    Finset (StoppedExternalBase (0, 0) A.labels) :=
  unprimedOddTieLeftWinnerBases A.labels
    (unprimedOddTerminalExternalRight A.labels A.terminal) A.candidateBases

abbrev Coord :=
  ActiveFreeStoppedBase (0, 0) A.labels A.creationSet A.activeBases

noncomputable def profile : A.Coord → ℕ :=
  activeFreeStoppedShape (0, 0) A.labels A.creationSet A.activeBases

noncomputable def lazyVector : (ℕ → Site) → A.Coord → ℕ :=
  unprimedOddActiveFreePathLazy m k A.creationSet A.labels A.terminal
    A.activeBases

noncomputable def nextDirection : (ℕ → Site) → Direction :=
  unprimedOddActiveFreePathNext m k A.creationSet A.labels A.terminal
    A.activeBases

noncomputable def statistic :
    (ℕ → Site) → (A.Coord → ℕ) × Direction :=
  fun s ↦ (A.lazyVector s, A.nextDirection s)

theorem measurableSet_event (hm : 0 < m) (hk : 0 < k) :
    MeasurableSet A.event := by
  have hIncrement : MeasurableSet A.incrementEvent := by
    rw [incrementEvent, unprimedOdd_source_partition m k A.creationSet
      A.labels A.terminal hm hk A.creationSet_free]
    unfold actualOddStoppedVectorEvent
    exact MeasurableSet.iUnion fun v ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_stoppedPrefixAtom
        (reconstructedOddStoppedPrefix A.labels v A.terminal)
  exact HLOZSourceInstantiation.measurableEmbedding_simpleRandomWalk
    |>.measurableSet_image.2 hIncrement

theorem measurable_statistic : Measurable A.statistic := by
  apply Measurable.prodMk
  · exact measurable_unprimedOddActiveFreePathLazy m k A.creationSet
      A.labels A.labels_nondistinguished A.terminal A.activeBases
  · exact measurable_unprimedOddActiveFreePathNext m k A.creationSet
      A.labels A.labels_nondistinguished A.terminal A.activeBases

theorem statistic_map_law (hm : 0 < m) (hk : 0 < k) :
    (simpleRandomWalkLaw.restrict A.event).map A.statistic =
      simpleRandomWalkLaw A.event •
        ((sourceTruncatedProfileMeasure m A.profile).prod directionLaw) := by
  exact unprimedOdd_sourceTieLeftWinner_StoppedEquation447Atom_map_law
    m k A.creationSet A.labels A.labels_nondistinguished A.terminal hm hk
      A.creationSet_card A.creationSet_free A.offBase A.terminal_mem
      A.candidateBases A.admissible_nonempty

theorem profile_lt (hm : 0 < m) : ∀ x, A.profile x < m :=
  unprimedOdd_tieLeftWinner_profile_lt_of_nonempty
    m k A.creationSet A.labels A.terminal hm A.creationSet_card
      A.creationSet_free A.offBase A.terminal_mem A.admissible_nonempty
      A.candidateBases

end UnprimedOddTerminalActiveFreeAtom

/-- Raw source data for the primed-even terminal strict-right branch. -/
structure PrimedEvenTerminalActiveFreeAtom (m k : ℕ) where
  q : ℕ
  creationSet : Finset Site
  first : Direction
  labels : Fin q → IncrementPair
  labels_nondistinguished :
    ∀ i, labels i ≠ primedDistinguishedIncrementPair
  terminal : IncrementPair
  creationSet_card : creationSet.card = k
  creationSet_free : HLOZPairing.PairFree
    (HLOZPairing.XPair HLOZPairing.east) creationSet
  offBase : PrimedEvenOffBaseMixedCondition
    first labels terminal m creationSet
  terminal_mem : primedStoppedTerminalSite first labels +
    directionStep (terminal 0) ∈ creationSet
  admissible_nonempty :
    (actualAdmissiblePrimedTerminalVectors m k first labels terminal
      (primedEvenSourceConstraint m k creationSet first labels terminal)).Nonempty
  candidateBases : Finset
    (StoppedExternalBase (primedInitialBase first) labels)

namespace PrimedEvenTerminalActiveFreeAtom

variable {m k : ℕ} (A : PrimedEvenTerminalActiveFreeAtom m k)

def incrementEvent : Set (ℕ → Direction) :=
  actualPrimedTerminalVectorEvent m k A.first A.labels A.terminal
      (stoppedRunVectorBox A.q m) ∩
    stoppedSourceCondition m k A.creationSet

def event : Set (ℕ → Site) := simpleRandomWalk '' A.incrementEvent

noncomputable def activeBases :
    Finset (StoppedExternalBase (primedInitialBase A.first) A.labels) :=
  primedEvenStrictRightWinnerBases A.first A.labels
    (primedEvenTerminalExternalLeft A.first A.labels A.terminal)
      A.candidateBases

abbrev Coord :=
  ActiveFreeStoppedBase (primedInitialBase A.first) A.labels A.creationSet
    A.activeBases

noncomputable def profile : A.Coord → ℕ :=
  activeFreeStoppedShape (primedInitialBase A.first) A.labels A.creationSet
    A.activeBases

noncomputable def lazyVector : (ℕ → Site) → A.Coord → ℕ :=
  primedEvenActiveFreePathLazy m k A.creationSet A.first A.labels A.terminal
    A.activeBases

noncomputable def nextDirection : (ℕ → Site) → Direction :=
  primedEvenActiveFreePathNext m k A.creationSet A.first A.labels A.terminal
    A.activeBases

noncomputable def statistic :
    (ℕ → Site) → (A.Coord → ℕ) × Direction :=
  fun s ↦ (A.lazyVector s, A.nextDirection s)

theorem measurableSet_event (hm : 0 < m) (hk : 0 < k) :
    MeasurableSet A.event := by
  have hIncrement : MeasurableSet A.incrementEvent := by
    rw [incrementEvent, primedEven_source_partition m k A.creationSet
      A.first A.labels A.terminal hm hk A.creationSet_free]
    unfold actualPrimedTerminalVectorEvent
    exact MeasurableSet.iUnion fun v ↦ MeasurableSet.iUnion fun _ ↦
      measurableSet_stoppedPrefixAtom
        (reconstructedPrimedTerminalStoppedPrefix
          A.first A.labels v A.terminal)
  exact HLOZSourceInstantiation.measurableEmbedding_simpleRandomWalk
    |>.measurableSet_image.2 hIncrement

theorem measurable_statistic : Measurable A.statistic := by
  apply Measurable.prodMk
  · exact measurable_primedEvenActiveFreePathLazy m k A.creationSet A.first
      A.labels A.labels_nondistinguished A.terminal A.activeBases
  · exact measurable_primedEvenActiveFreePathNext m k A.creationSet A.first
      A.labels A.labels_nondistinguished A.terminal A.activeBases

theorem statistic_map_law (hm : 0 < m) (hk : 0 < k) :
    (simpleRandomWalkLaw.restrict A.event).map A.statistic =
      simpleRandomWalkLaw A.event •
        ((sourceTruncatedProfileMeasure m A.profile).prod directionLaw) := by
  exact primedEven_sourceStrictRightWinner_StoppedEquation447Atom_map_law
    m k A.creationSet A.first A.labels A.labels_nondistinguished A.terminal
      hm hk A.creationSet_card A.creationSet_free A.offBase A.terminal_mem
      A.candidateBases A.admissible_nonempty

theorem profile_lt (hm : 0 < m) : ∀ x, A.profile x < m :=
  primedEven_strictRightWinner_profile_lt_of_nonempty
    m k A.creationSet A.first A.labels A.terminal hm A.creationSet_card
      A.creationSet_free A.offBase A.terminal_mem A.admissible_nonempty
      A.candidateBases

end PrimedEvenTerminalActiveFreeAtom

/-! ## Atomwise probability transport -/

/-- All deterministic and analytic information for applying Proposition 4.8
to one raw stopped atom.  `failure_subset` is the precise still-missing
candidate-to-active-free-profile identification; it is an event inclusion,
not a probability estimate. -/
structure UnprimedEvenProp48Evidence
    (cWindow m k : ℕ) (alpha cBase cTheta thetaPower : ℝ)
    (failure : Set (ℕ → Site)) where
  atom : UnprimedEvenActiveFreeAtom m k
  failure_subset : failure ∩ atom.event ⊆ atom.lazyVector ⁻¹'
    sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) atom.profile
      (geometricThreshold (Real.log (m : ℝ) ^ 2)
        (sourceLemma411GrowthFactor cWindow)
        (sourceAlphaIntervalCount m alpha))
  base_bound :
    (sourceTruncatedProfileMeasure m atom.profile).real
      (sourceProfileQEvent m 1 atom.profile (Real.log (m : ℝ) ^ 2)) ≤
        Real.exp (-cBase * Real.log (m : ℝ) ^ 2)
  theta_bound : ∀ l, 2 ≤ l → l ≤ sourceAlphaIntervalCount m alpha →
    (sourceTruncatedProfileMeasure m atom.profile).real
      (sourceProfileThetaBad cWindow m l atom.profile) ≤
        Real.exp (-cTheta * (m : ℝ) ^ thetaPower)

/-- Conditional-to-unconditional transport on one literal stopped atom.
The only probability estimate supplied to this theorem is the fixed-profile
conclusion of the checked Proposition 4.8 recursion.  The stopped product law
itself is derived above. -/
theorem unprimedEvenProp48Evidence_local_bound
    {cWindow m k : ℕ} {alpha cBase cTheta thetaPower : ℝ}
    {failure : Set (ℕ → Site)}
    (E : UnprimedEvenProp48Evidence cWindow m k alpha cBase cTheta
      thetaPower failure)
    (hm : 0 < m) (hk : 0 < k) (tail : ℝ≥0∞)
    (hProp48 :
      sourceTruncatedProfileMeasure m E.atom.profile
        (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) E.atom.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha))) ≤ tail) :
    simpleRandomWalkLaw (failure ∩ E.atom.event) ≤
      tail * simpleRandomWalkLaw E.atom.event := by
  let Q : Set (E.atom.Coord → ℕ) :=
    sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) E.atom.profile
      (geometricThreshold (Real.log (m : ℝ) ^ 2)
        (sourceLemma411GrowthFactor cWindow)
        (sourceAlphaIntervalCount m alpha))
  let B : Set ((E.atom.Coord → ℕ) × Direction) :=
    Q ×ˢ (Set.univ : Set Direction)
  have hB : MeasurableSet B := MeasurableSet.of_discrete
  have hmap := E.atom.statistic_map_law hm hk
  have hprod :
      (sourceTruncatedProfileMeasure m E.atom.profile).prod directionLaw B =
        sourceTruncatedProfileMeasure m E.atom.profile Q := by
    dsimp [B]
    rw [Measure.prod_prod, measure_univ, mul_one]
  have hrestricted :
      simpleRandomWalkLaw (E.atom.event ∩ E.atom.statistic ⁻¹' B) =
        simpleRandomWalkLaw E.atom.event *
          sourceTruncatedProfileMeasure m E.atom.profile Q := by
    have hmeasure := congrArg
      (fun mu : Measure ((E.atom.Coord → ℕ) × Direction) ↦ mu B) hmap
    rw [Measure.map_apply E.atom.measurable_statistic hB,
      Measure.restrict_apply (hB.preimage E.atom.measurable_statistic),
      Measure.smul_apply, smul_eq_mul, hprod] at hmeasure
    simpa only [Set.inter_comm] using hmeasure
  have hsubset : failure ∩ E.atom.event ⊆
      E.atom.event ∩ E.atom.statistic ⁻¹' B := by
    intro ω hω
    refine ⟨hω.2, ?_⟩
    exact ⟨E.failure_subset hω, trivial⟩
  calc
    simpleRandomWalkLaw (failure ∩ E.atom.event) ≤
        simpleRandomWalkLaw (E.atom.event ∩ E.atom.statistic ⁻¹' B) :=
      measure_mono hsubset
    _ = simpleRandomWalkLaw E.atom.event *
        sourceTruncatedProfileMeasure m E.atom.profile Q := hrestricted
    _ ≤ simpleRandomWalkLaw E.atom.event * tail := by gcongr
    _ = tail * simpleRandomWalkLaw E.atom.event := mul_comm _ _

/-- The corresponding deterministic and fixed-profile analytic evidence for
one literal primed strict-right atom. -/
structure PrimedRightProp48Evidence
    (cWindow m k : ℕ) (alpha cBase cTheta thetaPower : ℝ)
    (failure : Set (ℕ → Site)) where
  atom : PrimedRightActiveFreeAtom m k
  failure_subset : failure ∩ atom.event ⊆ atom.lazyVector ⁻¹'
    sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) atom.profile
      (geometricThreshold (Real.log (m : ℝ) ^ 2)
        (sourceLemma411GrowthFactor cWindow)
        (sourceAlphaIntervalCount m alpha))
  base_bound :
    (sourceTruncatedProfileMeasure m atom.profile).real
      (sourceProfileQEvent m 1 atom.profile (Real.log (m : ℝ) ^ 2)) ≤
        Real.exp (-cBase * Real.log (m : ℝ) ^ 2)
  theta_bound : ∀ l, 2 ≤ l → l ≤ sourceAlphaIntervalCount m alpha →
    (sourceTruncatedProfileMeasure m atom.profile).real
      (sourceProfileThetaBad cWindow m l atom.profile) ≤
        Real.exp (-cTheta * (m : ℝ) ^ thetaPower)

/-- Conditional-to-unconditional transport on one literal primed
strict-right atom, using the exact checked primed path map law. -/
theorem primedRightProp48Evidence_local_bound
    {cWindow m k : ℕ} {alpha cBase cTheta thetaPower : ℝ}
    {failure : Set (ℕ → Site)}
    (E : PrimedRightProp48Evidence cWindow m k alpha cBase cTheta
      thetaPower failure)
    (hm : 0 < m) (hk : 0 < k) (tail : ℝ≥0∞)
    (hProp48 :
      sourceTruncatedProfileMeasure m E.atom.profile
        (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) E.atom.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha))) ≤ tail) :
    simpleRandomWalkLaw (failure ∩ E.atom.event) ≤
      tail * simpleRandomWalkLaw E.atom.event := by
  let Q : Set (E.atom.Coord → ℕ) :=
    sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) E.atom.profile
      (geometricThreshold (Real.log (m : ℝ) ^ 2)
        (sourceLemma411GrowthFactor cWindow)
        (sourceAlphaIntervalCount m alpha))
  let B : Set ((E.atom.Coord → ℕ) × Direction) :=
    Q ×ˢ (Set.univ : Set Direction)
  have hB : MeasurableSet B := MeasurableSet.of_discrete
  have hmap := E.atom.statistic_map_law hm hk
  have hprod :
      (sourceTruncatedProfileMeasure m E.atom.profile).prod directionLaw B =
        sourceTruncatedProfileMeasure m E.atom.profile Q := by
    dsimp [B]
    rw [Measure.prod_prod, measure_univ, mul_one]
  have hrestricted :
      simpleRandomWalkLaw (E.atom.event ∩ E.atom.statistic ⁻¹' B) =
        simpleRandomWalkLaw E.atom.event *
          sourceTruncatedProfileMeasure m E.atom.profile Q := by
    have hmeasure := congrArg
      (fun mu : Measure ((E.atom.Coord → ℕ) × Direction) ↦ mu B) hmap
    rw [Measure.map_apply E.atom.measurable_statistic hB,
      Measure.restrict_apply (hB.preimage E.atom.measurable_statistic),
      Measure.smul_apply, smul_eq_mul, hprod] at hmeasure
    simpa only [Set.inter_comm] using hmeasure
  have hsubset : failure ∩ E.atom.event ⊆
      E.atom.event ∩ E.atom.statistic ⁻¹' B := by
    intro ω hω
    refine ⟨hω.2, ?_⟩
    exact ⟨E.failure_subset hω, trivial⟩
  calc
    simpleRandomWalkLaw (failure ∩ E.atom.event) ≤
        simpleRandomWalkLaw (E.atom.event ∩ E.atom.statistic ⁻¹' B) :=
      measure_mono hsubset
    _ = simpleRandomWalkLaw E.atom.event *
        sourceTruncatedProfileMeasure m E.atom.profile Q := hrestricted
    _ ≤ simpleRandomWalkLaw E.atom.event * tail := by gcongr
    _ = tail * simpleRandomWalkLaw E.atom.event := mul_comm _ _

/-- Common probability transport for the two full-terminal source atoms.
The `nextDirection` component is part of `statistic`; for the terminal
branches it is the fresh direction at `T + 1`. -/
private theorem terminalStoppedProfileEvent_local_bound
    {ι : Type*} [Fintype ι]
    {cWindow m : ℕ} {alpha : ℝ}
    {failure atom : Set (ℕ → Site)}
    (profile : ι → ℕ)
    (lazyVector : (ℕ → Site) → ι → ℕ)
    (statistic : (ℕ → Site) → (ι → ℕ) × Direction)
    (hmeasurable : Measurable statistic)
    (hmap : (simpleRandomWalkLaw.restrict atom).map statistic =
      simpleRandomWalkLaw atom •
        ((sourceTruncatedProfileMeasure m profile).prod directionLaw))
    (hsubset : failure ∩ atom ⊆ lazyVector ⁻¹'
      sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) profile
        (geometricThreshold (Real.log (m : ℝ) ^ 2)
          (sourceLemma411GrowthFactor cWindow)
          (sourceAlphaIntervalCount m alpha)))
    (hstatistic : ∀ s, statistic s = (lazyVector s, (statistic s).2))
    (tail : ℝ≥0∞)
    (hProp48 :
      sourceTruncatedProfileMeasure m profile
        (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha))) ≤ tail) :
    simpleRandomWalkLaw (failure ∩ atom) ≤
      tail * simpleRandomWalkLaw atom := by
  let Q : Set (ι → ℕ) :=
    sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) profile
      (geometricThreshold (Real.log (m : ℝ) ^ 2)
        (sourceLemma411GrowthFactor cWindow)
        (sourceAlphaIntervalCount m alpha))
  let B : Set ((ι → ℕ) × Direction) :=
    Q ×ˢ (Set.univ : Set Direction)
  have hB : MeasurableSet B := MeasurableSet.of_discrete
  have hprod :
      (sourceTruncatedProfileMeasure m profile).prod directionLaw B =
        sourceTruncatedProfileMeasure m profile Q := by
    dsimp [B]
    rw [Measure.prod_prod, measure_univ, mul_one]
  have hrestricted :
      simpleRandomWalkLaw (atom ∩ statistic ⁻¹' B) =
        simpleRandomWalkLaw atom *
          sourceTruncatedProfileMeasure m profile Q := by
    have hmeasure := congrArg
      (fun mu : Measure ((ι → ℕ) × Direction) ↦ mu B) hmap
    rw [Measure.map_apply hmeasurable hB,
      Measure.restrict_apply (hB.preimage hmeasurable),
      Measure.smul_apply, smul_eq_mul, hprod] at hmeasure
    simpa only [Set.inter_comm] using hmeasure
  have hfailure : failure ∩ atom ⊆ atom ∩ statistic ⁻¹' B := by
    intro omega homega
    refine ⟨homega.2, ?_⟩
    change statistic omega ∈ B
    rw [hstatistic omega]
    exact ⟨hsubset homega, trivial⟩
  calc
    simpleRandomWalkLaw (failure ∩ atom) ≤
        simpleRandomWalkLaw (atom ∩ statistic ⁻¹' B) := measure_mono hfailure
    _ = simpleRandomWalkLaw atom *
        sourceTruncatedProfileMeasure m profile Q := hrestricted
    _ ≤ simpleRandomWalkLaw atom * tail := by gcongr
    _ = tail * simpleRandomWalkLaw atom := mul_comm _ _

/-- Proposition-4.8 evidence on one unprimed-odd terminal atom. -/
structure UnprimedOddTerminalProp48Evidence
    (cWindow m k : ℕ) (alpha cBase cTheta thetaPower : ℝ)
    (failure : Set (ℕ → Site)) where
  atom : UnprimedOddTerminalActiveFreeAtom m k
  failure_subset : failure ∩ atom.event ⊆ atom.lazyVector ⁻¹'
    sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) atom.profile
      (geometricThreshold (Real.log (m : ℝ) ^ 2)
        (sourceLemma411GrowthFactor cWindow)
        (sourceAlphaIntervalCount m alpha))
  base_bound :
    (sourceTruncatedProfileMeasure m atom.profile).real
      (sourceProfileQEvent m 1 atom.profile (Real.log (m : ℝ) ^ 2)) ≤
        Real.exp (-cBase * Real.log (m : ℝ) ^ 2)
  theta_bound : ∀ l, 2 ≤ l → l ≤ sourceAlphaIntervalCount m alpha →
    (sourceTruncatedProfileMeasure m atom.profile).real
      (sourceProfileThetaBad cWindow m l atom.profile) ≤
        Real.exp (-cTheta * (m : ℝ) ^ thetaPower)

theorem unprimedOddTerminalProp48Evidence_local_bound
    {cWindow m k : ℕ} {alpha cBase cTheta thetaPower : ℝ}
    {failure : Set (ℕ → Site)}
    (E : UnprimedOddTerminalProp48Evidence cWindow m k alpha cBase cTheta
      thetaPower failure)
    (hm : 0 < m) (hk : 0 < k) (tail : ℝ≥0∞)
    (hProp48 :
      sourceTruncatedProfileMeasure m E.atom.profile
        (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) E.atom.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha))) ≤ tail) :
    simpleRandomWalkLaw (failure ∩ E.atom.event) ≤
      tail * simpleRandomWalkLaw E.atom.event := by
  apply terminalStoppedProfileEvent_local_bound E.atom.profile
    E.atom.lazyVector E.atom.statistic E.atom.measurable_statistic
    (E.atom.statistic_map_law hm hk) E.failure_subset
  · intro s
    rfl
  · exact hProp48

/-- Proposition-4.8 evidence on one primed-even terminal atom. -/
structure PrimedEvenTerminalProp48Evidence
    (cWindow m k : ℕ) (alpha cBase cTheta thetaPower : ℝ)
    (failure : Set (ℕ → Site)) where
  atom : PrimedEvenTerminalActiveFreeAtom m k
  failure_subset : failure ∩ atom.event ⊆ atom.lazyVector ⁻¹'
    sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) atom.profile
      (geometricThreshold (Real.log (m : ℝ) ^ 2)
        (sourceLemma411GrowthFactor cWindow)
        (sourceAlphaIntervalCount m alpha))
  base_bound :
    (sourceTruncatedProfileMeasure m atom.profile).real
      (sourceProfileQEvent m 1 atom.profile (Real.log (m : ℝ) ^ 2)) ≤
        Real.exp (-cBase * Real.log (m : ℝ) ^ 2)
  theta_bound : ∀ l, 2 ≤ l → l ≤ sourceAlphaIntervalCount m alpha →
    (sourceTruncatedProfileMeasure m atom.profile).real
      (sourceProfileThetaBad cWindow m l atom.profile) ≤
        Real.exp (-cTheta * (m : ℝ) ^ thetaPower)

theorem primedEvenTerminalProp48Evidence_local_bound
    {cWindow m k : ℕ} {alpha cBase cTheta thetaPower : ℝ}
    {failure : Set (ℕ → Site)}
    (E : PrimedEvenTerminalProp48Evidence cWindow m k alpha cBase cTheta
      thetaPower failure)
    (hm : 0 < m) (hk : 0 < k) (tail : ℝ≥0∞)
    (hProp48 :
      sourceTruncatedProfileMeasure m E.atom.profile
        (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha) E.atom.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha))) ≤ tail) :
    simpleRandomWalkLaw (failure ∩ E.atom.event) ≤
      tail * simpleRandomWalkLaw E.atom.event := by
  apply terminalStoppedProfileEvent_local_bound E.atom.profile
    E.atom.lazyVector E.atom.statistic E.atom.measurable_statistic
    (E.atom.statistic_map_law hm hk) E.failure_subset
  · intro s
    rfl
  · exact hProp48

/-! ## Exact global interface and the currently available low-band bridge -/

/-- A disjoint stopped-atom decomposition of one candidate failure.  Every
atom is given by the raw unprimed-even stopped construction, so no stopped
product law or candidate probability bound occurs in this interface. -/
structure UnprimedEvenStoppedCandidateDecomposition
    (cWindow m k : ℕ) (alpha cBase cTheta thetaPower : ℝ)
    (failure : Set (ℕ → Site)) where
  atoms : ℕ → UnprimedEvenProp48Evidence cWindow m k alpha cBase cTheta
    thetaPower failure
  cover : failure ⊆ ⋃ n, (atoms n).atom.event
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (atoms n).atom.event (atoms l).atom.event

/-- Aggregation of the atomwise checked Proposition 4.8 estimates. -/
theorem measure_failure_le_of_unprimedEvenStoppedCandidateDecomposition
    {cWindow m k : ℕ} {alpha cBase cTheta thetaPower : ℝ}
    {failure : Set (ℕ → Site)}
    (D : UnprimedEvenStoppedCandidateDecomposition cWindow m k alpha cBase
      cTheta thetaPower failure)
    (hm : 0 < m) (hk : 0 < k) (tail : ℝ≥0∞)
    (hProp48 : ∀ n,
      sourceTruncatedProfileMeasure m (D.atoms n).atom.profile
        (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
          (D.atoms n).atom.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha))) ≤ tail) :
    simpleRandomWalkLaw failure ≤ tail := by
  apply fixed_cardinality_of_disjoint_path_witnesses simpleRandomWalkLaw failure
    (fun n ↦ failure ∩ (D.atoms n).atom.event)
    (fun n ↦ (D.atoms n).atom.event) tail
  · intro ω hω
    rcases Set.mem_iUnion.mp (D.cover hω) with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, hω, hn⟩
  · intro n
    exact unprimedEvenProp48Evidence_local_bound (D.atoms n) hm hk tail
      (hProp48 n)
  · exact D.pairwise_disjoint
  · intro n
    exact (D.atoms n).atom.measurableSet_event hm hk

/-- A disjoint literal primed strict-right stopped-atom decomposition.  It
contains no product-law or candidate-tail premise. -/
structure PrimedRightStoppedCandidateDecomposition
    (cWindow m k : ℕ) (alpha cBase cTheta thetaPower : ℝ)
    (failure : Set (ℕ → Site)) where
  atoms : ℕ → PrimedRightProp48Evidence cWindow m k alpha cBase cTheta
    thetaPower failure
  cover : failure ⊆ ⋃ n, (atoms n).atom.event
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (atoms n).atom.event (atoms l).atom.event

/-- Aggregation of the atomwise checked Proposition 4.8 estimates on the
primed strict-right branch. -/
theorem measure_failure_le_of_primedRightStoppedCandidateDecomposition
    {cWindow m k : ℕ} {alpha cBase cTheta thetaPower : ℝ}
    {failure : Set (ℕ → Site)}
    (D : PrimedRightStoppedCandidateDecomposition cWindow m k alpha cBase
      cTheta thetaPower failure)
    (hm : 0 < m) (hk : 0 < k) (tail : ℝ≥0∞)
    (hProp48 : ∀ n,
      sourceTruncatedProfileMeasure m (D.atoms n).atom.profile
        (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
          (D.atoms n).atom.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha))) ≤ tail) :
    simpleRandomWalkLaw failure ≤ tail := by
  apply fixed_cardinality_of_disjoint_path_witnesses simpleRandomWalkLaw failure
    (fun n ↦ failure ∩ (D.atoms n).atom.event)
    (fun n ↦ (D.atoms n).atom.event) tail
  · intro ω hω
    rcases Set.mem_iUnion.mp (D.cover hω) with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, hω, hn⟩
  · intro n
    exact primedRightProp48Evidence_local_bound (D.atoms n) hm hk tail
      (hProp48 n)
  · exact D.pairwise_disjoint
  · intro n
    exact (D.atoms n).atom.measurableSet_event hm hk

/-- A disjoint stopped-atom decomposition of the unprimed-odd terminal
branch. The cover is branch-local data; no assertion that this branch covers
another stopping-time parity is built into the declaration. -/
structure UnprimedOddTerminalStoppedCandidateDecomposition
    (cWindow m k : ℕ) (alpha cBase cTheta thetaPower : ℝ)
    (failure : Set (ℕ → Site)) where
  atoms : ℕ → UnprimedOddTerminalProp48Evidence cWindow m k alpha cBase
    cTheta thetaPower failure
  cover : failure ⊆ ⋃ n, (atoms n).atom.event
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (atoms n).atom.event (atoms l).atom.event

theorem measure_failure_le_of_unprimedOddTerminalStoppedCandidateDecomposition
    {cWindow m k : ℕ} {alpha cBase cTheta thetaPower : ℝ}
    {failure : Set (ℕ → Site)}
    (D : UnprimedOddTerminalStoppedCandidateDecomposition cWindow m k alpha
      cBase cTheta thetaPower failure)
    (hm : 0 < m) (hk : 0 < k) (tail : ℝ≥0∞)
    (hProp48 : ∀ n,
      sourceTruncatedProfileMeasure m (D.atoms n).atom.profile
        (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
          (D.atoms n).atom.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha))) ≤ tail) :
    simpleRandomWalkLaw failure ≤ tail := by
  apply fixed_cardinality_of_disjoint_path_witnesses simpleRandomWalkLaw failure
    (fun n ↦ failure ∩ (D.atoms n).atom.event)
    (fun n ↦ (D.atoms n).atom.event) tail
  · intro omega homega
    rcases Set.mem_iUnion.mp (D.cover homega) with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, homega, hn⟩
  · intro n
    exact unprimedOddTerminalProp48Evidence_local_bound
      (D.atoms n) hm hk tail (hProp48 n)
  · exact D.pairwise_disjoint
  · intro n
    exact (D.atoms n).atom.measurableSet_event hm hk

/-- A disjoint stopped-atom decomposition of the primed-even terminal
branch, again with only a branch-local cover. -/
structure PrimedEvenTerminalStoppedCandidateDecomposition
    (cWindow m k : ℕ) (alpha cBase cTheta thetaPower : ℝ)
    (failure : Set (ℕ → Site)) where
  atoms : ℕ → PrimedEvenTerminalProp48Evidence cWindow m k alpha cBase
    cTheta thetaPower failure
  cover : failure ⊆ ⋃ n, (atoms n).atom.event
  pairwise_disjoint : Pairwise fun n l ↦
    Disjoint (atoms n).atom.event (atoms l).atom.event

theorem measure_failure_le_of_primedEvenTerminalStoppedCandidateDecomposition
    {cWindow m k : ℕ} {alpha cBase cTheta thetaPower : ℝ}
    {failure : Set (ℕ → Site)}
    (D : PrimedEvenTerminalStoppedCandidateDecomposition cWindow m k alpha
      cBase cTheta thetaPower failure)
    (hm : 0 < m) (hk : 0 < k) (tail : ℝ≥0∞)
    (hProp48 : ∀ n,
      sourceTruncatedProfileMeasure m (D.atoms n).atom.profile
        (sourceProfileQEvent m (sourceAlphaIntervalCount m alpha)
          (D.atoms n).atom.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m alpha))) ≤ tail) :
    simpleRandomWalkLaw failure ≤ tail := by
  apply fixed_cardinality_of_disjoint_path_witnesses simpleRandomWalkLaw failure
    (fun n ↦ failure ∩ (D.atoms n).atom.event)
    (fun n ↦ (D.atoms n).atom.event) tail
  · intro omega homega
    rcases Set.mem_iUnion.mp (D.cover homega) with ⟨n, hn⟩
    exact Set.mem_iUnion.mpr ⟨n, homega, hn⟩
  · intro n
    exact primedEvenTerminalProp48Evidence_local_bound
      (D.atoms n) hm hk tail (hProp48 n)
  · exact D.pairwise_disjoint
  · intro n
    exact (D.atoms n).atom.measurableSet_event hm hk

/-- The source-faithful left-winner parity split.  The ordinary unprimed
law applies when the stopped terminal has even parity, while the
unprimed-odd terminal law applies to the complementary terminal parity.
Neither branch is required to cover the other: only the displayed union
must cover the original left-winner failure. -/
structure LeftWinnerParitySplitStoppedCandidateDecomposition
    (cWindow m k : ℕ) (alpha cBase cTheta thetaPower : ℝ)
    (failure : Set (ℕ → Site)) where
  evenFailure : Set (ℕ → Site)
  oddTerminalFailure : Set (ℕ → Site)
  cover : failure ⊆ evenFailure ∪ oddTerminalFailure
  even : UnprimedEvenStoppedCandidateDecomposition cWindow m k alpha cBase
    cTheta thetaPower evenFailure
  oddTerminal : UnprimedOddTerminalStoppedCandidateDecomposition cWindow m k
    alpha cBase cTheta thetaPower oddTerminalFailure

/-- The matching source-faithful right-winner parity split.  The ordinary
primed-odd law and the primed-even terminal law are kept as separate
branches until this final two-event union. -/
structure RightWinnerParitySplitStoppedCandidateDecomposition
    (cWindow m k : ℕ) (alpha cBase cTheta thetaPower : ℝ)
    (failure : Set (ℕ → Site)) where
  oddFailure : Set (ℕ → Site)
  evenTerminalFailure : Set (ℕ → Site)
  cover : failure ⊆ oddFailure ∪ evenTerminalFailure
  odd : PrimedRightStoppedCandidateDecomposition cWindow m k alpha cBase
    cTheta thetaPower oddFailure
  evenTerminal : PrimedEvenTerminalStoppedCandidateDecomposition cWindow m k
    alpha cBase cTheta thetaPower evenTerminalFailure

/-! ### The source left/right winner split -/

/-- The horizontal dominoes which meet the candidate set.  A candidate site
is sent to the unique even base of its `X₁` domino. -/
noncomputable def hlozCandidateDominoBasesAtTime (window : Site → Finset Site)
    (s : ℕ → Site) (t q : ℕ) : Finset Site := by
  classical
  exact (hlozCandidateSitesAtTime window s t q).image horizontalChessBase

/-- The ambient tie-left selected endpoints of horizontal dominoes meeting
the candidate set.  The selected endpoint can lie just outside the original
spatial window; the literal active/free source set is defined below. -/
noncomputable def hlozLeftWinnerCandidateSitesAtTime (window : Site → Finset Site)
    (s : ℕ → Site) (t q : ℕ) : Finset Site := by
  classical
  exact (hlozCandidateDominoBasesAtTime window s t q).filter fun b ↦
    localTime s t (b + paperE1) ≤ localTime s t b

/-- The ambient strict-right selected endpoints of horizontal dominoes
meeting the candidate set.  The odd endpoint, rather than its even base, is
recorded. -/
noncomputable def hlozRightWinnerCandidateSitesAtTime (window : Site → Finset Site)
    (s : ℕ → Site) (t q : ℕ) : Finset Site := by
  classical
  exact ((hlozCandidateDominoBasesAtTime window s t q).filter fun b ↦
    localTime s t b < localTime s t (b + paperE1)).image
      (fun b ↦ b + paperE1)

theorem hlozLeftWinnerCandidateSitesAtTime_chessEven
    (window : Site → Finset Site) (s : ℕ → Site) (t q : ℕ)
    {x : Site} (hx : x ∈ hlozLeftWinnerCandidateSitesAtTime window s t q) :
    HLOZPairing.chessEven x := by
  classical
  have hxB := (Finset.mem_filter.mp hx).1
  rcases Finset.mem_image.mp hxB with ⟨y, _, rfl⟩
  exact horizontalChessBase_chessEven y

theorem hlozLeftWinnerCandidateSitesAtTime_localTime_eq_max
    (window : Site → Finset Site) (s : ℕ → Site) (t q : ℕ)
    {x : Site} (hx : x ∈ hlozLeftWinnerCandidateSitesAtTime window s t q) :
    localTime s t x = max (localTime s t x)
      (localTime s t (x + paperE1)) := by
  classical
  have hwin := (Finset.mem_filter.mp hx).2
  exact (max_eq_left hwin).symm

theorem hlozRightWinnerCandidateSitesAtTime_witness
    (window : Site → Finset Site) (s : ℕ → Site) (t q : ℕ)
    {x : Site} (hx : x ∈ hlozRightWinnerCandidateSitesAtTime window s t q) :
    ∃ b ∈ hlozCandidateDominoBasesAtTime window s t q,
      x = b + paperE1 ∧
        localTime s t b < localTime s t x ∧
        localTime s t x = max (localTime s t b) (localTime s t x) := by
  classical
  rcases Finset.mem_image.mp hx with ⟨b, hb, rfl⟩
  refine ⟨b, (Finset.mem_filter.mp hb).1, rfl,
    (Finset.mem_filter.mp hb).2, ?_⟩
  exact (max_eq_right (Finset.mem_filter.mp hb).2.le).symm

theorem hlozRightWinnerCandidateSitesAtTime_not_chessEven
    (window : Site → Finset Site) (s : ℕ → Site) (t q : ℕ)
    {x : Site} (hx : x ∈ hlozRightWinnerCandidateSitesAtTime window s t q) :
    ¬ HLOZPairing.chessEven x := by
  classical
  rcases hlozRightWinnerCandidateSitesAtTime_witness window s t q hx with
    ⟨b, hb, rfl, _⟩
  have hbB : HLOZPairing.chessEven b := by
    rcases Finset.mem_image.mp hb with ⟨y, _, rfl⟩
    exact horizontalChessBase_chessEven y
  exact HLOZReconstruction.not_chessEven_add_paperE1 hbB

/-- Tie-left and strict-right select exactly one endpoint of every candidate
domino.  The equality is stated at cardinality level because the two sets
live on different endpoint parities. -/
theorem hlozWinnerCandidateSitesAtTime_card_add
    (window : Site → Finset Site) (s : ℕ → Site) (t q : ℕ) :
    (hlozLeftWinnerCandidateSitesAtTime window s t q).card +
        (hlozRightWinnerCandidateSitesAtTime window s t q).card =
      (hlozCandidateDominoBasesAtTime window s t q).card := by
  classical
  let B := hlozCandidateDominoBasesAtTime window s t q
  let p : Site → Prop := fun b ↦
    localTime s t (b + paperE1) ≤ localTime s t b
  have hright :
      B.filter (fun b ↦ localTime s t b < localTime s t (b + paperE1)) =
        B.filter (fun b ↦ ¬ p b) := by
    ext b
    simp only [Finset.mem_filter, p, not_le]
  rw [hlozLeftWinnerCandidateSitesAtTime,
    hlozRightWinnerCandidateSitesAtTime, show
      hlozCandidateDominoBasesAtTime window s t q = B by rfl]
  rw [Finset.card_image_iff.mpr
    HLOZReconstruction.add_paperE1_injective.injOn, hright]
  exact Finset.card_filter_add_card_filter_not p

/-- Every horizontal candidate domino contains at most two candidate sites.
Combined with the exact winner split above, this is the factor-two loss in
the source candidate-cardinality reduction. -/
theorem hlozCandidateSitesAtTime_card_le_two_mul_winners
    (window : Site → Finset Site) (s : ℕ → Site) (t q : ℕ) :
    (hlozCandidateSitesAtTime window s t q).card ≤
      2 * ((hlozLeftWinnerCandidateSitesAtTime window s t q).card +
        (hlozRightWinnerCandidateSitesAtTime window s t q).card) := by
  classical
  let F := hlozCandidateSitesAtTime window s t q
  let B := hlozCandidateDominoBasesAtTime window s t q
  let Bplus := B.image (fun b ↦ b + paperE1)
  have hsub : F ⊆ B ∪ Bplus := by
    intro x hx
    have hbase : horizontalChessBase x ∈ B := by
      exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
    rcases eq_horizontalChessBase_or_eq_add_paperE1 x with h | h
    · exact Finset.mem_union.mpr (Or.inl (h ▸ hbase))
    · apply Finset.mem_union.mpr
      apply Or.inr
      exact Finset.mem_image.mpr ⟨horizontalChessBase x, hbase, h.symm⟩
  have hBplus : Bplus.card = B.card := by
    exact Finset.card_image_iff.mpr
      HLOZReconstruction.add_paperE1_injective.injOn
  calc
    F.card ≤ (B ∪ Bplus).card := Finset.card_le_card hsub
    _ ≤ B.card + Bplus.card := Finset.card_union_le _ _
    _ = 2 * B.card := by omega
    _ = 2 * ((hlozLeftWinnerCandidateSitesAtTime window s t q).card +
        (hlozRightWinnerCandidateSitesAtTime window s t q).card) := by
      rw [hlozWinnerCandidateSitesAtTime_card_add]

/-- The deterministic one-domino enlargement of a spatial window.  This is
the exact closure needed when the winning partner of a candidate lies just
outside the original window. -/
noncomputable def hlozDominoClosureWindow (window : Site → Finset Site)
    (c : Site) : Finset Site := by
  classical
  let B := (window c).image horizontalChessBase
  exact B ∪ B.image (fun b ↦ b + paperE1)

theorem hlozDominoClosureWindow_card_le
    (window : Site → Finset Site) (c : Site) :
    (hlozDominoClosureWindow window c).card ≤ 2 * (window c).card := by
  classical
  let B := (window c).image horizontalChessBase
  have hB : B.card ≤ (window c).card := Finset.card_image_le
  have hshift : (B.image (fun b ↦ b + paperE1)).card = B.card :=
    Finset.card_image_iff.mpr
      HLOZReconstruction.add_paperE1_injective.injOn
  calc
    (hlozDominoClosureWindow window c).card ≤
        B.card + (B.image (fun b ↦ b + paperE1)).card := by
      exact Finset.card_union_le _ _
    _ = 2 * B.card := by omega
    _ ≤ 2 * (window c).card := by omega

theorem hlozLeftWinnerCandidateSitesAtTime_subset_dominoClosure
    (window : Site → Finset Site) (s : ℕ → Site) (t q : ℕ) :
    hlozLeftWinnerCandidateSitesAtTime window s t q ⊆
      hlozDominoClosureWindow window (s t) := by
  classical
  intro x hx
  have hxB := (Finset.mem_filter.mp hx).1
  rcases Finset.mem_image.mp hxB with ⟨y, hy, rfl⟩
  have hyWindow := (Finset.mem_filter.mp hy).1
  apply Finset.mem_union.mpr
  exact Or.inl (Finset.mem_image.mpr ⟨y, hyWindow, rfl⟩)

theorem hlozRightWinnerCandidateSitesAtTime_subset_dominoClosure
    (window : Site → Finset Site) (s : ℕ → Site) (t q : ℕ) :
    hlozRightWinnerCandidateSitesAtTime window s t q ⊆
      hlozDominoClosureWindow window (s t) := by
  classical
  intro x hx
  rcases Finset.mem_image.mp hx with ⟨b, hb, rfl⟩
  have hbB := (Finset.mem_filter.mp hb).1
  rcases Finset.mem_image.mp hbB with ⟨y, hy, rfl⟩
  have hyWindow := (Finset.mem_filter.mp hy).1
  apply Finset.mem_union.mpr
  apply Or.inr
  exact Finset.mem_image.mpr
    ⟨horizontalChessBase y, Finset.mem_image.mpr ⟨y, hyWindow, rfl⟩, rfl⟩

/-- Literal source `M_e`: tie-left selected endpoints on free dominoes.
The explicit `< m` condition excludes the entire first-`k` creation domino,
because the selected endpoint is the pair maximum. -/
noncomputable def hlozLeftActiveFreeWinnerCandidateSitesAtTime
    (window : Site → Finset Site) (s : ℕ → Site) (t m q : ℕ) :
    Finset Site := by
  classical
  exact (hlozLeftWinnerCandidateSitesAtTime window s t q).filter fun x ↦
    localTime s t x < m

/-- Literal source `M_o`: strict-right selected endpoints on free dominoes.
As on the left, `< m` is the active/free creation-domino exclusion. -/
noncomputable def hlozRightActiveFreeWinnerCandidateSitesAtTime
    (window : Site → Finset Site) (s : ℕ → Site) (t m q : ℕ) :
    Finset Site := by
  classical
  exact (hlozRightWinnerCandidateSitesAtTime window s t q).filter fun x ↦
    localTime s t x < m

/-- The tie-left winners which belong to one of the level-`m` creation
sites.  These are the complementary part of the literal active/free set. -/
noncomputable def hlozLeftCreationWinnerCandidateSitesAtTime
    (window : Site → Finset Site) (s : ℕ → Site) (t m q : ℕ) :
    Finset Site := by
  classical
  exact (hlozLeftWinnerCandidateSitesAtTime window s t q).filter fun x ↦
    m ≤ localTime s t x

/-- The strict-right winners which belong to one of the level-`m` creation
sites. -/
noncomputable def hlozRightCreationWinnerCandidateSitesAtTime
    (window : Site → Finset Site) (s : ℕ → Site) (t m q : ℕ) :
    Finset Site := by
  classical
  exact (hlozRightWinnerCandidateSitesAtTime window s t q).filter fun x ↦
    m ≤ localTime s t x

theorem hlozLeftActiveFree_card_add_creation
    (window : Site → Finset Site) (s : ℕ → Site) (t m q : ℕ) :
    (hlozLeftActiveFreeWinnerCandidateSitesAtTime window s t m q).card +
        (hlozLeftCreationWinnerCandidateSitesAtTime window s t m q).card =
      (hlozLeftWinnerCandidateSitesAtTime window s t q).card := by
  classical
  let F := hlozLeftWinnerCandidateSitesAtTime window s t q
  let p : Site → Prop := fun x ↦ localTime s t x < m
  have hcreation :
      F.filter (fun x ↦ m ≤ localTime s t x) = F.filter (fun x ↦ ¬ p x) := by
    ext x
    simp only [Finset.mem_filter, p, not_lt]
  rw [hlozLeftActiveFreeWinnerCandidateSitesAtTime,
    hlozLeftCreationWinnerCandidateSitesAtTime,
    show hlozLeftWinnerCandidateSitesAtTime window s t q = F by rfl,
    hcreation]
  exact Finset.card_filter_add_card_filter_not p

theorem hlozRightActiveFree_card_add_creation
    (window : Site → Finset Site) (s : ℕ → Site) (t m q : ℕ) :
    (hlozRightActiveFreeWinnerCandidateSitesAtTime window s t m q).card +
        (hlozRightCreationWinnerCandidateSitesAtTime window s t m q).card =
      (hlozRightWinnerCandidateSitesAtTime window s t q).card := by
  classical
  let F := hlozRightWinnerCandidateSitesAtTime window s t q
  let p : Site → Prop := fun x ↦ localTime s t x < m
  have hcreation :
      F.filter (fun x ↦ m ≤ localTime s t x) = F.filter (fun x ↦ ¬ p x) := by
    ext x
    simp only [Finset.mem_filter, p, not_lt]
  rw [hlozRightActiveFreeWinnerCandidateSitesAtTime,
    hlozRightCreationWinnerCandidateSitesAtTime,
    show hlozRightWinnerCandidateSitesAtTime window s t q = F by rfl,
    hcreation]
  exact Finset.card_filter_add_card_filter_not p

theorem hlozLeftCreationWinnerCandidateSitesAtTime_subset_level
    (window : Site → Finset Site) (s : ℕ → Site) (t m q : ℕ)
    (hm : 0 < m) :
    hlozLeftCreationWinnerCandidateSitesAtTime window s t m q ⊆
      sitesAtLeastLevel s t m := by
  classical
  intro x hx
  have hxge := (Finset.mem_filter.mp hx).2
  apply Finset.mem_filter.mpr
  refine ⟨?_, hxge⟩
  by_contra hxv
  have hz := localTime_eq_zero_of_not_mem_visitedSites hxv
  omega

theorem hlozRightCreationWinnerCandidateSitesAtTime_subset_level
    (window : Site → Finset Site) (s : ℕ → Site) (t m q : ℕ)
    (hm : 0 < m) :
    hlozRightCreationWinnerCandidateSitesAtTime window s t m q ⊆
      sitesAtLeastLevel s t m := by
  classical
  intro x hx
  have hxge := (Finset.mem_filter.mp hx).2
  apply Finset.mem_filter.mpr
  refine ⟨?_, hxge⟩
  by_contra hxv
  have hz := localTime_eq_zero_of_not_mem_visitedSites hxv
  omega

theorem hlozCreationWinnerCandidateSitesAtTime_disjoint
    (window : Site → Finset Site) (s : ℕ → Site) (t m q : ℕ) :
    Disjoint
      (hlozLeftCreationWinnerCandidateSitesAtTime window s t m q)
      (hlozRightCreationWinnerCandidateSitesAtTime window s t m q) := by
  classical
  rw [Finset.disjoint_left]
  intro x hxLeft hxRight
  exact (hlozRightWinnerCandidateSitesAtTime_not_chessEven window s t q
      (Finset.mem_filter.mp hxRight).1)
    (hlozLeftWinnerCandidateSitesAtTime_chessEven window s t q
      (Finset.mem_filter.mp hxLeft).1)

theorem hlozCreationWinnerCandidateSitesAtTime_card_add_le_level
    (window : Site → Finset Site) (s : ℕ → Site) (t m q : ℕ)
    (hm : 0 < m) :
    (hlozLeftCreationWinnerCandidateSitesAtTime window s t m q).card +
        (hlozRightCreationWinnerCandidateSitesAtTime window s t m q).card ≤
      (sitesAtLeastLevel s t m).card := by
  classical
  let L := hlozLeftCreationWinnerCandidateSitesAtTime window s t m q
  let R := hlozRightCreationWinnerCandidateSitesAtTime window s t m q
  have hdisj : Disjoint L R :=
    hlozCreationWinnerCandidateSitesAtTime_disjoint window s t m q
  have hsub : L ∪ R ⊆ sitesAtLeastLevel s t m := by
    intro x hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact hlozLeftCreationWinnerCandidateSitesAtTime_subset_level
        window s t m q hm hx
    · exact hlozRightCreationWinnerCandidateSitesAtTime_subset_level
        window s t m q hm hx
  rw [← Finset.card_union_of_disjoint hdisj]
  exact Finset.card_le_card hsub

/-- The exact deterministic source split: every candidate is charged, with
the factor-two domino loss, either to an active/free left winner, an
active/free right winner, or to one of the level-`m` creation sites. -/
theorem hlozCandidateSitesAtTime_card_le_activeFree_add_level
    (window : Site → Finset Site) (s : ℕ → Site) (t m q : ℕ)
    (hm : 0 < m) :
    (hlozCandidateSitesAtTime window s t q).card ≤
      2 * ((hlozLeftActiveFreeWinnerCandidateSitesAtTime
          window s t m q).card +
        (hlozRightActiveFreeWinnerCandidateSitesAtTime
          window s t m q).card +
        (sitesAtLeastLevel s t m).card) := by
  have hcandidate :=
    hlozCandidateSitesAtTime_card_le_two_mul_winners window s t q
  have hleft := hlozLeftActiveFree_card_add_creation window s t m q
  have hright := hlozRightActiveFree_card_add_creation window s t m q
  have hcreation :=
    hlozCreationWinnerCandidateSitesAtTime_card_add_le_level
      window s t m q hm
  omega

/-- At the finite `k`-th level-creation time, the last term in the source
split is exactly `k`. -/
theorem hlozCandidateSitesAt_firstKSitesReachLevel_card_le_activeFree_add_k
    (window : Site → Finset Site) (s : ℕ → Site) (m k q : ℕ)
    (hm : 0 < m) (hk : 0 < k)
    (hkfinite : firstKSitesReachLevel m k s ≠ ⊤) :
    (hlozCandidateSitesAtTime window s
        (firstKSitesReachLevel m k s).untopA q).card ≤
      2 * ((hlozLeftActiveFreeWinnerCandidateSitesAtTime window s
          (firstKSitesReachLevel m k s).untopA m q).card +
        (hlozRightActiveFreeWinnerCandidateSitesAtTime window s
          (firstKSitesReachLevel m k s).untopA m q).card + k) := by
  have h := hlozCandidateSitesAtTime_card_le_activeFree_add_level
    window s (firstKSitesReachLevel m k s).untopA m q hm
  rw [card_at_firstKSitesReachLevel_eq s m k hk hkfinite] at h
  exact h

theorem hlozLeftActiveFreeWinnerCandidateSitesAtTime_subset_dominoClosure
    (window : Site → Finset Site) (s : ℕ → Site) (t m q : ℕ) :
    hlozLeftActiveFreeWinnerCandidateSitesAtTime window s t m q ⊆
      hlozDominoClosureWindow window (s t) :=
  (Finset.filter_subset _ _).trans
    (hlozLeftWinnerCandidateSitesAtTime_subset_dominoClosure window s t q)

theorem hlozRightActiveFreeWinnerCandidateSitesAtTime_subset_dominoClosure
    (window : Site → Finset Site) (s : ℕ → Site) (t m q : ℕ) :
    hlozRightActiveFreeWinnerCandidateSitesAtTime window s t m q ⊆
      hlozDominoClosureWindow window (s t) :=
  (Finset.filter_subset _ _).trans
    (hlozRightWinnerCandidateSitesAtTime_subset_dominoClosure window s t q)

theorem hlozLeftActiveFreeWinnerCandidateSitesAtTime_localTime_bounds
    (window : Site → Finset Site) (s : ℕ → Site) (t m q : ℕ)
    {x : Site}
    (hx : x ∈ hlozLeftActiveFreeWinnerCandidateSitesAtTime window s t m q) :
    q ≤ localTime s t x ∧ localTime s t x < m := by
  classical
  have hxRaw := (Finset.mem_filter.mp hx).1
  have hxlt := (Finset.mem_filter.mp hx).2
  have hxWin := (Finset.mem_filter.mp hxRaw).2
  have hxBase := (Finset.mem_filter.mp hxRaw).1
  rcases Finset.mem_image.mp hxBase with ⟨y, hy, hyx⟩
  have hyq := (Finset.mem_filter.mp hy).2
  rcases eq_horizontalChessBase_or_eq_add_paperE1 y with hyLeft | hyRight
  · have : y = x := hyLeft.trans hyx
    subst y
    exact ⟨hyq, hxlt⟩
  · have : y = x + paperE1 := hyRight.trans (congrArg (fun z ↦ z + paperE1) hyx)
    rw [this] at hyq
    exact ⟨hyq.trans hxWin, hxlt⟩

theorem hlozRightActiveFreeWinnerCandidateSitesAtTime_localTime_bounds
    (window : Site → Finset Site) (s : ℕ → Site) (t m q : ℕ)
    {x : Site}
    (hx : x ∈ hlozRightActiveFreeWinnerCandidateSitesAtTime window s t m q) :
    q ≤ localTime s t x ∧ localTime s t x < m := by
  classical
  have hxRaw := (Finset.mem_filter.mp hx).1
  have hxlt := (Finset.mem_filter.mp hx).2
  rcases hlozRightWinnerCandidateSitesAtTime_witness window s t q hxRaw with
    ⟨b, hb, hxb, hblt, _⟩
  rcases Finset.mem_image.mp hb with ⟨y, hy, hyb⟩
  have hyq := (Finset.mem_filter.mp hy).2
  rcases eq_horizontalChessBase_or_eq_add_paperE1 y with hyLeft | hyRight
  · have : y = b := hyLeft.trans hyb
    rw [this] at hyq
    have hblt' : localTime s t b ≤ localTime s t (b + paperE1) := by
      rw [← hxb]
      exact hblt.le
    have hxlt' : localTime s t (b + paperE1) < m := by
      rw [← hxb]
      exact hxlt
    rw [hxb]
    exact ⟨hyq.trans hblt', hxlt'⟩
  · have : y = x := by
      rw [hxb]
      exact hyRight.trans (congrArg (fun z ↦ z + paperE1) hyb)
    rw [this] at hyq
    exact ⟨hyq, hxlt⟩

theorem hlozLeftActiveFreeWinnerCandidateSitesAtTime_avoids_creationDomino
    (window : Site → Finset Site) (s : ℕ → Site) (t m q : ℕ)
    {x : Site}
    (hx : x ∈ hlozLeftActiveFreeWinnerCandidateSitesAtTime window s t m q) :
    x ∉ sitesAtLeastLevel s t m ∧
      x + paperE1 ∉ sitesAtLeastLevel s t m := by
  classical
  have hxRaw := (Finset.mem_filter.mp hx).1
  have hxlt := (Finset.mem_filter.mp hx).2
  have hpartner := (Finset.mem_filter.mp hxRaw).2
  constructor
  · intro hxC
    have := (Finset.mem_filter.mp hxC).2
    omega
  · intro hxC
    have := (Finset.mem_filter.mp hxC).2
    omega

theorem hlozRightActiveFreeWinnerCandidateSitesAtTime_avoids_creationDomino
    (window : Site → Finset Site) (s : ℕ → Site) (t m q : ℕ)
    {x : Site}
    (hx : x ∈ hlozRightActiveFreeWinnerCandidateSitesAtTime window s t m q) :
    ∃ b, x = b + paperE1 ∧
      b ∉ sitesAtLeastLevel s t m ∧
      x ∉ sitesAtLeastLevel s t m := by
  classical
  have hxRaw := (Finset.mem_filter.mp hx).1
  have hxlt := (Finset.mem_filter.mp hx).2
  rcases hlozRightWinnerCandidateSitesAtTime_witness window s t q hxRaw with
    ⟨b, _, hxb, hblt, _⟩
  refine ⟨b, hxb, ?_, ?_⟩
  · intro hbC
    have hbge := (Finset.mem_filter.mp hbC).2
    omega
  · intro hxC
    have hxge := (Finset.mem_filter.mp hxC).2
    omega

noncomputable def hlozLeftWinnerCandidateCapFailureEvent (window : Site → Finset Site)
    (m k qCandidate cap : ℕ) : Set (ℕ → Site) :=
  {s | cap < (hlozLeftActiveFreeWinnerCandidateSitesAtTime window s
    (firstKSitesReachLevel m k s).untopA m qCandidate).card}

noncomputable def hlozRightWinnerCandidateCapFailureEvent (window : Site → Finset Site)
    (m k qCandidate cap : ℕ) : Set (ℕ → Site) :=
  {s | cap < (hlozRightActiveFreeWinnerCandidateSitesAtTime window s
    (firstKSitesReachLevel m k s).untopA m qCandidate).card}

/-- Honest event-level consequence of the deterministic winner split.  The
numerical hypothesis records all constant losses explicitly: two from
closing the candidate window under domino partners, the two winner caps,
and the at-most-`k` creation sites.  In particular, this theorem does not
pretend that splitting a cap into two halves can absorb the factor two. -/
theorem hlozCandidateCapFailureEvent_inter_subset_winnerFailure_union
    (window : Site → Finset Site) (m k qCandidate cap leftCap rightCap : ℕ)
    (P : Set (ℕ → Site)) (hm : 0 < m) (hk : 0 < k)
    (hP : P ⊆ hlozThresholdTimeEventK m (k + 1))
    (hcap : 2 * (leftCap + rightCap + k) ≤ cap) :
    hlozCandidateCapFailureEvent window m k qCandidate cap ∩ P ⊆
      (hlozLeftWinnerCandidateCapFailureEvent window m k qCandidate leftCap ∩ P) ∪
        (hlozRightWinnerCandidateCapFailureEvent window m k qCandidate rightCap ∩ P) := by
  intro s hs
  rcases hs with ⟨hfailure, hsP⟩
  by_cases hleft : s ∈
      hlozLeftWinnerCandidateCapFailureEvent window m k qCandidate leftCap
  · exact Or.inl ⟨hleft, hsP⟩
  by_cases hright : s ∈
      hlozRightWinnerCandidateCapFailureEvent window m k qCandidate rightCap
  · exact Or.inr ⟨hright, hsP⟩
  exfalso
  have hnext := hP hsP
  change firstKSitesReachLevel m (k + 1) s <
    firstKSitesReachLevel (m + 1) 1 s at hnext
  have hnextFinite : firstKSitesReachLevel m (k + 1) s ≠ ⊤ :=
    ne_top_of_lt hnext
  have hkFinite : firstKSitesReachLevel m k s ≠ ⊤ := by
    intro htop
    have hle := firstKSitesReachLevel_mono_k s m (show k ≤ k + 1 by omega)
    rw [htop] at hle
    exact hnextFinite (top_unique hle)
  have hdet :=
    hlozCandidateSitesAt_firstKSitesReachLevel_card_le_activeFree_add_k
      window s m k qCandidate hm hk hkFinite
  change cap < (hlozCandidateSitesAtTime window s
    (firstKSitesReachLevel m k s).untopA qCandidate).card at hfailure
  change ¬ leftCap <
    (hlozLeftActiveFreeWinnerCandidateSitesAtTime window s
      (firstKSitesReachLevel m k s).untopA m qCandidate).card at hleft
  change ¬ rightCap <
    (hlozRightActiveFreeWinnerCandidateSitesAtTime window s
      (firstKSitesReachLevel m k s).untopA m qCandidate).card at hright
  omega

/-- Split the full source cap exactly between the two winner parities. -/
noncomputable def sourceLeftWinnerCandidateCap
    (C : ℝ) (m : ℕ) (alpha : ℝ) (j : SourceBetaBandIndex) : ℕ :=
  sourceBetaCandidateCap C m alpha j / 2

noncomputable def sourceRightWinnerCandidateCap
    (C : ℝ) (m : ℕ) (alpha : ℝ) (j : SourceBetaBandIndex) : ℕ :=
  sourceBetaCandidateCap C m alpha j -
    sourceLeftWinnerCandidateCap C m alpha j

theorem sourceLeftWinnerCandidateCap_add_right
    (C : ℝ) (m : ℕ) (alpha : ℝ) (j : SourceBetaBandIndex) :
    sourceLeftWinnerCandidateCap C m alpha j +
      sourceRightWinnerCandidateCap C m alpha j =
        sourceBetaCandidateCap C m alpha j := by
  unfold sourceRightWinnerCandidateCap sourceLeftWinnerCandidateCap
  omega

/-- A source-faithful way to pay the deterministic domino and creation-site
losses is to use the Proposition 4.8 estimate with a smaller exponential
coefficient and the final Lemma 4.10 cap with a larger coefficient.  A gap
of `20` is deliberately generous and makes the ceiling calculation uniform,
including the first band where `beta-kappaOne = 0`. -/
theorem eventually_two_mul_smallCandidateCap_add_stage_le_largeCandidateCap
    {Csmall Cfull : ℝ} (hsmall : 0 ≤ Csmall)
    (hgap : Csmall + 20 ≤ Cfull) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      2 * (sourceBetaCandidateCap Csmall m (alphaValue a) j +
          stageNumber r) ≤
        sourceBetaCandidateCap Cfull m (alphaValue a) j := by
  filter_upwards [eventually_ge_atTop 2] with m hm
  intro r a ha j
  let gamma := sourceBeta (alphaValue a) j - kappaOne
  let x := (m : ℝ) ^ gamma
  let L2 := Real.log ((m : ℝ) + 1) ^ 2
  let Esmall := Real.exp (Csmall * x) * L2
  let Efull := Real.exp (Cfull * x) * L2
  have hgamma : 0 ≤ gamma := by
    dsimp [gamma]
    exact sub_nonneg.mpr (kappaOne_le_sourceBeta ha j)
  have hmone : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hxone : 1 ≤ x := by
    exact Real.one_le_rpow hmone hgamma
  have hx0 : 0 ≤ x := hxone.trans' (by norm_num)
  have hmplus : (3 : ℝ) ≤ (m : ℝ) + 1 := by
    exact_mod_cast (show 3 ≤ m + 1 by omega)
  have hmpluspos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hlog : 1 < Real.log ((m : ℝ) + 1) :=
    (Real.lt_log_iff_exp_lt hmpluspos).2
      (Real.exp_one_lt_three.trans_le hmplus)
  have hL2 : 1 ≤ L2 := by
    dsimp [L2]
    nlinarith
  have hEsmall : 1 ≤ Esmall := by
    dsimp [Esmall]
    have hexp : 1 ≤ Real.exp (Csmall * x) :=
      Real.one_le_exp (mul_nonneg hsmall hx0)
    nlinarith [mul_le_mul hexp hL2 (by norm_num : (0 : ℝ) ≤ 1)
      (Real.exp_nonneg _)]
  have hexponent : Csmall * x + 20 ≤ Cfull * x := by
    have hmul := mul_le_mul_of_nonneg_right hgap hx0
    nlinarith
  have hscale : 21 * Esmall ≤ Efull := by
    have h21 : (21 : ℝ) ≤ Real.exp 20 := by
      convert Real.add_one_le_exp 20 using 1 <;> norm_num
    dsimp [Esmall, Efull]
    calc
      21 * (Real.exp (Csmall * x) * L2) ≤
          Real.exp 20 * (Real.exp (Csmall * x) * L2) := by
        gcongr
      _ = Real.exp (Csmall * x + 20) * L2 := by
        rw [Real.exp_add]
        ring
      _ ≤ Real.exp (Cfull * x) * L2 := by
        gcongr
  have hsmallCeil :
      (sourceBetaCandidateCap Csmall m (alphaValue a) j : ℝ) <
        Esmall + 1 := by
    rw [sourceBetaCandidateCap]
    exact Nat.ceil_lt_add_one (by
      positivity)
  have hstage : stageNumber r ≤ 3 := by
    unfold stageNumber
    omega
  have htargetReal :
      ((2 * (sourceBetaCandidateCap Csmall m (alphaValue a) j +
          stageNumber r) : ℕ) : ℝ) < Efull := by
    push_cast
    have hrough :
        2 * ((sourceBetaCandidateCap Csmall m (alphaValue a) j : ℝ) +
          (stageNumber r : ℝ)) < 10 * Esmall := by
      have hstageReal : (stageNumber r : ℝ) ≤ 3 := by exact_mod_cast hstage
      nlinarith
    exact hrough.trans_le (by nlinarith [hscale])
  have hlt :
      2 * (sourceBetaCandidateCap Csmall m (alphaValue a) j +
          stageNumber r) <
        sourceBetaCandidateCap Cfull m (alphaValue a) j := by
    change 2 * (sourceBetaCandidateCap Csmall m (alphaValue a) j +
        stageNumber r) < Nat.ceil Efull
    rw [Nat.lt_ceil]
    exact htargetReal
  omega

/-- The exact X-east event cover used by the low-band connector.  The two
stopped laws are applied with coefficient `Csmall`; the final candidate
event uses `Cfull`, so the deterministic factor two and the first three
creation sites are genuinely absorbed rather than silently discarded. -/
theorem eventually_fullCandidateFailure_subset_smallWinnerFailures_xEast
    {Csmall Cfull : ℝ} (hsmall : 0 ≤ Csmall)
    (hgap : Csmall + 20 ≤ Cfull) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      hlozCandidateCapFailureEvent
            (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
            (sourceBetaCandidateThreshold m (alphaValue a) j)
            (sourceBetaCandidateCap Cfull m (alphaValue a) j) ∩
          prefixPairingEvent m (0 : Fin 6) (stageNumber r + 1) ⊆
        (hlozLeftWinnerCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceLeftWinnerCandidateCap Csmall m (alphaValue a) j) ∩
            prefixPairingEvent m (0 : Fin 6) (stageNumber r + 1)) ∪
          (hlozRightWinnerCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceRightWinnerCandidateCap Csmall m (alphaValue a) j) ∩
            prefixPairingEvent m (0 : Fin 6) (stageNumber r + 1)) := by
  filter_upwards [eventually_ge_atTop 2,
    eventually_two_mul_smallCandidateCap_add_stage_le_largeCandidateCap
      hsmall hgap] with m hm hcap
  intro r a ha j
  apply hlozCandidateCapFailureEvent_inter_subset_winnerFailure_union
      (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
      (sourceBetaCandidateThreshold m (alphaValue a) j)
      (sourceBetaCandidateCap Cfull m (alphaValue a) j)
      (sourceLeftWinnerCandidateCap Csmall m (alphaValue a) j)
      (sourceRightWinnerCandidateCap Csmall m (alphaValue a) j)
      (prefixPairingEvent m (0 : Fin 6) (stageNumber r + 1))
  · omega
  · unfold stageNumber
    omega
  · intro s hs
    exact hs.1
  · rw [sourceLeftWinnerCandidateCap_add_right]
    exact hcap r a ha j

/-- The exact low-band stopped input for the left-winner event.  Its two
branches are the diagonal unprimed-even case and the formerly missing
unprimed-odd terminal case.  Thus the full event is reached only through an
explicit parity cover, never through a diagonal-only decomposition. -/
def Prop47Lemma410Prop48LeftParityLowBandInputs
    (cWindow : ℕ) (C cBase cTheta thetaPower : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
    sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
    Nonempty (LeftWinnerParitySplitStoppedCandidateDecomposition cWindow m
      (stageNumber r) (sourceBeta (alphaValue a) j) cBase cTheta thetaPower
      (hlozLeftWinnerCandidateCapFailureEvent
          (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
          (sourceBetaCandidateThreshold m (alphaValue a) j)
          (sourceLeftWinnerCandidateCap C m (alphaValue a) j) ∩
        prefixPairingEvent m (0 : Fin 6) (stageNumber r + 1)))

/-- The exact matching low-band stopped input for the strict-right event.
It joins the diagonal primed-odd branch to the primed-even terminal branch
by an explicit parity cover. -/
def Prop47Lemma410Prop48RightParityLowBandInputs
    (cWindow : ℕ) (C cBase cTheta thetaPower : ℝ) : Prop :=
  ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
    alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
    sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
    Nonempty (RightWinnerParitySplitStoppedCandidateDecomposition cWindow m
      (stageNumber r) (sourceBeta (alphaValue a) j) cBase cTheta thetaPower
      (hlozRightWinnerCandidateCapFailureEvent
          (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
          (sourceBetaCandidateThreshold m (alphaValue a) j)
          (sourceRightWinnerCandidateCap C m (alphaValue a) j) ∩
        prefixPairingEvent m (0 : Fin 6) (stageNumber r + 1)))

/-- The candidate-cap event is measurable even though its defining local
time is evaluated at a stopping time. -/
theorem measurable_stoppedCandidateSitesAtTime
    (window : Site → Finset Site) (m k qCandidate : ℕ) :
    Measurable (fun s : ℕ → Site ↦
      hlozCandidateSitesAtTime window s
        (firstKSitesReachLevel m k s).untopA qCandidate) := by
  let τ := firstKSitesReachLevel m k
  have hτ : IsStoppingTime HLOZFoundation.canonicalFiltration τ :=
    isStoppingTime_firstKSitesReachLevel m k
  have hcoord : Measurable (fun s : ℕ → Site ↦ s (τ s).untopA) :=
    (HLOZLemma410Race.measurable_stoppedCoordinate hτ).mono
      hτ.measurableSpace_le le_rfl
  have hlocal (x : Site) :
      Measurable (fun s : ℕ → Site ↦ localTime s (τ s).untopA x) :=
    (HLOZLemma410Race.measurable_stoppedLocalTime hτ x).mono
      hτ.measurableSpace_le le_rfl
  rw [measurable_finset_iff]
  intro x
  simp only [hlozCandidateSitesAtTime, Finset.mem_filter]
  apply Measurable.and
  · exact (measurable_finset_mem x).comp
      ((measurable_of_countable window).comp hcoord)
  · exact measurableSet_setOfPred.mp
      (measurableSet_le measurable_const (hlocal x))

theorem measurable_stoppedLocalTime_firstKSites
    (m k : ℕ) (x : Site) :
    Measurable (fun s : ℕ → Site ↦
      localTime s (firstKSitesReachLevel m k s).untopA x) := by
  let τ := firstKSitesReachLevel m k
  have hτ : IsStoppingTime HLOZFoundation.canonicalFiltration τ :=
    isStoppingTime_firstKSitesReachLevel m k
  exact (HLOZLemma410Race.measurable_stoppedLocalTime hτ x).mono
    hτ.measurableSpace_le le_rfl

theorem measurable_stoppedCandidateDominoBasesAtTime
    (window : Site → Finset Site) (m k qCandidate : ℕ) :
    Measurable (fun s : ℕ → Site ↦
      hlozCandidateDominoBasesAtTime window s
        (firstKSitesReachLevel m k s).untopA qCandidate) := by
  exact (measurable_of_countable
      (fun F : Finset Site ↦ F.image horizontalChessBase)).comp
    (measurable_stoppedCandidateSitesAtTime window m k qCandidate)

theorem measurable_stoppedLeftWinnerCandidateSitesAtTime
    (window : Site → Finset Site) (m k qCandidate : ℕ) :
    Measurable (fun s : ℕ → Site ↦
      hlozLeftWinnerCandidateSitesAtTime window s
        (firstKSitesReachLevel m k s).untopA qCandidate) := by
  rw [measurable_finset_iff]
  intro x
  simp only [hlozLeftWinnerCandidateSitesAtTime, Finset.mem_filter]
  apply Measurable.and
  · exact (measurable_finset_mem x).comp
      (measurable_stoppedCandidateDominoBasesAtTime window m k qCandidate)
  · exact measurableSet_setOfPred.mp
      (measurableSet_le
        (measurable_stoppedLocalTime_firstKSites m k (x + paperE1))
        (measurable_stoppedLocalTime_firstKSites m k x))

theorem measurable_stoppedRightWinnerCandidateSitesAtTime
    (window : Site → Finset Site) (m k qCandidate : ℕ) :
    Measurable (fun s : ℕ → Site ↦
      hlozRightWinnerCandidateSitesAtTime window s
        (firstKSitesReachLevel m k s).untopA qCandidate) := by
  have hrightBases : Measurable (fun s : ℕ → Site ↦
      (hlozCandidateDominoBasesAtTime window s
        (firstKSitesReachLevel m k s).untopA qCandidate).filter fun b ↦
          localTime s (firstKSitesReachLevel m k s).untopA b <
            localTime s (firstKSitesReachLevel m k s).untopA
              (b + paperE1)) := by
    rw [measurable_finset_iff]
    intro b
    simp only [Finset.mem_filter]
    apply Measurable.and
    · exact (measurable_finset_mem b).comp
        (measurable_stoppedCandidateDominoBasesAtTime window m k qCandidate)
    · exact measurableSet_setOfPred.mp
        (measurableSet_lt
          (measurable_stoppedLocalTime_firstKSites m k b)
          (measurable_stoppedLocalTime_firstKSites m k (b + paperE1)))
  exact (measurable_of_countable
      (fun F : Finset Site ↦ F.image (fun b ↦ b + paperE1))).comp
    hrightBases

theorem measurable_stoppedLeftActiveFreeWinnerCandidateSitesAtTime
    (window : Site → Finset Site) (m k qCandidate : ℕ) :
    Measurable (fun s : ℕ → Site ↦
      hlozLeftActiveFreeWinnerCandidateSitesAtTime window s
        (firstKSitesReachLevel m k s).untopA m qCandidate) := by
  rw [measurable_finset_iff]
  intro x
  simp only [hlozLeftActiveFreeWinnerCandidateSitesAtTime,
    Finset.mem_filter]
  apply Measurable.and
  · exact (measurable_finset_mem x).comp
      (measurable_stoppedLeftWinnerCandidateSitesAtTime
        window m k qCandidate)
  · exact measurableSet_setOfPred.mp
      (measurableSet_lt
        (measurable_stoppedLocalTime_firstKSites m k x) measurable_const)

theorem measurable_stoppedRightActiveFreeWinnerCandidateSitesAtTime
    (window : Site → Finset Site) (m k qCandidate : ℕ) :
    Measurable (fun s : ℕ → Site ↦
      hlozRightActiveFreeWinnerCandidateSitesAtTime window s
        (firstKSitesReachLevel m k s).untopA m qCandidate) := by
  rw [measurable_finset_iff]
  intro x
  simp only [hlozRightActiveFreeWinnerCandidateSitesAtTime,
    Finset.mem_filter]
  apply Measurable.and
  · exact (measurable_finset_mem x).comp
      (measurable_stoppedRightWinnerCandidateSitesAtTime
        window m k qCandidate)
  · exact measurableSet_setOfPred.mp
      (measurableSet_lt
        (measurable_stoppedLocalTime_firstKSites m k x) measurable_const)

theorem measurableSet_hlozCandidateCapFailureEvent
    (window : Site → Finset Site) (m k qCandidate cap : ℕ) :
    MeasurableSet
      (hlozCandidateCapFailureEvent window m k qCandidate cap) := by
  have hcandidates : Measurable (fun s : ℕ → Site ↦
      hlozCandidateSitesAtTime window s
        (firstKSitesReachLevel m k s).untopA qCandidate) := by
    exact measurable_stoppedCandidateSitesAtTime window m k qCandidate
  unfold hlozCandidateCapFailureEvent
  exact measurableSet_lt measurable_const
    ((measurable_of_countable Finset.card).comp hcandidates)

theorem measurableSet_hlozLeftWinnerCandidateCapFailureEvent
    (window : Site → Finset Site) (m k qCandidate cap : ℕ) :
    MeasurableSet
      (hlozLeftWinnerCandidateCapFailureEvent window m k qCandidate cap) := by
  unfold hlozLeftWinnerCandidateCapFailureEvent
  exact measurableSet_lt measurable_const
    ((measurable_of_countable Finset.card).comp
      (measurable_stoppedLeftActiveFreeWinnerCandidateSitesAtTime
        window m k qCandidate))

theorem measurableSet_hlozRightWinnerCandidateCapFailureEvent
    (window : Site → Finset Site) (m k qCandidate cap : ℕ) :
    MeasurableSet
      (hlozRightWinnerCandidateCapFailureEvent window m k qCandidate cap) := by
  unfold hlozRightWinnerCandidateCapFailureEvent
  exact measurableSet_lt measurable_const
    ((measurable_of_countable Finset.card).comp
      (measurable_stoppedRightActiveFreeWinnerCandidateSitesAtTime
        window m k qCandidate))

/-! ### The deterministic high-band spatial bound -/

/-- The exact Euclidean lattice ball of squared radius `R^2` contains at
most the enclosing `(2R+1) × (2R+1)` integer box.  This repairs the much
coarser box used only to define `hlozLatticeBallSq`. -/
theorem hlozLatticeBallSq_card_le_square (R : ℕ) (c : Site) :
    (hlozLatticeBallSq (R ^ 2) c).card ≤ (2 * R + 1) ^ 2 := by
  classical
  let box : Finset Site :=
    (Finset.Icc (c.1 - (R : ℤ)) (c.1 + (R : ℤ))).product
      (Finset.Icc (c.2 - (R : ℤ)) (c.2 + (R : ℤ)))
  have hsub : hlozLatticeBallSq (R ^ 2) c ⊆ box := by
    intro x hx
    have hdist := (Finset.mem_filter.mp hx).2
    have h1sq : (x.1 - c.1).natAbs ^ 2 ≤ R ^ 2 := by
      unfold siteSquaredDistance at hdist
      omega
    have h2sq : (x.2 - c.2).natAbs ^ 2 ≤ R ^ 2 := by
      unfold siteSquaredDistance at hdist
      omega
    have h1 : (x.1 - c.1).natAbs ≤ R :=
      (sq_le_sq₀ (Nat.zero_le _) (Nat.zero_le _)).mp h1sq
    have h2 : (x.2 - c.2).natAbs ≤ R :=
      (sq_le_sq₀ (Nat.zero_le _) (Nat.zero_le _)).mp h2sq
    have h1abs : |x.1 - c.1| ≤ (R : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h1
    have h2abs : |x.2 - c.2| ≤ (R : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast h2
    rcases abs_le.mp h1abs with ⟨h1lo, h1hi⟩
    rcases abs_le.mp h2abs with ⟨h2lo, h2hi⟩
    apply Finset.mem_product.mpr
    constructor <;> apply Finset.mem_Icc.mpr <;> omega
  calc
    (hlozLatticeBallSq (R ^ 2) c).card ≤ box.card :=
      Finset.card_le_card hsub
    _ = (2 * R + 1) ^ 2 := by
      dsimp [box]
      rw [Finset.card_product, Int.card_Icc, Int.card_Icc]
      have heq1 : c.1 + (R : ℤ) + 1 - (c.1 - (R : ℤ)) =
          1 + (R : ℤ) * 2 := by ring
      have heq2 : c.2 + (R : ℤ) + 1 - (c.2 - (R : ℤ)) =
          1 + (R : ℤ) * 2 := by ring
      rw [heq1, heq2]
      have heqNat : 1 + (R : ℤ) * 2 = ((1 + R * 2 : ℕ) : ℤ) := by
        norm_num
      rw [heqNat, Int.toNat_natCast]
      ring

theorem sourceLemma410Window_card_le_square
    (m : ℕ) (alpha : ℝ) (c : Site) :
    (sourceLemma410Window m alpha c).card ≤
      (2 * sourceLemma410Radius m alpha + 1) ^ 2 := by
  exact hlozLatticeBallSq_card_le_square (sourceLemma410Radius m alpha) c

/-- In every source band above `7/10`, the candidate cap eventually exceeds
the entire deterministic spatial window.  This is the source argument
(4.973)--(4.980): `alpha ≤ kappa₂`, while
`beta-kappa₁ > 7/10-kappa₁ > kappa₂`, so the cap exponential
dominates the window exponential. -/
theorem eventually_sourceLemma410Window_card_lt_candidateCap
    {C alpha : ℝ} (hC : 0 < C)
    (halpha0 : 0 < alpha) (halpha : alpha ≤ kappaTwo)
    (j : SourceBetaBandIndex)
    (hbeta : (7 : ℝ) / 10 < sourceBeta alpha j) :
    ∀ᶠ m : ℕ in atTop, ∀ c : Site,
      (sourceLemma410Window m alpha c).card <
        sourceBetaCandidateCap C m alpha j := by
  let gamma := sourceBeta alpha j - kappaOne
  have hAlphaGamma : alpha < gamma := by
    dsimp [gamma]
    norm_num [kappaOne, kappaTwo] at hbeta halpha ⊢
    linarith
  have htwo :=
    HLOZNearCriticalBridge.eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := (2 : ℝ)) (d := C / 2) (p := alpha) (q := gamma)
      (by norm_num) (half_pos hC) hAlphaGamma
  have hconst :=
    HLOZNearCriticalBridge.eventually_const_mul_nat_rpow_le_const_mul_nat_rpow
      (C := Real.log 25) (d := C / 2) (p := (0 : ℝ)) (q := gamma)
      (Real.log_nonneg (by norm_num)) (half_pos hC)
      (lt_trans halpha0 hAlphaGamma)
  filter_upwards [htwo, hconst, eventually_ge_atTop 2] with
      m htwoM hconstM hm
  intro c
  let x := (m : ℝ) ^ alpha
  let R := sourceLemma410Radius m alpha
  have hx0 : 0 ≤ x := Real.rpow_nonneg (by positivity) _
  have hEone : 1 ≤ Real.exp x := Real.one_le_exp hx0
  have hR : (R : ℝ) ≤ 2 * Real.exp x := by
    have hceil : (R : ℝ) < Real.exp x + 1 := by
      exact Nat.ceil_lt_add_one (Real.exp_nonneg x)
    linarith
  have hside : ((2 * R + 1 : ℕ) : ℝ) ≤ 5 * Real.exp x := by
    push_cast
    nlinarith
  have hsquare : (((2 * R + 1) ^ 2 : ℕ) : ℝ) ≤
      25 * Real.exp (2 * x) := by
    rw [Nat.cast_pow]
    calc
      ((2 * R + 1 : ℕ) : ℝ) ^ 2 ≤ (5 * Real.exp x) ^ 2 := by
        exact (sq_le_sq₀ (by positivity) (by positivity)).2 hside
      _ = 25 * Real.exp (2 * x) := by
        rw [mul_pow]
        norm_num
        rw [pow_two, ← Real.exp_add]
        ring
  have hcardReal : ((sourceLemma410Window m alpha c).card : ℝ) ≤
      (((2 * R + 1) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast sourceLemma410Window_card_le_square m alpha c
  have hconstM' : Real.log 25 ≤ (C / 2) * (m : ℝ) ^ gamma := by
    simpa only [Real.rpow_zero, mul_one] using hconstM
  have hexponent : Real.log 25 + 2 * x ≤ C * (m : ℝ) ^ gamma := by
    dsimp [x]
    calc
      Real.log 25 + 2 * (m : ℝ) ^ alpha ≤
          (C / 2) * (m : ℝ) ^ gamma +
            (C / 2) * (m : ℝ) ^ gamma := add_le_add hconstM' htwoM
      _ = C * (m : ℝ) ^ gamma := by ring
  have hspatial : 25 * Real.exp (2 * x) ≤
      Real.exp (C * (m : ℝ) ^ gamma) := by
    calc
      25 * Real.exp (2 * x) = Real.exp (Real.log 25 + 2 * x) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 25)]
      _ ≤ Real.exp (C * (m : ℝ) ^ gamma) :=
        Real.exp_le_exp.mpr hexponent
  have hmplus : (3 : ℝ) ≤ (m : ℝ) + 1 := by
    exact_mod_cast (show 3 ≤ m + 1 by omega)
  have hmpluspos : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hlog : 1 < Real.log ((m : ℝ) + 1) :=
    (Real.lt_log_iff_exp_lt hmpluspos).2
      (Real.exp_one_lt_three.trans_le hmplus)
  have hlogsq : 1 < Real.log ((m : ℝ) + 1) ^ 2 := by nlinarith
  rw [sourceBetaCandidateCap, Nat.lt_ceil]
  have hwindow : ((sourceLemma410Window m alpha c).card : ℝ) ≤
      Real.exp (C * (m : ℝ) ^ gamma) :=
    hcardReal.trans (hsquare.trans hspatial)
  dsimp [gamma] at hwindow ⊢
  nlinarith [Real.exp_pos
    (C * (m : ℝ) ^ (sourceBeta alpha j - kappaOne))]

/-- The preceding high-band comparison is uniform on the finite source
alpha/beta grids. -/
theorem eventually_all_sourceLemma410Window_card_lt_candidateCap
    {C : ℝ} (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      (7 : ℝ) / 10 < sourceBeta (alphaValue a) j → ∀ c : Site,
        (sourceLemma410Window m (alphaValue a) c).card <
          sourceBetaCandidateCap C m (alphaValue a) j := by
  have hpairs : ∀ᶠ m : ℕ in atTop,
      ∀ p : AlphaIndex × SourceBetaBandIndex,
        alphaValue p.1 ≤ kappaTwo →
        (7 : ℝ) / 10 < sourceBeta (alphaValue p.1) p.2 →
        ∀ c : Site,
          (sourceLemma410Window m (alphaValue p.1) c).card <
            sourceBetaCandidateCap C m (alphaValue p.1) p.2 := by
    rw [Filter.eventually_all]
    intro p
    by_cases ha : alphaValue p.1 ≤ kappaTwo
    · by_cases hb : (7 : ℝ) / 10 < sourceBeta (alphaValue p.1) p.2
      · filter_upwards [eventually_sourceLemma410Window_card_lt_candidateCap
          hC (alphaValue_pos p.1) ha p.2 hb] with m hm
        exact fun _ _ ↦ hm
      · exact Filter.Eventually.of_forall fun _ _ h ↦ (hb h).elim
    · exact Filter.Eventually.of_forall fun _ h ↦ (ha h).elim
  filter_upwards [hpairs] with m hm
  intro a ha j hj
  exact hm (a, j) ha hj

theorem hlozCandidateCapFailureEvent_eq_empty_of_window_card_lt
    (window : Site → Finset Site) (m k qCandidate cap : ℕ)
    (hcard : ∀ c, (window c).card < cap) :
    hlozCandidateCapFailureEvent window m k qCandidate cap = ∅ := by
  ext s
  constructor
  · intro hs
    have hsub : hlozCandidateSitesAtTime window s
        (firstKSitesReachLevel m k s).untopA qCandidate ⊆
          window (s (firstKSitesReachLevel m k s).untopA) := by
      exact Finset.filter_subset _ _
    have hcandidates := Finset.card_le_card hsub
    have hwindow := hcard (s (firstKSitesReachLevel m k s).untopA)
    change cap < (hlozCandidateSitesAtTime window s
      (firstKSitesReachLevel m k s).untopA qCandidate).card at hs
    exact (not_lt_of_ge (hcandidates.trans hwindow.le)) hs
  · intro hs
    exact hs.elim

/-- Above `7/10` the candidate failure event is eventually empty, uniformly
in every source stage.  Thus no Proposition 4.8 hypothesis is used in the
high bands. -/
theorem eventually_hlozCandidateCapFailureEvent_eq_empty_highBands
    {C : ℝ} (hC : 0 < C) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      (7 : ℝ) / 10 < sourceBeta (alphaValue a) j →
      hlozCandidateCapFailureEvent
          (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
          (sourceBetaCandidateThreshold m (alphaValue a) j)
          (sourceBetaCandidateCap C m (alphaValue a) j) = ∅ := by
  filter_upwards [eventually_all_sourceLemma410Window_card_lt_candidateCap hC]
    with m hm
  intro r a ha j hj
  exact hlozCandidateCapFailureEvent_eq_empty_of_window_card_lt
    (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
    (sourceBetaCandidateThreshold m (alphaValue a) j)
    (sourceBetaCandidateCap C m (alphaValue a) j) (hm a ha j hj)

/-- The checked unprimed/left-winner reduction for every Lemma 4.10 band at
most `7/10`, exactly the range in which the source invokes Proposition 4.8.
It invokes the exact Proposition 4.8 high-band theorem on each fixed stopped
coordinate type. -/
theorem prop47Lemma410Prop48StoppedCandidateTail_leftWinner_lowBands
    (cWindow : ℕ) {C cBase cTheta thetaPower d : ℝ}
    (hcBase : 0 < cBase) (hcTheta : 0 < cTheta)
    (hthetaPower : 0 < thetaPower) (hd : 0 < d)
    (hcompare : 8 * d ≤
      min cBase
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48LeftParityLowBandInputs cWindow C cBase
      cTheta thetaPower) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
      simpleRandomWalkLaw
          (hlozLeftWinnerCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceLeftWinnerCandidateCap C m (alphaValue a) j) ∩
            prefixPairingEvent m (0 : Fin 6) (stageNumber r + 1)) ≤
        sourceBetaCandidateTail d m := by
  have hgood := eventually_sourceProp48NumericalAt cWindow hcBase hcTheta
    hthetaPower
  have htwoD : 0 < 2 * d := by positivity
  have hshift := eventually_prop48Rate_le_sourceBetaCandidateTail
    (rate := min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    htwoD (by nlinarith [hcompare])
  have habsorb := eventually_two_mul_sourceBetaCandidateTail_two_mul_le hd
  filter_upwards [h, hgood, hshift, habsorb, eventually_ge_atTop 2] with
      m hm hgoodM hshiftM habsorbM hmLarge
  intro r a ha j hj
  rcases hm r a ha j hj with ⟨D⟩
  have hmPos : 0 < m := by omega
  have hEvenProfile (n : ℕ) :
      sourceTruncatedProfileMeasure m (D.even.atoms n).atom.profile
        (sourceProfileQEvent m
          (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
          (D.even.atoms n).atom.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m
              (sourceBeta (alphaValue a) j)))) ≤
        sourceBetaCandidateTail (2 * d) m := by
    exact sourceTruncatedProfile_prop48_band_bound_at_ennreal hgoodM
      (sourceBeta (alphaValue a) j) (D.even.atoms n).atom.profile
      (kappaOne_le_sourceBeta ha j) (hj.trans (by norm_num))
      ((D.even.atoms n).atom.profile_lt hmPos)
      (D.even.atoms n).base_bound (D.even.atoms n).theta_bound
      (sourceBetaCandidateTail (2 * d) m) hshiftM
  have hOddTerminalProfile (n : ℕ) :
      sourceTruncatedProfileMeasure m (D.oddTerminal.atoms n).atom.profile
        (sourceProfileQEvent m
          (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
          (D.oddTerminal.atoms n).atom.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m
              (sourceBeta (alphaValue a) j)))) ≤
        sourceBetaCandidateTail (2 * d) m := by
    exact sourceTruncatedProfile_prop48_band_bound_at_ennreal hgoodM
      (sourceBeta (alphaValue a) j) (D.oddTerminal.atoms n).atom.profile
      (kappaOne_le_sourceBeta ha j) (hj.trans (by norm_num))
      ((D.oddTerminal.atoms n).atom.profile_lt hmPos)
      (D.oddTerminal.atoms n).base_bound
      (D.oddTerminal.atoms n).theta_bound
      (sourceBetaCandidateTail (2 * d) m) hshiftM
  have hEven := measure_failure_le_of_unprimedEvenStoppedCandidateDecomposition
    D.even (by omega) (by simp [stageNumber])
      (sourceBetaCandidateTail (2 * d) m) hEvenProfile
  have hOddTerminal :=
    measure_failure_le_of_unprimedOddTerminalStoppedCandidateDecomposition
      D.oddTerminal (by omega) (by simp [stageNumber])
        (sourceBetaCandidateTail (2 * d) m) hOddTerminalProfile
  calc
    simpleRandomWalkLaw _ ≤
        simpleRandomWalkLaw (D.evenFailure ∪ D.oddTerminalFailure) :=
      measure_mono D.cover
    _ ≤ simpleRandomWalkLaw D.evenFailure +
        simpleRandomWalkLaw D.oddTerminalFailure := measure_union_le _ _
    _ ≤ sourceBetaCandidateTail (2 * d) m +
        sourceBetaCandidateTail (2 * d) m := add_le_add hEven hOddTerminal
    _ = (2 : ℝ≥0∞) * sourceBetaCandidateTail (2 * d) m := by
      ring
    _ ≤ sourceBetaCandidateTail d m := habsorbM

/-- The checked primed strict-right reduction on the same source range
`beta ≤ 7/10`.  This consumes the literal primed atom decomposition and the
proved strict-right map law; it assumes no stopped product law or Q-tail. -/
theorem prop47Lemma410Prop48StoppedCandidateTail_rightWinner_lowBands
    (cWindow : ℕ) {C cBase cTheta thetaPower d : ℝ}
    (hcBase : 0 < cBase) (hcTheta : 0 < cTheta)
    (hthetaPower : 0 < thetaPower) (hd : 0 < d)
    (hcompare : 8 * d ≤
      min cBase
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48RightParityLowBandInputs cWindow C cBase
      cTheta thetaPower) :
    ∀ᶠ m : ℕ in atTop, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
      simpleRandomWalkLaw
          (hlozRightWinnerCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceRightWinnerCandidateCap C m (alphaValue a) j) ∩
            prefixPairingEvent m (0 : Fin 6) (stageNumber r + 1)) ≤
        sourceBetaCandidateTail d m := by
  have hgood := eventually_sourceProp48NumericalAt cWindow hcBase hcTheta
    hthetaPower
  have htwoD : 0 < 2 * d := by positivity
  have hshift := eventually_prop48Rate_le_sourceBetaCandidateTail
    (rate := min cBase
      (imbalanceRate
        (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    htwoD (by nlinarith [hcompare])
  have habsorb := eventually_two_mul_sourceBetaCandidateTail_two_mul_le hd
  filter_upwards [h, hgood, hshift, habsorb, eventually_ge_atTop 2] with
      m hm hgoodM hshiftM habsorbM hmLarge
  intro r a ha j hj
  rcases hm r a ha j hj with ⟨D⟩
  have hmPos : 0 < m := by omega
  have hOddProfile (n : ℕ) :
      sourceTruncatedProfileMeasure m (D.odd.atoms n).atom.profile
        (sourceProfileQEvent m
          (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
          (D.odd.atoms n).atom.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m
              (sourceBeta (alphaValue a) j)))) ≤
        sourceBetaCandidateTail (2 * d) m := by
    exact sourceTruncatedProfile_prop48_band_bound_at_ennreal hgoodM
      (sourceBeta (alphaValue a) j) (D.odd.atoms n).atom.profile
      (kappaOne_le_sourceBeta ha j) (hj.trans (by norm_num))
      ((D.odd.atoms n).atom.profile_lt hmPos)
      (D.odd.atoms n).base_bound (D.odd.atoms n).theta_bound
      (sourceBetaCandidateTail (2 * d) m) hshiftM
  have hEvenTerminalProfile (n : ℕ) :
      sourceTruncatedProfileMeasure m (D.evenTerminal.atoms n).atom.profile
        (sourceProfileQEvent m
          (sourceAlphaIntervalCount m (sourceBeta (alphaValue a) j))
          (D.evenTerminal.atoms n).atom.profile
          (geometricThreshold (Real.log (m : ℝ) ^ 2)
            (sourceLemma411GrowthFactor cWindow)
            (sourceAlphaIntervalCount m
              (sourceBeta (alphaValue a) j)))) ≤
        sourceBetaCandidateTail (2 * d) m := by
    exact sourceTruncatedProfile_prop48_band_bound_at_ennreal hgoodM
      (sourceBeta (alphaValue a) j) (D.evenTerminal.atoms n).atom.profile
      (kappaOne_le_sourceBeta ha j) (hj.trans (by norm_num))
      ((D.evenTerminal.atoms n).atom.profile_lt hmPos)
      (D.evenTerminal.atoms n).base_bound
      (D.evenTerminal.atoms n).theta_bound
      (sourceBetaCandidateTail (2 * d) m) hshiftM
  have hOdd := measure_failure_le_of_primedRightStoppedCandidateDecomposition
    D.odd (by omega) (by simp [stageNumber])
      (sourceBetaCandidateTail (2 * d) m) hOddProfile
  have hEvenTerminal :=
    measure_failure_le_of_primedEvenTerminalStoppedCandidateDecomposition
      D.evenTerminal (by omega) (by simp [stageNumber])
        (sourceBetaCandidateTail (2 * d) m) hEvenTerminalProfile
  calc
    simpleRandomWalkLaw _ ≤
        simpleRandomWalkLaw (D.oddFailure ∪ D.evenTerminalFailure) :=
      measure_mono D.cover
    _ ≤ simpleRandomWalkLaw D.oddFailure +
        simpleRandomWalkLaw D.evenTerminalFailure := measure_union_le _ _
    _ ≤ sourceBetaCandidateTail (2 * d) m +
        sourceBetaCandidateTail (2 * d) m := add_le_add hOdd hEvenTerminal
    _ = (2 : ℝ≥0∞) * sourceBetaCandidateTail (2 * d) m := by
      ring
    _ ≤ sourceBetaCandidateTail d m := habsorbM

/-! ## Residual transport to the other source pairings -/

/-- The exact deterministic/measure-preserving input needed to transport
the proved `X₁` candidate estimate to the other three rotated `X` tilings.
This contains no probability bound.  It is deliberately separate from the
two column tilings, which are not rotations of the checkerboard tiling. -/
structure Prop48XRotationCandidateTransport (C : ℝ) where
  pathMap : Dir → (ℕ → Site) → (ℕ → Site)
  measurable_pathMap : ∀ d, Measurable (pathMap d)
  preserves_walk_law : ∀ d,
    simpleRandomWalkLaw.map (pathMap d) = simpleRandomWalkLaw
  candidate_preimage : ∀ (d : Dir) (m : ℕ) (r : StageIndex)
      (a : AlphaIndex) (j : SourceBetaBandIndex),
    pathMap d ⁻¹'
      (hlozLeftWinnerCandidateCapFailureEvent
          (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
          (sourceBetaCandidateThreshold m (alphaValue a) j)
          (sourceLeftWinnerCandidateCap C m (alphaValue a) j) ∩
        prefixPairingEvent m (xIndex d) (stageNumber r + 1)) =
      hlozLeftWinnerCandidateCapFailureEvent
          (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
          (sourceBetaCandidateThreshold m (alphaValue a) j)
          (sourceLeftWinnerCandidateCap C m (alphaValue a) j) ∩
        prefixPairingEvent m (0 : Fin 6) (stageNumber r + 1)

/-- Once the event identity above is checked, the X-east low-band theorem
transports to all four checkerboard tilings without another stopped-law
assumption. -/
theorem prop47Lemma410Prop48StoppedCandidateTail_leftWinner_xRotatedLowBands
    (cWindow : ℕ) {C cBase cTheta thetaPower d : ℝ}
    (hcBase : 0 < cBase) (hcTheta : 0 < cTheta)
    (hthetaPower : 0 < thetaPower) (hd : 0 < d)
    (hcompare : 8 * d ≤
      min cBase
        (imbalanceRate
          (Real.exp (sourceAdjacentComparisonExponent cWindow))) / 2)
    (h : Prop47Lemma410Prop48LeftParityLowBandInputs cWindow C cBase
      cTheta thetaPower)
    (T : Prop48XRotationCandidateTransport C) :
    ∀ᶠ m : ℕ in atTop, ∀ d₀ : Dir, ∀ r : StageIndex, ∀ a : AlphaIndex,
      alphaValue a ≤ kappaTwo → ∀ j : SourceBetaBandIndex,
      sourceBeta (alphaValue a) j ≤ (7 : ℝ) / 10 →
      simpleRandomWalkLaw
          (hlozLeftWinnerCandidateCapFailureEvent
              (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
              (sourceBetaCandidateThreshold m (alphaValue a) j)
              (sourceLeftWinnerCandidateCap C m (alphaValue a) j) ∩
            prefixPairingEvent m (xIndex d₀) (stageNumber r + 1)) ≤
        sourceBetaCandidateTail d m := by
  have hEast :=
    prop47Lemma410Prop48StoppedCandidateTail_leftWinner_lowBands cWindow
    hcBase hcTheta hthetaPower hd hcompare h
  filter_upwards [hEast] with m hm
  intro d₀ r a ha j hj
  let E := hlozLeftWinnerCandidateCapFailureEvent
      (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
      (sourceBetaCandidateThreshold m (alphaValue a) j)
      (sourceLeftWinnerCandidateCap C m (alphaValue a) j) ∩
    prefixPairingEvent m (xIndex d₀) (stageNumber r + 1)
  have hE : MeasurableSet E :=
    (measurableSet_hlozLeftWinnerCandidateCapFailureEvent _ _ _ _ _).inter
      (measurableSet_prefixPairingEvent _ _ _)
  calc
    simpleRandomWalkLaw E =
        (simpleRandomWalkLaw.map (T.pathMap d₀)) E := by
      rw [T.preserves_walk_law]
    _ = simpleRandomWalkLaw ((T.pathMap d₀) ⁻¹' E) := by
      rw [Measure.map_apply (T.measurable_pathMap d₀) hE]
    _ = simpleRandomWalkLaw
        (hlozLeftWinnerCandidateCapFailureEvent
            (sourceLemma410Window m (alphaValue a)) m (stageNumber r)
            (sourceBetaCandidateThreshold m (alphaValue a) j)
            (sourceLeftWinnerCandidateCap C m (alphaValue a) j) ∩
          prefixPairingEvent m (0 : Fin 6) (stageNumber r + 1)) := by
      rw [T.candidate_preimage]
    _ ≤ sourceBetaCandidateTail d m := hm r a ha j hj

/- The independent column residual is intentionally not encoded by
`Prop48XRotationCandidateTransport`: the `Y` and `Y'` tilings use different
endpoint selectors and require their own stopped source partitions and
active-free capped map-law theorems.  No such theorem is currently exported
by `HLOZStoppedMapLaw`; consequently this connector makes no all-six or
`Prop47Lemma410Prop48StoppedCandidateTail` claim. -/

end Erdos1166.HLOZLemma410Prop48Connector
