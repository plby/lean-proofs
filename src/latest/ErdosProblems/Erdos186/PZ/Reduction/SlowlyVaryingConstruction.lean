/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.QuantitativeConstruction
import ErdosProblems.Erdos186.PZ.SourceParameterAsymptotics

/-!
# Quantitative reduction with source parameters frozen at the input size

The public reduction theorem quantifies its input threshold after `delta`
and `gamma`.  The final PZ iteration instead evaluates the slowly varying
source parameters at the initial population.  This module proves the
corresponding diagonal quantitative construction directly from the explicit
threshold proof: `epsilon` and `K` remain fixed, while only
`delta kappa N` and `gamma kappa K N` vary with the input cardinality.
-/

namespace Erdos186.PZ.Reduction

open Erdos186.Irreducible
open Filter
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- A slowly varying power of `delta` loses less than every fixed positive
power of the population. -/
theorem tendsto_delta_rpow_mul_nat_rpow_atTop
    (kappa E q : ℝ) (hE : 0 < E) (hq : 0 < q) :
    Tendsto
      (fun N : ℕ ↦ Erdos186.delta kappa N ^ E * (N : ℝ) ^ q)
      atTop atTop := by
  apply tendsto_atTop.mpr
  intro C
  have hgrowth : ∀ᶠ N : ℕ in atTop,
      C ≤ (N : ℝ) ^ (q / 2) :=
    ((tendsto_rpow_atTop (half_pos hq)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop C
  have hpower : 0 < q / (2 * E) := by positivity
  have hdelta : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-(q / (2 * E))) ≤ Erdos186.delta kappa N :=
    Erdos186.eventually_nat_rpow_neg_le_delta kappa hpower
  filter_upwards [hgrowth, hdelta, Erdos186.eventually_delta_pos kappa,
      eventually_gt_atTop (0 : ℕ)]
    with N hgrowthN hdeltaN hdeltaPos hN
  have hNreal : 0 < (N : ℝ) := by exact_mod_cast hN
  have hdeltaPower :
      (N : ℝ) ^ (-(q / 2)) ≤ Erdos186.delta kappa N ^ E := by
    calc
      (N : ℝ) ^ (-(q / 2)) =
          ((N : ℝ) ^ (-(q / (2 * E)))) ^ E := by
        rw [← Real.rpow_mul hNreal.le]
        congr 1
        field_simp
      _ ≤ Erdos186.delta kappa N ^ E :=
        Real.rpow_le_rpow (Real.rpow_nonneg hNreal.le _)
          hdeltaN hE.le
  calc
    C ≤ (N : ℝ) ^ (q / 2) := hgrowthN
    _ = (N : ℝ) ^ (-(q / 2)) * (N : ℝ) ^ q := by
      rw [← Real.rpow_add hNreal]
      congr 1
      ring
    _ ≤ Erdos186.delta kappa N ^ E * (N : ℝ) ^ q := by
      gcongr

/-- Terminal power absorption remains uniform when `delta` is evaluated at
the input population. -/
theorem exists_terminalAbsorption_slowlyVarying_threshold
    (beta epsilon kappa constant : ℝ) (R : ℕ)
    (hbeta : 1 < beta) (hepsilon0 : 0 < epsilon)
    (hepsilon1 : epsilon < (1 / 3 : ℝ))
    (hconstant : 0 < constant) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ m n x v r : ℕ,
        threshold ≤ m → r ≤ R →
        Real.rpow (m : ℝ) (1 - epsilon) < (n : ℝ) →
        Erdos186.delta kappa m * (n : ℝ) ≤ (x : ℝ) →
        (v : ℝ) ≤ constant * Real.rpow (m : ℝ) beta →
        (2 : ℝ) ^ r * (v : ℝ) ≤
          Real.rpow (x : ℝ) (2 * (beta + 1)) := by
  let E : ℝ := 2 * (beta + 1)
  let q : ℝ := (1 - epsilon) * E - beta
  have hE : 0 < E := by dsimp [E]; nlinarith
  have ha : (2 / 3 : ℝ) < 1 - epsilon := by linarith
  have hbasegap : beta < (2 / 3 : ℝ) * E := by
    dsimp [E]
    nlinarith
  have hq : 0 < q := by
    have hmul := mul_lt_mul_of_pos_right ha hE
    dsimp [q]
    linarith
  have heventual :=
    (tendsto_delta_rpow_mul_nat_rpow_atTop kappa E q hE hq).eventually_ge_atTop
      ((2 : ℝ) ^ R * constant)
  obtain ⟨t, ht⟩ := eventually_atTop.1 heventual
  obtain ⟨deltaThreshold, hdeltaLarge⟩ := eventually_atTop.1
    (Erdos186.eventually_delta_pos kappa)
  let threshold := max 2 (max t deltaThreshold)
  refine ⟨threshold, le_max_left _ _, ?_⟩
  intro m n x v r hm hr hpop hx hv
  have htm : t ≤ m :=
    (le_max_left t deltaThreshold).trans
      ((le_max_right 2 (max t deltaThreshold)).trans hm)
  have hdeltaM : deltaThreshold ≤ m :=
    (le_max_right t deltaThreshold).trans
      ((le_max_right 2 (max t deltaThreshold)).trans hm)
  have hcoefficient := ht m htm
  have hm2 : 2 ≤ m := (le_max_left 2 (max t deltaThreshold)).trans hm
  have hmpos : 0 < (m : ℝ) := by positivity
  have hdelta := hdeltaLarge m hdeltaM
  have hnpos : 0 < (n : ℝ) := by
    have hp : 0 < Real.rpow (m : ℝ) (1 - epsilon) :=
      Real.rpow_pos_of_pos hmpos _
    linarith
  have hxpos : 0 < (x : ℝ) :=
    lt_of_lt_of_le (mul_pos hdelta hnpos) hx
  have htwo : (2 : ℝ) ^ r ≤ (2 : ℝ) ^ R :=
    pow_le_pow_right₀ (by norm_num) hr
  have hpowNonneg : 0 ≤ Real.rpow (m : ℝ) beta :=
    Real.rpow_nonneg hmpos.le _
  have hcandidate :
      Erdos186.delta kappa m * Real.rpow (m : ℝ) (1 - epsilon) ≤
        (x : ℝ) :=
    (mul_le_mul_of_nonneg_left hpop.le hdelta.le).trans hx
  calc
    (2 : ℝ) ^ r * (v : ℝ) ≤
        (2 : ℝ) ^ r * (constant * Real.rpow (m : ℝ) beta) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ ≤ (2 : ℝ) ^ R *
        (constant * Real.rpow (m : ℝ) beta) :=
      mul_le_mul_of_nonneg_right htwo
        (mul_nonneg hconstant.le hpowNonneg)
    _ = ((2 : ℝ) ^ R * constant) *
        Real.rpow (m : ℝ) beta := by ring
    _ ≤ (Erdos186.delta kappa m ^ E *
          Real.rpow (m : ℝ) q) * Real.rpow (m : ℝ) beta :=
      mul_le_mul_of_nonneg_right hcoefficient hpowNonneg
    _ = Erdos186.delta kappa m ^ E *
        Real.rpow (m : ℝ) ((1 - epsilon) * E) := by
      have hadd : Real.rpow (m : ℝ) q * Real.rpow (m : ℝ) beta =
          Real.rpow (m : ℝ) (q + beta) :=
        (Real.rpow_add hmpos q beta).symm
      rw [mul_assoc, hadd]
      apply congrArg (Erdos186.delta kappa m ^ E * ·)
      congr 1
      dsimp [q]
      ring
    _ = Real.rpow
        (Erdos186.delta kappa m *
          Real.rpow (m : ℝ) (1 - epsilon)) E := by
      have hpowpow :
          Real.rpow (m : ℝ) ((1 - epsilon) * E) =
            Real.rpow (Real.rpow (m : ℝ) (1 - epsilon)) E :=
        Real.rpow_mul hmpos.le (1 - epsilon) E
      rw [hpowpow]
      exact (Real.mul_rpow
        (x := Erdos186.delta kappa m)
        (y := Real.rpow (m : ℝ) (1 - epsilon)) (z := E)
        hdelta.le (Real.rpow_nonneg hmpos.le _)).symm
    _ ≤ Real.rpow (x : ℝ) E :=
      Real.rpow_le_rpow
        (mul_nonneg hdelta.le (Real.rpow_nonneg hmpos.le _))
        hcandidate hE.le
    _ = Real.rpow (x : ℝ) (2 * (beta + 1)) := rfl

/-- Dense candidates eventually exceed a fixed finite threshold for the
source cutoff `delta kappa m`. -/
theorem exists_denseCandidate_card_slowlyVarying_threshold
    (epsilon kappa : ℝ) (candidateThreshold : ℕ)
    (_hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1) :
    ∃ inputThreshold : ℕ, 2 ≤ inputThreshold ∧
      ∀ m n x : ℕ,
        inputThreshold ≤ m →
        Real.rpow (m : ℝ) (1 - epsilon) < (n : ℝ) →
        Erdos186.delta kappa m * (n : ℝ) ≤ (x : ℝ) →
        candidateThreshold ≤ x := by
  have ha : 0 < 1 - epsilon := sub_pos.mpr hepsilon1
  have heventual : ∀ᶠ m : ℕ in atTop,
      (candidateThreshold : ℝ) ≤
        Erdos186.delta kappa m * (m : ℝ) ^ (1 - epsilon) := by
    simpa only [Real.rpow_one] using
      (tendsto_delta_rpow_mul_nat_rpow_atTop kappa 1 (1 - epsilon)
        zero_lt_one ha).eventually_ge_atTop (candidateThreshold : ℝ)
  obtain ⟨t, ht⟩ := eventually_atTop.1 heventual
  obtain ⟨deltaThreshold, hdeltaLarge⟩ := eventually_atTop.1
    (Erdos186.eventually_delta_pos kappa)
  let inputThreshold := max 2 (max t deltaThreshold)
  refine ⟨inputThreshold, le_max_left _ _, ?_⟩
  intro m n x hm hpopulation hdense
  have htm : t ≤ m :=
    (le_max_left t deltaThreshold).trans
      ((le_max_right 2 (max t deltaThreshold)).trans hm)
  have hdeltaM : deltaThreshold ≤ m :=
    (le_max_right t deltaThreshold).trans
      ((le_max_right 2 (max t deltaThreshold)).trans hm)
  have hdelta := hdeltaLarge m hdeltaM
  have hstrict :
      Erdos186.delta kappa m * Real.rpow (m : ℝ) (1 - epsilon) <
        Erdos186.delta kappa m * (n : ℝ) :=
    mul_lt_mul_of_pos_left hpopulation hdelta
  exact_mod_cast (ht m htm).trans (hstrict.le.trans hdense)

/-- Terminal candidate closure with the cutoff evaluated at the initial
population. -/
theorem exists_terminalCandidateClosure_slowlyVarying_threshold
    {beta eta : ℝ} (C : HigherDimensionalContext (2 * (beta + 1)) eta)
    (R : ℕ) (epsilon selectorExponent kappa constant : ℝ)
    (hbeta : 1 < beta) (heta0 : 0 < eta) (heta1 : eta < 1)
    (hepsilon0 : 0 < epsilon)
    (hepsilon1 : epsilon < (1 / 3 : ℝ))
    (hselector0 : 0 < selectorExponent)
    (hselector1 : selectorExponent < 1)
    (hconstant : 0 < constant) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ (m : ℕ)
        (S : CoordinateReplacementState (C.scaleSelector selectorExponent)),
        threshold ≤ m → S.selected.dimension ≤ R →
        Real.rpow (m : ℝ) (1 - epsilon) < (S.points.card : ℝ) →
        (S.selected.progression.volume : ℝ) ≤
          constant * Real.rpow (m : ℝ) beta →
        (C.scaleSelector selectorExponent).CandidateClosedAt
          S.points S.eligible (Erdos186.delta kappa m) := by
  obtain ⟨scaleThreshold, hscaleTwo, hscale⟩ :=
    exists_canonicalScale_threshold_boundedDimension C R heta0 heta1
      (ε := 1 - selectorExponent) (sub_pos.mpr hselector1)
      (by linarith)
  obtain ⟨absorbThreshold, habsorbTwo, habsorb⟩ :=
    exists_terminalAbsorption_slowlyVarying_threshold beta epsilon kappa
      constant R hbeta hepsilon0 hepsilon1 hconstant
  obtain ⟨denseThreshold, hdenseTwo, hdense⟩ :=
    exists_denseCandidate_card_slowlyVarying_threshold epsilon kappa
      scaleThreshold hepsilon0 (hepsilon1.trans (by norm_num))
  let threshold := max absorbThreshold denseThreshold
  refine ⟨threshold, le_max_of_le_left habsorbTwo, ?_⟩
  intro m S hm hrank hpopulation hvolume
  have habsorbM : absorbThreshold ≤ m :=
    (le_max_left _ _).trans hm
  have hdenseM : denseThreshold ≤ m :=
    (le_max_right _ _).trans hm
  apply scaleSelector_candidateClosedAt_of_threshold
    (threshold := scaleThreshold)
  · intro q hq
    have hs := hscale S.selected.dimension hrank q hq
    have hexponent : (1 : ℝ) - (1 - selectorExponent) =
        selectorExponent := by ring
    rw [hexponent] at hs
    exact hs
  · intro X _hX _hXne hcutoff
    exact hdense m S.points.card X.card hdenseM hpopulation hcutoff
  · intro X _hX _hXne hcutoff
    exact habsorb m S.points.card X.card
      S.selected.progression.volume S.selected.dimension habsorbM hrank
      hpopulation hcutoff hvolume

end

end Erdos186.PZ.Reduction
