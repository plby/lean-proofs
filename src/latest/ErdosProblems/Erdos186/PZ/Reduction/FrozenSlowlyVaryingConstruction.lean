/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Reduction.SlowlyVaryingConstruction

/-!
# Candidate closure with source parameters frozen on a square-root range
-/

namespace Erdos186.PZ.Reduction

open Erdos186.Irreducible
open Filter
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Terminal power absorption when `delta` is frozen at `initialCard`, while
the current input population may be any value above its square root. -/
theorem exists_terminalAbsorption_frozenSlowlyVarying_threshold
    (beta epsilon kappa constant p : ℝ) (R : ℕ)
    (hbeta : 1 < beta) (hepsilon0 : 0 < epsilon)
    (hepsilon1 : epsilon < (1 / 3 : ℝ))
    (hconstant : 0 < constant) (hp : 0 < p) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ initialCard currentCard n x v r : ℕ,
        threshold ≤ initialCard →
        Real.rpow (initialCard : ℝ) p ≤ (currentCard : ℝ) →
        r ≤ R →
        Real.rpow (currentCard : ℝ) (1 - epsilon) < (n : ℝ) →
        Erdos186.delta kappa initialCard * (n : ℝ) ≤ (x : ℝ) →
        (v : ℝ) ≤ constant * Real.rpow (currentCard : ℝ) beta →
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
  have hpq : 0 < p * q := mul_pos hp hq
  have heventual :=
    (tendsto_delta_rpow_mul_nat_rpow_atTop kappa E (p * q) hE hpq).eventually_ge_atTop
      ((2 : ℝ) ^ R * constant)
  obtain ⟨t, ht⟩ := eventually_atTop.1 heventual
  obtain ⟨deltaThreshold, hdeltaLarge⟩ := eventually_atTop.1
    (Erdos186.eventually_delta_pos kappa)
  let threshold := max 2 (max t deltaThreshold)
  refine ⟨threshold, le_max_left _ _, ?_⟩
  intro initialCard currentCard n x v r hinitial hpersist hr hpop hx hv
  have htN : t ≤ initialCard :=
    (le_max_left t deltaThreshold).trans
      ((le_max_right 2 (max t deltaThreshold)).trans hinitial)
  have hdeltaN : deltaThreshold ≤ initialCard :=
    (le_max_right t deltaThreshold).trans
      ((le_max_right 2 (max t deltaThreshold)).trans hinitial)
  have hcoefficient := ht initialCard htN
  have hNtwo : 2 ≤ initialCard :=
    (le_max_left 2 (max t deltaThreshold)).trans hinitial
  have hNpos : 0 < (initialCard : ℝ) := by positivity
  have hcurrentPos : 0 < (currentCard : ℝ) :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hNpos p) hpersist
  have hdelta := hdeltaLarge initialCard hdeltaN
  have hnpos : 0 < (n : ℝ) := by
    have hp : 0 < Real.rpow (currentCard : ℝ) (1 - epsilon) :=
      Real.rpow_pos_of_pos hcurrentPos _
    linarith
  have hxpos : 0 < (x : ℝ) :=
    lt_of_lt_of_le (mul_pos hdelta hnpos) hx
  have htwo : (2 : ℝ) ^ r ≤ (2 : ℝ) ^ R :=
    pow_le_pow_right₀ (by norm_num) hr
  have hpowNonneg : 0 ≤ Real.rpow (currentCard : ℝ) beta :=
    Real.rpow_nonneg hcurrentPos.le _
  have hcurrentPower : (initialCard : ℝ) ^ (p * q) ≤
      Real.rpow (currentCard : ℝ) q := by
    rw [Real.rpow_mul hNpos.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) hpersist hq.le
  have hcandidate :
      Erdos186.delta kappa initialCard *
          Real.rpow (currentCard : ℝ) (1 - epsilon) ≤ (x : ℝ) :=
    (mul_le_mul_of_nonneg_left hpop.le hdelta.le).trans hx
  calc
    (2 : ℝ) ^ r * (v : ℝ) ≤
        (2 : ℝ) ^ r * (constant * Real.rpow (currentCard : ℝ) beta) :=
      mul_le_mul_of_nonneg_left hv (by positivity)
    _ ≤ (2 : ℝ) ^ R *
        (constant * Real.rpow (currentCard : ℝ) beta) :=
      mul_le_mul_of_nonneg_right htwo
        (mul_nonneg hconstant.le hpowNonneg)
    _ = ((2 : ℝ) ^ R * constant) *
        Real.rpow (currentCard : ℝ) beta := by ring
    _ ≤ (Erdos186.delta kappa initialCard ^ E *
          (initialCard : ℝ) ^ (p * q)) *
        Real.rpow (currentCard : ℝ) beta :=
      mul_le_mul_of_nonneg_right hcoefficient hpowNonneg
    _ ≤ (Erdos186.delta kappa initialCard ^ E *
          Real.rpow (currentCard : ℝ) q) *
        Real.rpow (currentCard : ℝ) beta := by
      gcongr
    _ = Erdos186.delta kappa initialCard ^ E *
        Real.rpow (currentCard : ℝ) ((1 - epsilon) * E) := by
      have hadd : Real.rpow (currentCard : ℝ) q *
          Real.rpow (currentCard : ℝ) beta =
            Real.rpow (currentCard : ℝ) (q + beta) :=
        (Real.rpow_add hcurrentPos q beta).symm
      rw [mul_assoc, hadd]
      apply congrArg (Erdos186.delta kappa initialCard ^ E * ·)
      congr 1
      dsimp [q]
      ring
    _ = Real.rpow
        (Erdos186.delta kappa initialCard *
          Real.rpow (currentCard : ℝ) (1 - epsilon)) E := by
      have hpowpow :
          Real.rpow (currentCard : ℝ) ((1 - epsilon) * E) =
            Real.rpow (Real.rpow (currentCard : ℝ) (1 - epsilon)) E :=
        Real.rpow_mul hcurrentPos.le (1 - epsilon) E
      rw [hpowpow]
      exact (Real.mul_rpow
        (x := Erdos186.delta kappa initialCard)
        (y := Real.rpow (currentCard : ℝ) (1 - epsilon)) (z := E)
        hdelta.le (Real.rpow_nonneg hcurrentPos.le _)).symm
    _ ≤ Real.rpow (x : ℝ) E :=
      Real.rpow_le_rpow
        (mul_nonneg hdelta.le (Real.rpow_nonneg hcurrentPos.le _))
        hcandidate hE.le
    _ = Real.rpow (x : ℝ) (2 * (beta + 1)) := rfl

/-- Dense candidates for the frozen cutoff eventually exceed any fixed
finite canonical-scale threshold throughout the square-root range. -/
theorem exists_denseCandidate_card_frozenSlowlyVarying_threshold
    (epsilon kappa p : ℝ) (candidateThreshold : ℕ)
    (_hepsilon0 : 0 < epsilon) (hepsilon1 : epsilon < 1)
    (hp : 0 < p) :
    ∃ inputThreshold : ℕ, 2 ≤ inputThreshold ∧
      ∀ initialCard currentCard n x : ℕ,
        inputThreshold ≤ initialCard →
        Real.rpow (initialCard : ℝ) p ≤ (currentCard : ℝ) →
        Real.rpow (currentCard : ℝ) (1 - epsilon) < (n : ℝ) →
        Erdos186.delta kappa initialCard * (n : ℝ) ≤ (x : ℝ) →
        candidateThreshold ≤ x := by
  have ha : 0 < 1 - epsilon := sub_pos.mpr hepsilon1
  have hpa : 0 < p * (1 - epsilon) := mul_pos hp ha
  have heventual : ∀ᶠ N : ℕ in atTop,
      (candidateThreshold : ℝ) ≤
        Erdos186.delta kappa N * (N : ℝ) ^ (p * (1 - epsilon)) := by
    simpa only [Real.rpow_one] using
      (tendsto_delta_rpow_mul_nat_rpow_atTop kappa 1
        (p * (1 - epsilon)) zero_lt_one hpa).eventually_ge_atTop
          (candidateThreshold : ℝ)
  obtain ⟨t, ht⟩ := eventually_atTop.1 heventual
  obtain ⟨deltaThreshold, hdeltaLarge⟩ := eventually_atTop.1
    (Erdos186.eventually_delta_pos kappa)
  let inputThreshold := max 2 (max t deltaThreshold)
  refine ⟨inputThreshold, le_max_left _ _, ?_⟩
  intro initialCard currentCard n x hinitial hpersist hpopulation hdense
  have htN : t ≤ initialCard :=
    (le_max_left t deltaThreshold).trans
      ((le_max_right 2 (max t deltaThreshold)).trans hinitial)
  have hdeltaN : deltaThreshold ≤ initialCard :=
    (le_max_right t deltaThreshold).trans
      ((le_max_right 2 (max t deltaThreshold)).trans hinitial)
  have hdelta := hdeltaLarge initialCard hdeltaN
  have hNtwo : 2 ≤ initialCard :=
    (le_max_left 2 (max t deltaThreshold)).trans hinitial
  have hNpos : 0 < (initialCard : ℝ) := by exact_mod_cast (by omega : 0 < initialCard)
  have hpower : (initialCard : ℝ) ^ (p * (1 - epsilon)) ≤
      Real.rpow (currentCard : ℝ) (1 - epsilon) := by
    rw [Real.rpow_mul hNpos.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hNpos.le _) hpersist ha.le
  have hstrict :
      Erdos186.delta kappa initialCard *
          (initialCard : ℝ) ^ (p * (1 - epsilon)) <
        Erdos186.delta kappa initialCard * (n : ℝ) :=
    (mul_le_mul_of_nonneg_left hpower hdelta.le).trans_lt
      (mul_lt_mul_of_pos_left hpopulation hdelta)
  exact_mod_cast (ht initialCard htN).trans (hstrict.le.trans hdense)

/-- Candidate closure with source `delta` frozen at `initialCard`, uniformly
for current inputs on the retained square-root range. -/
theorem exists_terminalCandidateClosure_frozenSlowlyVarying_threshold
    {beta eta : ℝ} (C : HigherDimensionalContext (2 * (beta + 1)) eta)
    (R : ℕ) (epsilon selectorExponent kappa constant p : ℝ)
    (hbeta : 1 < beta) (heta0 : 0 < eta) (heta1 : eta < 1)
    (hepsilon0 : 0 < epsilon)
    (hepsilon1 : epsilon < (1 / 3 : ℝ))
    (hselector0 : 0 < selectorExponent)
    (hselector1 : selectorExponent < 1)
    (hconstant : 0 < constant) (hp : 0 < p) :
    ∃ threshold : ℕ, 2 ≤ threshold ∧
      ∀ (initialCard currentCard : ℕ)
        (S : CoordinateReplacementState (C.scaleSelector selectorExponent)),
        threshold ≤ initialCard →
        Real.rpow (initialCard : ℝ) p ≤ (currentCard : ℝ) →
        S.selected.dimension ≤ R →
        Real.rpow (currentCard : ℝ) (1 - epsilon) <
          (S.points.card : ℝ) →
        (S.selected.progression.volume : ℝ) ≤
          constant * Real.rpow (currentCard : ℝ) beta →
        (C.scaleSelector selectorExponent).CandidateClosedAt
          S.points S.eligible (Erdos186.delta kappa initialCard) := by
  obtain ⟨scaleThreshold, hscaleTwo, hscale⟩ :=
    exists_canonicalScale_threshold_boundedDimension C R heta0 heta1
      (ε := 1 - selectorExponent) (sub_pos.mpr hselector1)
      (by linarith)
  obtain ⟨absorbThreshold, habsorbTwo, habsorb⟩ :=
    exists_terminalAbsorption_frozenSlowlyVarying_threshold beta epsilon
      kappa constant p R hbeta hepsilon0 hepsilon1 hconstant hp
  obtain ⟨denseThreshold, hdenseTwo, hdense⟩ :=
    exists_denseCandidate_card_frozenSlowlyVarying_threshold epsilon kappa p
      scaleThreshold hepsilon0 (hepsilon1.trans (by norm_num)) hp
  let threshold := max absorbThreshold denseThreshold
  refine ⟨threshold, le_max_of_le_left habsorbTwo, ?_⟩
  intro initialCard currentCard S hinitial hpersist hrank hpopulation hvolume
  have habsorbN : absorbThreshold ≤ initialCard :=
    (le_max_left _ _).trans hinitial
  have hdenseN : denseThreshold ≤ initialCard :=
    (le_max_right _ _).trans hinitial
  apply scaleSelector_candidateClosedAt_of_threshold
    (threshold := scaleThreshold)
  · intro q hq
    have hs := hscale S.selected.dimension hrank q hq
    have hexponent : (1 : ℝ) - (1 - selectorExponent) =
        selectorExponent := by ring
    rw [hexponent] at hs
    exact hs
  · intro X _hX _hXne hcutoff
    exact hdense initialCard currentCard S.points.card X.card hdenseN hpersist
      hpopulation hcutoff
  · intro X _hX _hXne hcutoff
    exact habsorb initialCard currentCard S.points.card X.card
      S.selected.progression.volume S.selected.dimension habsorbN hpersist
      hrank hpopulation hcutoff hvolume

end

end Erdos186.PZ.Reduction
