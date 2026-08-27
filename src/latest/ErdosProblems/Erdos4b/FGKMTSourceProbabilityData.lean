/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTProbabilityPinnedMean
import ErdosProblems.Erdos4b.FGKMTProbabilityAtomBound

/-!
# Constructed finite probability data for the random sieve

The dimension, tuple and integer distributions are genuinely constructed.
This package is an input to the subsequent random residue sieve, not a
replacement for the hypergraph covering or the prime-gap conclusions.
-/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

structure SourceProbabilityData (c e : ℝ) (x : ℕ) where
  dimension : ℕ
  dimension_eq : dimension = growingSieveDimension x
  dimension_ge : 2 ≤ dimension
  shifts : Fin dimension → ℕ
  shifts_injective : Function.Injective shifts
  shifts_admissible : BoundedGaps.IsAdmissible (Finset.univ.image shifts)
  shifts_bounds : ∀ i, (shifts i).Prime ∧ dimension < shifts i ∧ shifts i < 2 * dimension ^ 2
  gain : ℝ
  gain_pos : 0 < gain
  gain_lower : Real.log (Real.log (x : ℝ)) / 368640 ≤ gain
  gain_upper : gain ≤ (6 / 5 : ℝ) * Real.exp 24 * Real.log (Real.log (x : ℝ))
  mass : ℕ → ℤ → ℝ
  mass_nonneg : ∀ p ∈ commonPinnedPrimeSet (x / 2) x, ∀ n : ℤ, 0 ≤ mass p n
  mass_support : ∀ p ∈ commonPinnedPrimeSet (x / 2) x, ∀ n : ℤ,
    sourceIntervalLength c x < |(n : ℝ)| → mass p n = 0
  mass_sum_one : ∀ p ∈ commonPinnedPrimeSet (x / 2) x,
    (∑ n ∈ integerWeightWindow (sourceIntervalLength c x), mass p n) = 1
  mass_atom_bound : ∀ p ∈ commonPinnedPrimeSet (x / 2) x, ∀ n : ℤ,
    mass p n ≤ (x : ℝ) ^ (-2 / 3 + e : ℝ)
  pinned_mean : ∀ Q : ℕ, Q.Prime → x < Q → (Q : ℝ) ≤ sourceIntervalLength c x →
    ∀ j : Fin dimension,
      |(∑ p ∈ commonPinnedPrimeSet (x / 2) x, mass p ((Q : ℤ) - (shifts j : ℤ) * p)) -
          (gain / dimension) * x / (2 * sourceIntervalLength c x)| ≤
        (4 / Real.log (Real.log (x : ℝ)) ^ 10) *
          ((gain / dimension) * x / (2 * sourceIntervalLength c x))

theorem eventually_nonempty_sourceProbabilityData {c e : ℝ} (hc : 0 < c) (he : 0 < e) :
    ∀ᶠ x : ℕ in atTop, Nonempty (SourceProbabilityData c e x) := by
  obtain ⟨_a, _ha, hweights⟩ := exists_sourceWeightEstimates hc (by positivity : 0 < e / 2)
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  filter_upwards [hweights, eventually_sourceWeightGain_loglog_bounds,
    eventually_weightProbability_atom_bound he, eventually_sourceIntervalLength_bounds hc,
    eventually_growingSieveDimension_profile_range, eventually_ge_atTop (1 : ℕ),
    hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    hloglog.eventually (eventually_ge_atTop (2 : ℝ))] with
      x hweights hgain hatom hinterval hprofile hx hL hLL
  obtain ⟨B, m, h, _hB1, _hBsize, hB, hm, hmk, hinj, hadm, hshift, H⟩ := hweights
  have hxpos : 0 < x := by omega
  have hxR : (0 : ℝ) < x := by exact_mod_cast hxpos
  have hy : 0 < sourceIntervalLength c x := hxR.trans_le hinterval.1
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  change 2 ≤ Real.log (Real.log (x : ℝ)) at hLL
  have herror : 1 / Real.log (Real.log (x : ℝ)) ^ 10 ≤ (1 / 2 : ℝ) := by
    have hpow := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hLL 10
    apply (div_le_iff₀ (by positivity : 0 < Real.log (Real.log (x : ℝ)) ^ 10)).mpr
    norm_num at hpow
    linarith
  have hlogk : 10000 ≤ Real.log (m + 1 : ℕ) := by simpa only [hmk] using hprofile.2
  have hdim : (m + 1 : ℕ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) := by
    simpa only [hmk] using growingSieveDimension_le x
  have hg := hgain m B hmk hB
  refine ⟨{
    dimension := m + 1
    dimension_eq := hmk
    dimension_ge := by omega
    shifts := h
    shifts_injective := hinj
    shifts_admissible := hadm
    shifts_bounds := hshift
    gain := commonWeightGain m B (dimensionPreSieveModulus (m + 1) B) (dimensionSieveRadius x) x
    gain_pos := H.2.1
    gain_lower := hg.1
    gain_upper := hg.2
    mass := commonPrimeSieveProbability (m + 1) (dimensionPreSieveModulus (m + 1) B)
      (B * dimensionPreSieveModulus (m + 1) B) (dimensionSieveRadius x) (sourceIntervalLength c x) h
    mass_nonneg := fun p _hp n => commonPrimeSieveProbability_nonneg _ _ _ _ _ _ p n
    mass_support := fun p _hp n hn => commonPrimeSieveProbability_zero_of_outside _ _ _ _ _ _ p n hn
    mass_sum_one := fun p hp => sum_commonPrimeSieveProbability_eq_one
      (H.totalMass_pos hy hLpos herror hp)
    mass_atom_bound := hatom m B hm hlogk hdim hB (sourceIntervalLength c x) hinterval.1 h hadm H
    pinned_mean := fun Q hQ hxQ hQy j =>
      H.pinned_probability_error hxpos hy hLpos herror hQ hxQ hQy j
  }⟩

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_nonempty_sourceProbabilityData
