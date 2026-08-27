/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTBadPinnedVertexCount

/-! # The normalized tuple mass lost by discarding bad prime labels -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

theorem finite_bad_mass_le {Ω : Type*} [Fintype Ω] (μ Z : Ω → ℝ) (E : Ω → Prop)
    [DecidablePred E]
    (hμ : ∀ a, 0 ≤ μ a) (hsum : ∑ a, μ a = 1) {η δ : ℝ} (hδ : 0 ≤ δ)
    (hmean : (∑ a, μ a * Z a) ≤ 1 + η) (hgood : ∀ a, ¬E a → 1 - δ ≤ Z a) :
    (∑ a, μ a * (if E a then Z a else 0)) ≤ η + δ + ∑ a, if E a then μ a else 0 := by
  classical
  calc
    _ ≤ ∑ a, (μ a * Z a - (1 - δ) * μ a + if E a then μ a else 0) := by
      apply Finset.sum_le_sum
      intro a _ha
      by_cases he : E a
      · rw [if_pos he, if_pos he]
        nlinarith [mul_nonneg (hμ a) hδ]
      · rw [if_neg he, if_neg he, mul_zero, add_zero]
        have h := mul_le_mul_of_nonneg_left (hgood a he) (hμ a)
        nlinarith
    _ = (∑ a, μ a * Z a) - (1 - δ) + ∑ a, if E a then μ a else 0 := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        hsum, mul_one]
    _ ≤ _ := by linarith

theorem eventually_source_tuple_mean_error {c e : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, Real.log (x : ℝ) ^ 20 < (p : ℝ)) →
      ∀ p ∈ commonPinnedPrimeSet (x / 2) x,
      |residueExpectation S (D.tupleSurvivalMass S p) - residueSieveDensity S ^ D.dimension| ≤
        (144 / Real.log (x : ℝ) ^ 16) * residueSieveDensity S ^ D.dimension := by
  filter_upwards [eventually_uniform_residue_correlation (by norm_num : (0 : ℝ) ≤ 2),
    eventually_sourceTuple_ranges hc, eventually_sourceIntervalLength_bounds hc]
    with x hcor hranges hy
  intro D S hS hrough p hp
  have hσ := residueSieveDensity_pos (fun l hl => (hS l hl).one_lt)
  have hp0 := (mem_commonPinnedPrimeSet.mp hp).2.2.pos
  have hk : (D.dimension : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) := by
    simpa only [D.dimension_eq] using growingSieveDimension_le x
  have hsize : (D.dimension : ℝ) ≤ Real.log (x : ℝ) := by
    have hh : 2 * (D.dimension : ℝ) ≤ Real.log (x : ℝ) := by
      simpa only [D.dimension_eq] using hranges.1
    have hk0 : (0 : ℝ) ≤ D.dimension := Nat.cast_nonneg _
    linarith
  apply residueWeighted_expectation_error S (integerWeightWindow (sourceIntervalLength c x))
    (D.mass p) (D.residueTuple p) (fun n _hn => D.mass_nonneg p hp n) (D.mass_sum_one p hp)
  intro n hn
  have hcard : ((D.residueTuple p n).card : ℝ) ≤ Real.log (x : ℝ) := by
    simpa only [D.residueTuple_card hp0 n] using hsize
  have hheight : ∀ m ∈ D.residueTuple p n, |(m : ℝ)| ≤ (x : ℝ) ^ (2 : ℝ) := by
    simpa only [Real.rpow_two] using D.residueTuple_height (hy.2.2 D.dimension hk) hranges.2 hp hn
  have h := residue_correlation_absolute_error hσ (hcor S hS hrough _ hcard hheight)
  norm_num only [show (48 : ℝ) * (2 + 1) = 144 from by norm_num,
    D.residueTuple_card hp0 n] at h
  exact h

theorem source_bad_mass_log_budget {L : ℝ} (hL : 5 ≤ L) :
    144 / L ^ 16 + 1 / L ^ 3 + 2 / L ^ 6 ≤ 4 / L ^ 3 := by
  have hLpos : 0 < L := by linarith
  have h144 : (144 : ℝ) ≤ L ^ 13 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hL 13
    norm_num at h
    linarith
  have hfirst : 144 / L ^ 16 ≤ 1 / L ^ 3 := by
    calc
      _ = (144 / L ^ 13) * (1 / L ^ 3) := by field_simp [hLpos.ne']
      _ ≤ 1 * (1 / L ^ 3) := mul_le_mul_of_nonneg_right
        ((div_le_one (pow_pos hLpos 13)).mpr h144) (by positivity)
      _ = _ := one_mul _
  have hpower : L ^ 3 ≤ L ^ 6 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (by linarith : 1 ≤ L) 3
    norm_num at h
    nlinarith [sq_nonneg (L ^ 3 - 1)]
  have hsecond : 2 / L ^ 6 ≤ 2 / L ^ 3 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos hLpos 3) hpower
  calc
    _ ≤ 1 / L ^ 3 + 1 / L ^ 3 + 2 / L ^ 3 := add_le_add (add_le_add hfirst le_rfl) hsecond
    _ = _ := by ring

theorem eventually_source_badPrime_mass_mean_le {c e : ℝ} (hc : 0 < c) (he : e ≤ 1 / 12) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, Real.log (x : ℝ) ^ 20 < (p : ℝ)) →
      (∀ p ∈ S, p ≤ x) → ∀ p ∈ commonPinnedPrimeSet (x / 2) x,
      residueExpectation S (fun a => if p ∈ D.badTuplePrimes S a then
          D.tupleSurvivalMass S p a / residueSieveDensity S ^ D.dimension else 0) ≤
        4 / Real.log (x : ℝ) ^ 3 := by
  classical
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_source_tuple_mean_error (e := e) hc,
    eventually_source_tuple_bad_probability hc he,
    hlog.eventually (eventually_ge_atTop (5 : ℝ))] with x hmean hprob hL
  intro D S hS hrough hupper p hp
  have hσ := residueSieveDensity_pos (fun l hl => (hS l hl).one_lt)
  have hM := pow_pos hσ D.dimension
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hmeanNorm : (∑ a : ResidueAssignment S, residueAssignmentMass S a *
      (D.tupleSurvivalMass S p a / residueSieveDensity S ^ D.dimension)) ≤
        1 + 144 / Real.log (x : ℝ) ^ 16 := by
    simp only [← mul_div_assoc, ← Finset.sum_div]
    apply (div_le_iff₀ hM).mpr
    have h := (abs_le.mp (hmean D S hS hrough p hp)).2
    change residueExpectation S (D.tupleSurvivalMass S p) ≤ _
    nlinarith
  have hgood (a : ResidueAssignment S) (ha : p ∉ D.badTuplePrimes S a) :
      1 - 1 / Real.log (x : ℝ) ^ 3 ≤
        D.tupleSurvivalMass S p a / residueSieveDensity S ^ D.dimension := by
    have herr : |D.tupleSurvivalMass S p a / residueSieveDensity S ^ D.dimension - 1| ≤
        1 / Real.log (x : ℝ) ^ 3 := by
      apply le_of_not_gt
      intro hbad
      exact ha (Finset.mem_filter.mpr ⟨hp, hbad⟩)
    linarith [(abs_le.mp herr).1]
  have h := finite_bad_mass_le (residueAssignmentMass S)
    (fun a => D.tupleSurvivalMass S p a / residueSieveDensity S ^ D.dimension)
    (fun a => p ∈ D.badTuplePrimes S a) (residueAssignmentMass_nonneg S)
    (residueAssignmentMass_sum (fun l hl => (hS l hl).pos)) (by positivity) hmeanNorm hgood
  have hbadProb : (∑ a : ResidueAssignment S,
      if p ∈ D.badTuplePrimes S a then residueAssignmentMass S a else 0) ≤
        2 / Real.log (x : ℝ) ^ 6 := by
    simpa only [SourceProbabilityData.badTuplePrimes, Finset.mem_filter, hp, true_and] using
      hprob D S hS hrough hupper p hp
  exact h.trans ((add_le_add le_rfl hbadProb).trans (source_bad_mass_log_budget hL))

open scoped Classical in
def SourceProbabilityData.badTupleMass {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (a : ResidueAssignment S) : ℝ :=
  ∑ p ∈ commonPinnedPrimeSet (x / 2) x,
    if p ∈ D.badTuplePrimes S a then D.tupleSurvivalMass S p a / residueSieveDensity S ^ D.dimension
    else 0

theorem SourceProbabilityData.badTupleMass_nonneg {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (a : ResidueAssignment S) : 0 ≤ D.badTupleMass S a := by
  classical
  have hσ := residueSieveDensity_pos (fun p hp => (hS p hp).one_lt)
  apply Finset.sum_nonneg
  intro p hp
  split_ifs
  · exact div_nonneg (D.tupleSurvivalMass_nonneg S a hp) (pow_nonneg hσ.le _)
  · exact le_rfl

theorem eventually_source_badTupleMass_mean_le {c e : ℝ} (hc : 0 < c) (he : e ≤ 1 / 12) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, Real.log (x : ℝ) ^ 20 < (p : ℝ)) →
      (∀ p ∈ S, p ≤ x) → residueExpectation S (D.badTupleMass S) ≤
        8 * (x : ℝ) / Real.log (x : ℝ) ^ 4 := by
  classical
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_source_badPrime_mass_mean_le hc he,
    eventually_commonPinnedPrimeSet_card_bounds,
    hlog.eventually (eventually_gt_atTop (0 : ℝ))] with x hmean hP hL
  intro D S hS hrough hupper
  unfold SourceProbabilityData.badTupleMass
  rw [residueExpectation_sum]
  calc
    _ ≤ ∑ _p ∈ commonPinnedPrimeSet (x / 2) x, 4 / Real.log (x : ℝ) ^ 3 :=
      Finset.sum_le_sum fun p hp => hmean D S hS hrough hupper p hp
    _ = ((commonPinnedPrimeSet (x / 2) x).card : ℝ) * (4 / Real.log (x : ℝ) ^ 3) := by simp
    _ ≤ (2 * (x : ℝ) / Real.log (x : ℝ)) * (4 / Real.log (x : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_right hP.2 (by positivity)
    _ = _ := by field_simp [hL.ne']; ring

end

end Erdos4b.FGKMT
