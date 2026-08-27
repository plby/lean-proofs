/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedConcentration

/-! # Logarithmic tail bounds at a surviving source vertex -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

theorem eventually_pinnedOverlap_relative_le :
    ∀ᶠ x : ℕ in atTop, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, p ≤ x) →
      ∀ k : ℕ, (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
        (4 * (k : ℝ) * Real.log (x : ℝ) ^ 2 * (x : ℝ) ^ (-2 / 3 + 1 / 12 : ℝ)) /
          (residueSieveDensity S ^ (k - 1)) ^ 2 ≤ 1 / Real.log (x : ℝ) ^ 12 := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow4 := ((isLittleO_log_rpow_rpow_atTop ((4 : ℕ) : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 12)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  have hpow12 := ((isLittleO_log_rpow_rpow_atTop ((12 : ℕ) : ℝ)
    (by norm_num : (0 : ℝ) < 5 / 12)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_residueSieveDensity_inv_square_pow_le_rpow
    (by norm_num : (0 : ℝ) < 1 / 12), hpow4, hpow12,
    hlog.eventually (eventually_ge_atTop (4 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with x hσpow h4 h12 hL hx
  intro S hS hupper k hk
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hlog0 := hLpos.le
  simp only [Function.comp_apply, Real.rpow_natCast, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hlog0 4),
    abs_of_nonneg (Real.rpow_nonneg hxR.le (1 / 12 : ℝ))] at h4
  simp only [Function.comp_apply, Real.rpow_natCast, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hlog0 12),
    abs_of_nonneg (Real.rpow_nonneg hxR.le (5 / 12 : ℝ))] at h12
  have hkL := hk.trans (Real.rpow_le_self_of_one_le (by linarith) (by norm_num))
  have hfactor : 4 * (k : ℝ) * Real.log (x : ℝ) ^ 2 ≤ (x : ℝ) ^ (1 / 12 : ℝ) := by
    refine le_trans ?_ h4
    calc
      _ ≤ 4 * Real.log (x : ℝ) * Real.log (x : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hkL (by norm_num)) (by positivity)
      _ = 4 * Real.log (x : ℝ) ^ 3 := by ring
      _ ≤ Real.log (x : ℝ) * Real.log (x : ℝ) ^ 3 :=
        mul_le_mul_of_nonneg_right hL (by positivity)
      _ = _ := by ring
  have hk' : ((k - 1 : ℕ) : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) :=
    (Nat.cast_le.mpr (Nat.sub_le k 1)).trans hk
  have hnorm := hσpow S hS hupper (k - 1) hk'
  have hi0 : 0 ≤ ((residueSieveDensity S ^ (k - 1)) ^ 2)⁻¹ := by positivity
  apply (le_div_iff₀ (pow_pos hLpos 12)).mpr
  rw [div_eq_mul_inv]
  calc
    _ ≤ (((x : ℝ) ^ (1 / 12 : ℝ) * (x : ℝ) ^ (-2 / 3 + 1 / 12 : ℝ)) *
        (x : ℝ) ^ (1 / 12 : ℝ)) * (x : ℝ) ^ (5 / 12 : ℝ) := by
      apply mul_le_mul
      · exact mul_le_mul
          (mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hxR.le _))
          hnorm hi0 (by positivity)
      · exact h12
      · exact pow_nonneg hlog0 12
      · positivity
    _ = 1 := by
      rw [← Real.rpow_add hxR, ← Real.rpow_add hxR, ← Real.rpow_add hxR]
      norm_num

theorem eventually_source_pinned_bad_probability {c e : ℝ} (hc : 0 < c) (he : e ≤ 1 / 12) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, Real.log (x : ℝ) ^ 20 < (p : ℝ)) →
      (∀ p ∈ S, p ≤ x) → ∀ q ∈ sourceSievingPrimes c x,
      (∑ a : ResidueAssignment S,
        if 1 / Real.log (x : ℝ) ^ 3 <
            |D.pinnedNormalizedSurvival S q a / residueSieveDensity S ^ (D.dimension - 1) - 1|
          then conditionalResidueMass S q a else 0) ≤ 2 / Real.log (x : ℝ) ^ 6 := by
  classical
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_source_pinned_concentration (e := e) hc,
    eventually_pinnedOverlap_relative_le, hlog.eventually (eventually_ge_atTop (5 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with x htail hoverlap hL hx
  intro D S hS hrough hupper q hq
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hσ := residueSieveDensity_pos (fun p hp => (hS p hp).one_lt)
  have hM := pow_pos hσ (D.dimension - 1)
  have hr : 0 < 1 / Real.log (x : ℝ) ^ 3 := by positivity
  have hk : (D.dimension : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) := by
    simpa only [D.dimension_eq] using growingSieveDimension_le x
  have hcap : (x : ℝ) ^ (-2 / 3 + e : ℝ) ≤ (x : ℝ) ^ (-2 / 3 + 1 / 12 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx) (by linarith)
  have hrelative := (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcap
      (by positivity : 0 ≤ 4 * (D.dimension : ℝ) * Real.log (x : ℝ) ^ 2))
    (sq_nonneg (residueSieveDensity S ^ (D.dimension - 1)))).trans
      (hoverlap S hS hupper D.dimension hk)
  have h := (htail D S hS hrough q hq _ hr).trans
    (source_tuple_tail_algebra hL hM hrelative)
  refine le_trans ?_ h
  apply Finset.sum_le_sum
  intro a _ha
  by_cases hbad : 1 / Real.log (x : ℝ) ^ 3 <
      |D.pinnedNormalizedSurvival S q a / residueSieveDensity S ^ (D.dimension - 1) - 1|
  · rw [if_pos hbad]
    have heq : D.pinnedNormalizedSurvival S q a / residueSieveDensity S ^ (D.dimension - 1) - 1 =
        (D.pinnedNormalizedSurvival S q a - residueSieveDensity S ^ (D.dimension - 1)) /
          residueSieveDensity S ^ (D.dimension - 1) := by field_simp
    rw [heq, abs_div, abs_of_pos hM] at hbad
    have hlarge := ((lt_div_iff₀ hM).mp hbad).le
    rw [if_pos hlarge]
  · rw [if_neg hbad]
    split_ifs
    · exact conditionalResidueMass_nonneg (fun p hp => (hS p hp).one_lt) q a
    · exact le_rfl

open scoped Classical in
theorem eventually_source_surviving_pinned_bad_probability {c e : ℝ}
    (hc : 0 < c) (he : e ≤ 1 / 12) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, Real.log (x : ℝ) ^ 20 < (p : ℝ)) →
      (∀ p ∈ S, p ≤ x) → ∀ q ∈ sourceSievingPrimes c x,
      (∑ a : ResidueAssignment S,
        if residueAssignmentAvoids S {(q : ℤ)} a ∧
            1 / Real.log (x : ℝ) ^ 3 <
              |D.pinnedNormalizedSurvival S q a / residueSieveDensity S ^ (D.dimension - 1) - 1|
          then residueAssignmentMass S a else 0) ≤
        2 * residueSieveDensity S / Real.log (x : ℝ) ^ 6 := by
  classical
  filter_upwards [eventually_source_pinned_bad_probability hc he] with x hprob
  intro D S hS hrough hupper q hq
  have hσ := residueSieveDensity_pos (fun p hp => (hS p hp).one_lt)
  rw [conditionalResidue_event_identity hσ]
  calc
    _ ≤ residueSieveDensity S * (2 / Real.log (x : ℝ) ^ 6) :=
      mul_le_mul_of_nonneg_left (hprob D S hS hrough hupper q hq) hσ.le
    _ = _ := by ring

end

end Erdos4b.FGKMT
