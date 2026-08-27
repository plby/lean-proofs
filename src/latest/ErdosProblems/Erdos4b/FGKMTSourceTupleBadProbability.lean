/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTResidueDensityLower

/-! # Explicit probability of a bad source tuple -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

theorem eventually_source_tuple_overlap_relative_le :
    ∀ᶠ x : ℕ in atTop, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, p ≤ x) →
      ∀ k : ℕ, (k : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) →
        ((k : ℝ) ^ 2 * (x : ℝ) ^ (-2 / 3 + 1 / 12 : ℝ)) /
          (residueSieveDensity S ^ k) ^ 2 ≤ 1 / Real.log (x : ℝ) ^ 12 := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow2 := ((isLittleO_log_rpow_rpow_atTop ((2 : ℕ) : ℝ)
    (by norm_num : (0 : ℝ) < 1 / 12)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  have hpow12 := ((isLittleO_log_rpow_rpow_atTop ((12 : ℕ) : ℝ)
    (by norm_num : (0 : ℝ) < 5 / 12)).comp_tendsto
      (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_residueSieveDensity_inv_square_pow_le_rpow
    (by norm_num : (0 : ℝ) < 1 / 12), hpow2, hpow12,
    hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with x hσpow h2 h12 hL hx
  intro S hS hupper k hk
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hlog0 := hLpos.le
  simp only [Function.comp_apply, Real.rpow_natCast, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hlog0 2),
    abs_of_nonneg (Real.rpow_nonneg hxR.le (1 / 12 : ℝ))] at h2
  simp only [Function.comp_apply, Real.rpow_natCast, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hlog0 12),
    abs_of_nonneg (Real.rpow_nonneg hxR.le (5 / 12 : ℝ))] at h12
  have hkL := hk.trans (Real.rpow_le_self_of_one_le hL (by norm_num))
  have hk2 := (pow_le_pow_left₀ (Nat.cast_nonneg k) hkL 2).trans h2
  have hσpos := residueSieveDensity_pos (fun p hp => (hS p hp).one_lt)
  have hi0 : 0 ≤ ((residueSieveDensity S ^ k) ^ 2)⁻¹ := by positivity
  have hnorm := hσpow S hS hupper k hk
  apply (le_div_iff₀ (pow_pos hLpos 12)).mpr
  rw [div_eq_mul_inv]
  calc
    _ ≤ (((x : ℝ) ^ (1 / 12 : ℝ) * (x : ℝ) ^ (-2 / 3 + 1 / 12 : ℝ)) *
        (x : ℝ) ^ (1 / 12 : ℝ)) * (x : ℝ) ^ (5 / 12 : ℝ) := by
      apply mul_le_mul
      · exact mul_le_mul (mul_le_mul_of_nonneg_right hk2 (Real.rpow_nonneg hxR.le _))
          hnorm hi0 (by positivity)
      · exact h12
      · exact pow_nonneg hlog0 12
      · positivity
    _ = 1 := by
      rw [← Real.rpow_add hxR, ← Real.rpow_add hxR, ← Real.rpow_add hxR]
      norm_num

theorem source_tuple_tail_algebra {L M D : ℝ} (hL : 5 ≤ L) (hM : 0 < M)
    (hD : D / M ^ 2 ≤ 1 / L ^ 12) :
    (3 * (144 / L ^ 16) * M ^ 2 + D) / ((1 / L ^ 3) * M) ^ 2 ≤ 2 / L ^ 6 := by
  have hLpos : 0 < L := by linarith
  have hL0 := hLpos.ne'
  have hid : (3 * (144 / L ^ 16) * M ^ 2 + D) / ((1 / L ^ 3) * M) ^ 2 =
      432 / L ^ 10 + (D / M ^ 2) * L ^ 6 := by
    field_simp [hL0, hM.ne']
    ring
  have h432 : (432 : ℝ) ≤ L ^ 4 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 5) hL 4
    norm_num at hh
    linarith
  have hfirst : 432 / L ^ 10 ≤ 1 / L ^ 6 := by
    have hc : 432 / L ^ 4 ≤ 1 := (div_le_one (pow_pos hLpos 4)).mpr h432
    calc
      _ = (432 / L ^ 4) * (1 / L ^ 6) := by field_simp [hL0]
      _ ≤ 1 * (1 / L ^ 6) := mul_le_mul_of_nonneg_right hc (by positivity)
      _ = _ := one_mul _
  have hsecond : (D / M ^ 2) * L ^ 6 ≤ 1 / L ^ 6 := by
    calc
      _ ≤ (1 / L ^ 12) * L ^ 6 := mul_le_mul_of_nonneg_right hD (pow_nonneg hLpos.le 6)
      _ = _ := by field_simp [hL0]
  rw [hid]
  calc
    _ ≤ 1 / L ^ 6 + 1 / L ^ 6 := add_le_add hfirst hsecond
    _ = _ := by ring

def SourceProbabilityData.tupleSurvivalMass {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (p : ℕ) (a : ResidueAssignment S) : ℝ :=
  ∑ n ∈ integerWeightWindow (sourceIntervalLength c x),
    D.mass p n * residueAvoidanceIndicator S (D.residueTuple p n) a

theorem eventually_source_tuple_bad_probability {c e : ℝ} (hc : 0 < c) (he : e ≤ 1 / 12) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, Real.log (x : ℝ) ^ 20 < (p : ℝ)) →
      (∀ p ∈ S, p ≤ x) → ∀ p ∈ commonPinnedPrimeSet (x / 2) x,
      (∑ a : ResidueAssignment S,
        if 1 / Real.log (x : ℝ) ^ 3 <
            |D.tupleSurvivalMass S p a / residueSieveDensity S ^ D.dimension - 1|
          then residueAssignmentMass S a else 0) ≤ 2 / Real.log (x : ℝ) ^ 6 := by
  classical
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_source_tuple_concentration (e := e) hc,
    eventually_source_tuple_overlap_relative_le,
    hlog.eventually (eventually_ge_atTop (5 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with x htail hoverlap hL hx
  intro D S hS hrough hupper p hp
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hσ := residueSieveDensity_pos (fun q hq => (hS q hq).one_lt)
  have hM := pow_pos hσ D.dimension
  have hr : 0 < 1 / Real.log (x : ℝ) ^ 3 := by positivity
  have hk : (D.dimension : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) := by
    simpa only [D.dimension_eq] using growingSieveDimension_le x
  have hcap : (x : ℝ) ^ (-2 / 3 + e : ℝ) ≤ (x : ℝ) ^ (-2 / 3 + 1 / 12 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hx) (by linarith)
  have hrelative := (div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcap (sq_nonneg (D.dimension : ℝ)))
    (sq_nonneg (residueSieveDensity S ^ D.dimension))).trans
      (hoverlap S hS hupper D.dimension hk)
  have h := (htail D S hS hrough p hp _ hr).trans
    (source_tuple_tail_algebra hL hM hrelative)
  refine le_trans ?_ h
  apply Finset.sum_le_sum
  intro a _ha
  by_cases hbad : 1 / Real.log (x : ℝ) ^ 3 <
      |D.tupleSurvivalMass S p a / residueSieveDensity S ^ D.dimension - 1|
  · rw [if_pos hbad]
    have heq : D.tupleSurvivalMass S p a / residueSieveDensity S ^ D.dimension - 1 =
        (D.tupleSurvivalMass S p a - residueSieveDensity S ^ D.dimension) /
          residueSieveDensity S ^ D.dimension := by field_simp
    rw [heq, abs_div, abs_of_pos hM] at hbad
    have hlarge := ((lt_div_iff₀ hM).mp hbad).le
    unfold SourceProbabilityData.tupleSurvivalMass at hlarge
    rw [if_pos hlarge]
  · rw [if_neg hbad]
    split_ifs
    · exact residueAssignmentMass_nonneg S a
    · exact le_rfl

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.eventually_source_tuple_overlap_relative_le
#print axioms Erdos4b.FGKMT.eventually_source_tuple_bad_probability
