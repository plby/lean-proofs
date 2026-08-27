/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedIncidence

/-! # Few source vertices lose substantial degree at bad prime labels -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

theorem finset_nonnegative_tail_count_le {α : Type*} (Q : Finset α) (f : α → ℝ)
    (hf : ∀ q ∈ Q, 0 ≤ f q) {θ : ℝ} (hθ : 0 < θ) :
    ((Q.filter fun q => θ < f q).card : ℝ) ≤ (∑ q ∈ Q, f q) / θ := by
  classical
  apply (le_div_iff₀ hθ).mpr
  simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
    Nat.cast_zero, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro q hq
  by_cases h : θ < f q
  · simp only [if_pos h, one_mul]
    exact h.le
  · simp only [if_neg h, zero_mul]
    exact hf q hq

open scoped Classical in
def SourceProbabilityData.lostDegreeVertices {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) (θ : ℝ)
    (a : ResidueAssignment S) : Finset ℕ :=
  (sourceSievingPrimes c x).filter fun q => θ < D.pinnedBadMass S q a

theorem eventually_source_lostDegreeCount_mean_le {c e : ℝ} (hc : 0 < c) (he : e ≤ 1 / 12) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, Real.log (x : ℝ) ^ 20 < (p : ℝ)) →
      (∀ p ∈ S, p ≤ x) → ∀ θ : ℝ, 0 < θ →
      residueExpectation S (fun a => ((D.lostDegreeVertices S θ a).card : ℝ)) ≤
        8 * (D.dimension : ℝ) * x / (Real.log (x : ℝ) ^ 4 * θ) := by
  filter_upwards [eventually_source_pinnedBadMass_mean_le hc he] with x hmean
  intro D S hS hrough hupper θ hθ
  calc
    _ ≤ residueExpectation S (fun a =>
        (∑ q ∈ sourceSievingPrimes c x, D.pinnedBadMass S q a) / θ) :=
      residueExpectation_mono S fun a =>
        finset_nonnegative_tail_count_le (sourceSievingPrimes c x) (fun q => D.pinnedBadMass S q a)
          (fun q _hq => D.pinnedBadMass_nonneg hS q a) hθ
    _ = residueExpectation S (fun a =>
        ∑ q ∈ sourceSievingPrimes c x, D.pinnedBadMass S q a) / θ := by
      simp only [residueExpectation, ← mul_div_assoc, ← Finset.sum_div]
    _ ≤ (8 * (D.dimension : ℝ) * x / Real.log (x : ℝ) ^ 4) / θ :=
      div_le_div_of_nonneg_right (hmean D S hS hrough hupper) hθ.le
    _ = _ := by ring

theorem eventually_source_lostDegreeCount_tail_le {c e : ℝ} (hc : 0 < c) (he : e ≤ 1 / 12) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, Real.log (x : ℝ) ^ 20 < (p : ℝ)) →
      (∀ p ∈ S, p ≤ x) → ∀ θ v : ℝ, 0 < θ → 0 < v →
      (∑ a : ResidueAssignment S,
        if v ≤ ((D.lostDegreeVertices S θ a).card : ℝ) then residueAssignmentMass S a else 0) ≤
        8 * (D.dimension : ℝ) * x / (Real.log (x : ℝ) ^ 4 * θ * v) := by
  filter_upwards [eventually_source_lostDegreeCount_mean_le hc he] with x hmean
  intro D S hS hrough hupper θ v hθ hv
  have ht := finite_nonnegative_tail_le (residueAssignmentMass S)
    (fun a => ((D.lostDegreeVertices S θ a).card : ℝ)) (residueAssignmentMass_nonneg S)
    (fun a => Nat.cast_nonneg _) hv
  exact ht.trans ((div_le_div_of_nonneg_right (hmean D S hS hrough hupper θ hθ) hv.le).trans_eq
    (by ring))

theorem eventually_source_lostDegreeCount_loglog_tail {c e : ℝ} (hc : 0 < c) (he : e ≤ 1 / 12) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, Real.log (x : ℝ) ^ 20 < (p : ℝ)) →
      (∀ p ∈ S, p ≤ x) →
      (∑ a : ResidueAssignment S,
        if (x : ℝ) / (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ)) ^ 2) ≤
            ((D.lostDegreeVertices S (1 / Real.log (Real.log (x : ℝ)) ^ 3) a).card : ℝ)
          then residueAssignmentMass S a else 0) ≤ 1 / Real.log (Real.log (x : ℝ)) := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsmall := ((isLittleO_log_rpow_rpow_atTop ((6 : ℕ) : ℝ)
    (by norm_num : (0 : ℝ) < 1)).comp_tendsto hlog).eventuallyLE
  filter_upwards [eventually_source_lostDegreeCount_tail_le hc he, hsmall,
    hlog.eventually (eventually_ge_atTop (8 : ℝ)), eventually_ge_atTop (1 : ℕ)]
    with x htail hsmall hL hx
  intro D S hS hrough hupper
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hx
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hlpos : 0 < Real.log (Real.log (x : ℝ)) := Real.log_pos (by linarith)
  have hk : (D.dimension : ℝ) ≤ Real.log (x : ℝ) := by
    have hdim : (D.dimension : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) := by
      simpa only [D.dimension_eq] using growingSieveDimension_le x
    exact hdim.trans (Real.rpow_le_self_of_one_le (by linarith) (by norm_num))
  have hsmall' : Real.log (Real.log (x : ℝ)) ^ 6 ≤ Real.log (x : ℝ) := by
    simpa only [Function.comp_apply, Real.rpow_natCast, Real.rpow_one, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg hlpos.le 6), abs_of_pos hLpos] using hsmall
  have hbudget : 8 * (D.dimension : ℝ) * Real.log (Real.log (x : ℝ)) ^ 6 ≤
      Real.log (x : ℝ) ^ 3 := by
    calc
      _ ≤ 8 * Real.log (x : ℝ) * Real.log (Real.log (x : ℝ)) ^ 6 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (by norm_num)) (by positivity)
      _ ≤ 8 * Real.log (x : ℝ) * Real.log (x : ℝ) :=
        mul_le_mul_of_nonneg_left hsmall' (by positivity)
      _ ≤ Real.log (x : ℝ) ^ 3 := by
        have h := mul_le_mul_of_nonneg_right hL (sq_nonneg (Real.log (x : ℝ)))
        nlinarith
  refine (htail D S hS hrough hupper _ _ (by positivity) (by positivity)).trans ?_
  have heq : 8 * (D.dimension : ℝ) * x /
      (Real.log (x : ℝ) ^ 4 * (1 / Real.log (Real.log (x : ℝ)) ^ 3) *
        ((x : ℝ) / (Real.log (x : ℝ) * Real.log (Real.log (x : ℝ)) ^ 2))) =
      8 * (D.dimension : ℝ) * Real.log (Real.log (x : ℝ)) ^ 5 / Real.log (x : ℝ) ^ 3 := by
    field_simp [hxpos.ne', hLpos.ne', hlpos.ne']
  rw [heq]
  apply (div_le_div_iff₀ (pow_pos hLpos 3) hlpos).mpr
  simpa only [pow_succ, mul_assoc, one_mul] using hbudget

end

end Erdos4b.FGKMT
