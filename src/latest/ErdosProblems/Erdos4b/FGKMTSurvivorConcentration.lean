/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTFiniteConcentration

/-! # Concentration of the literal random-residue survivor count -/

namespace Erdos4b.FGKMT

open Filter
open scoped BigOperators

theorem residueExpectation_survivor_square_le {S : Finset ℕ}
    (hS : ∀ p ∈ S, 0 < p) {T : Finset ℤ} {e : ℝ} (he : 0 ≤ e)
    (hpair : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      residueAvoidanceMass S ({i} ∪ {j}) ≤ (1 + e) * residueSieveDensity S ^ 2) :
    residueExpectation S (fun a => ((residueSurvivorSet S T a).card : ℝ) ^ 2) ≤
      (T.card : ℝ) * residueSieveDensity S +
        (1 + e) * ((T.card : ℝ) * residueSieveDensity S) ^ 2 := by
  classical
  have hexact : residueExpectation S
      (fun a => ((residueSurvivorSet S T a).card : ℝ) ^ 2) =
      ∑ i ∈ T, ∑ j ∈ T, residueAvoidanceMass S ({i} ∪ {j}) := by
    simpa only [one_mul, residueSurvivorSet_card_eq_sum] using
      residueExpectation_weighted_indicator_square S T (fun _ => 1) (fun n => {n})
  rw [hexact]
  calc
    _ ≤ ∑ i ∈ T, ∑ j ∈ T,
        ((1 + e) * residueSieveDensity S ^ 2 +
          if i = j then residueSieveDensity S else 0) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : i = j
      · subst j
        rw [Finset.union_self, residueAvoidanceMass_singleton hS, if_pos rfl]
        have hk : 0 ≤ (1 + e) * residueSieveDensity S ^ 2 :=
          mul_nonneg (by linarith) (sq_nonneg _)
        linarith
      · rw [if_neg hij, add_zero]
        exact hpair i hi j hj hij
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
      have hdiag (i : ℤ) (hi : i ∈ T) :
          (∑ j ∈ T, if i = j then residueSieveDensity S else 0) =
            residueSieveDensity S := by simp [hi]
      rw [Finset.sum_congr rfl hdiag]
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

theorem residueSurvivor_count_variance_le {S : Finset ℕ}
    (hS : ∀ p ∈ S, 0 < p) {T : Finset ℤ} {e : ℝ} (he : 0 ≤ e)
    (hpair : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      residueAvoidanceMass S ({i} ∪ {j}) ≤ (1 + e) * residueSieveDensity S ^ 2) :
    residueExpectation S (fun a =>
      (((residueSurvivorSet S T a).card : ℝ) -
        (T.card : ℝ) * residueSieveDensity S) ^ 2) ≤
      e * ((T.card : ℝ) * residueSieveDensity S) ^ 2 +
        (T.card : ℝ) * residueSieveDensity S := by
  have hcenter := finite_centered_second_moment (residueAssignmentMass S)
    (fun a => ((residueSurvivorSet S T a).card : ℝ))
    ((T.card : ℝ) * residueSieveDensity S) (residueAssignmentMass_sum hS)
  change residueExpectation S _ = residueExpectation S _ -
    2 * ((T.card : ℝ) * residueSieveDensity S) * residueExpectation S _ +
      ((T.card : ℝ) * residueSieveDensity S) ^ 2 at hcenter
  rw [residueExpectation_survivor_count hS] at hcenter
  rw [hcenter]
  have hsecond := residueExpectation_survivor_square_le hS he hpair
  nlinarith

theorem residueSurvivor_count_tail_le {S : Finset ℕ}
    (hS : ∀ p ∈ S, 0 < p) {T : Finset ℤ} {e r : ℝ} (he : 0 ≤ e)
    (hpair : ∀ i ∈ T, ∀ j ∈ T, i ≠ j →
      residueAvoidanceMass S ({i} ∪ {j}) ≤ (1 + e) * residueSieveDensity S ^ 2)
    (hM : 0 < (T.card : ℝ) * residueSieveDensity S) (hr : 0 < r) :
    (∑ a : ResidueAssignment S,
      if r * ((T.card : ℝ) * residueSieveDensity S) ≤
          |((residueSurvivorSet S T a).card : ℝ) -
            (T.card : ℝ) * residueSieveDensity S|
        then residueAssignmentMass S a else 0) ≤
      (e + 1 / ((T.card : ℝ) * residueSieveDensity S)) / r ^ 2 := by
  have htail := finite_square_tail_le (residueAssignmentMass S)
    (fun a => ((residueSurvivorSet S T a).card : ℝ))
    (residueAssignmentMass_nonneg S) ((T.card : ℝ) * residueSieveDensity S)
    (mul_pos hr hM)
  have hvar := residueSurvivor_count_variance_le hS he hpair
  refine htail.trans ((div_le_div_of_nonneg_right hvar (sq_nonneg _)).trans_eq ?_)
  have hT0 := (mul_ne_zero_iff.mp hM.ne').1
  have hσ0 := (mul_ne_zero_iff.mp hM.ne').2
  field_simp [hr.ne', hT0, hσ0]

theorem eventually_uniform_survivor_concentration {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ x : ℕ in atTop, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, Real.log (x : ℝ) ^ 20 < (p : ℝ)) →
      ∀ T : Finset ℤ, T.Nonempty → (∀ n ∈ T, |(n : ℝ)| ≤ (x : ℝ) ^ A) →
      ∀ r : ℝ, 0 < r →
      (∑ a : ResidueAssignment S,
        if r * ((T.card : ℝ) * residueSieveDensity S) ≤
            |((residueSurvivorSet S T a).card : ℝ) -
              (T.card : ℝ) * residueSieveDensity S|
          then residueAssignmentMass S a else 0) ≤
        (48 * (A + 1) / Real.log (x : ℝ) ^ 16 +
          1 / ((T.card : ℝ) * residueSieveDensity S)) / r ^ 2 := by
  classical
  filter_upwards [eventually_uniform_residue_correlation hA,
    eventually_residueSieveCutoff_bounds] with x hcor hcut
  intro S hS hrough T hT hheight r hr
  have hσ := residueSieveDensity_pos (fun p hp => (hS p hp).one_lt)
  have hM : 0 < (T.card : ℝ) * residueSieveDensity S :=
    mul_pos (by exact_mod_cast Finset.card_pos.mpr hT) hσ
  apply residueSurvivor_count_tail_le (fun p hp => (hS p hp).pos)
    (by positivity) _ hM hr
  intro i hi j hj hij
  have hsize : (({i} ∪ {j} : Finset ℤ).card : ℝ) ≤ Real.log (x : ℝ) := by
    simpa [Finset.card_pair hij] using hcut.1
  have hN : ∀ n ∈ ({i} ∪ {j} : Finset ℤ), |(n : ℝ)| ≤ (x : ℝ) ^ A := by
    intro n hn
    simp only [Finset.mem_union, Finset.mem_singleton] at hn
    rcases hn with rfl | rfl
    · exact hheight _ hi
    · exact hheight _ hj
  have hbound := hcor S hS hrough ({i} ∪ {j}) hsize hN
  have hcard : ({i} ∪ {j} : Finset ℤ).card = 2 := by simp [hij]
  rw [hcard] at hbound
  apply (div_le_iff₀ (sq_pos_of_pos hσ)).mp
  linarith [(abs_le.mp hbound).2]

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.residueSurvivor_count_tail_le
#print axioms Erdos4b.FGKMT.eventually_uniform_survivor_concentration
