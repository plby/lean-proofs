/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTConditionalResidue

/-! # Conditional tuple concentration, retaining overlap outside the pin -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

theorem conditionalResidueWeighted_expectation_error {α : Type*}
    (S : Finset ℕ) (q : ℤ) (J : Finset α) (b : α → ℝ) (N : α → Finset ℤ)
    (hb : ∀ j ∈ J, 0 ≤ b j) (hsum : ∑ j ∈ J, b j = 1) {s e : ℝ}
    (hpoint : ∀ j ∈ J, |conditionalAvoidanceMass S q (N j) - s| ≤ e * s) :
    |conditionalResidueExpectation S q
        (fun a => ∑ j ∈ J, b j * residueAvoidanceIndicator S (N j) a) - s| ≤ e * s := by
  rw [conditionalResidueExpectation_weighted_sum]
  have hsub : (∑ j ∈ J, b j * conditionalAvoidanceMass S q (N j)) - s =
      ∑ j ∈ J, b j * (conditionalAvoidanceMass S q (N j) - s) := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  rw [hsub]
  calc
    _ ≤ ∑ j ∈ J, |b j * (conditionalAvoidanceMass S q (N j) - s)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j ∈ J, b j * (e * s) := by
      apply Finset.sum_le_sum
      intro j hj
      rw [abs_mul, abs_of_nonneg (hb j hj)]
      exact mul_le_mul_of_nonneg_left (hpoint j hj) (hb j hj)
    _ = _ := by rw [← Finset.sum_mul, hsum, one_mul]

theorem conditionalResidueWeighted_second_moment_le {α : Type*} {S : Finset ℕ}
    (hS : ∀ p ∈ S, 1 < p) (q : ℤ) (J : Finset α) (b : α → ℝ) (N : α → Finset ℤ)
    (hb : ∀ j ∈ J, 0 ≤ b j) (hsum : ∑ j ∈ J, b j = 1)
    {s e : ℝ} (he : 0 ≤ e)
    (hpair : ∀ i ∈ J, ∀ j ∈ J, Disjoint ((N i).erase q) ((N j).erase q) →
      conditionalAvoidanceMass S q (N i ∪ N j) ≤ (1 + e) * s ^ 2) :
    conditionalResidueExpectation S q
        (fun a => (∑ j ∈ J, b j * residueAvoidanceIndicator S (N j) a) ^ 2) ≤
      (1 + e) * s ^ 2 + residueTupleOverlapMass J b (fun j => (N j).erase q) := by
  classical
  rw [conditionalResidueExpectation_weighted_square]
  calc
    _ ≤ ∑ i ∈ J, ∑ j ∈ J,
        ((b i * b j) * ((1 + e) * s ^ 2) +
          if Disjoint ((N i).erase q) ((N j).erase q) then 0 else b i * b j) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      have hbij := mul_nonneg (hb i hi) (hb j hj)
      by_cases hd : Disjoint ((N i).erase q) ((N j).erase q)
      · rw [if_pos hd, add_zero]
        exact mul_le_mul_of_nonneg_left (hpair i hi j hj hd) hbij
      · rw [if_neg hd]
        have htriv := mul_le_mul_of_nonneg_left
          (conditionalAvoidanceMass_le_one hS q (N i ∪ N j)) hbij
        have hmain : 0 ≤ (b i * b j) * ((1 + e) * s ^ 2) :=
          mul_nonneg hbij (mul_nonneg (by linarith) (sq_nonneg _))
        linarith
    _ = _ := by
      simp only [Finset.sum_add_distrib]
      congr 1
      simp only [← Finset.sum_mul, ← Finset.mul_sum, hsum, mul_one, one_mul]

theorem conditionalResidueWeighted_tail_le {α : Type*} {S : Finset ℕ}
    (hS : ∀ p ∈ S, 1 < p) (q : ℤ) (J : Finset α) (b : α → ℝ) (N : α → Finset ℤ)
    (hb : ∀ j ∈ J, 0 ≤ b j) (hsum : ∑ j ∈ J, b j = 1)
    {s e r : ℝ} (hs : 0 < s) (he : 0 ≤ e) (hr : 0 < r)
    (hpoint : ∀ j ∈ J, |conditionalAvoidanceMass S q (N j) - s| ≤ e * s)
    (hpair : ∀ i ∈ J, ∀ j ∈ J, Disjoint ((N i).erase q) ((N j).erase q) →
      conditionalAvoidanceMass S q (N i ∪ N j) ≤ (1 + e) * s ^ 2) :
    (∑ a : ResidueAssignment S,
      if r * s ≤ |(∑ j ∈ J, b j * residueAvoidanceIndicator S (N j) a) - s|
        then conditionalResidueMass S q a else 0) ≤
      (3 * e * s ^ 2 + residueTupleOverlapMass J b (fun j => (N j).erase q)) /
        (r * s) ^ 2 := by
  exact finite_concentration_of_moments (conditionalResidueMass S q) _
    (conditionalResidueMass_nonneg hS q) (conditionalResidueMass_sum hS q) hs hr
    (conditionalResidueWeighted_expectation_error S q J b N hb hsum hpoint)
    (conditionalResidueWeighted_second_moment_le hS q J b N hb hsum he hpair)

theorem inter_eq_singleton_of_disjoint_erase {N M : Finset ℤ} {q : ℤ}
    (hN : q ∈ N) (hM : q ∈ M) (hd : Disjoint (N.erase q) (M.erase q)) :
    N ∩ M = {q} := by
  classical
  ext n
  constructor
  · intro hn
    apply Finset.mem_singleton.mpr
    by_contra hne
    exact Finset.disjoint_left.mp hd
      (Finset.mem_erase.mpr ⟨hne, (Finset.mem_inter.mp hn).1⟩)
      (Finset.mem_erase.mpr ⟨hne, (Finset.mem_inter.mp hn).2⟩)
  · intro hn
    have heq := Finset.mem_singleton.mp hn
    subst n
    exact Finset.mem_inter.mpr ⟨hN, hM⟩

theorem eventually_uniform_conditional_residue_concentration {A : ℝ} (hA : 0 ≤ A) :
    ∀ᶠ x : ℕ in atTop, ∀ (α : Type*) (S : Finset ℕ),
      (∀ p ∈ S, p.Prime) → (∀ p ∈ S, Real.log (x : ℝ) ^ 20 < (p : ℝ)) →
      ∀ (q : ℤ) (J : Finset α) (b : α → ℝ) (N : α → Finset ℤ) (k : ℕ),
      (∀ j ∈ J, 0 ≤ b j) → (∑ j ∈ J, b j = 1) →
      (∀ j ∈ J, q ∈ N j) → (∀ j ∈ J, (N j).card = k) →
      2 * (k : ℝ) ≤ Real.log (x : ℝ) →
      (∀ j ∈ J, ∀ n ∈ N j, |(n : ℝ)| ≤ (x : ℝ) ^ A) →
      ∀ r : ℝ, 0 < r →
      (∑ a : ResidueAssignment S,
        if r * residueSieveDensity S ^ (k - 1) ≤
            |(∑ j ∈ J, b j * residueAvoidanceIndicator S (N j) a) -
              residueSieveDensity S ^ (k - 1)|
          then conditionalResidueMass S q a else 0) ≤
        (3 * (48 * (A + 1) / Real.log (x : ℝ) ^ 16) *
            (residueSieveDensity S ^ (k - 1)) ^ 2 +
          residueTupleOverlapMass J b (fun j => (N j).erase q)) /
          (r * residueSieveDensity S ^ (k - 1)) ^ 2 := by
  classical
  filter_upwards [eventually_uniform_residue_correlation hA] with x hcor
  intro α S hS hrough q J b N k hb hsum hpin hcard hk hheight r hr
  have hσ := residueSieveDensity_pos (fun p hp => (hS p hp).one_lt)
  apply conditionalResidueWeighted_tail_le (fun p hp => (hS p hp).one_lt) q J b N hb hsum
    (pow_pos hσ (k - 1)) (by positivity) hr
  · intro j hj
    have hjk : ((N j).card : ℝ) ≤ Real.log (x : ℝ) := by
      rw [hcard j hj]
      have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      linarith
    simpa only [hcard j hj] using conditionalResidue_correlation_absolute_error hσ (hpin j hj)
      (hcor S hS hrough (N j) hjk (hheight j hj))
  · intro i hi j hj hd
    have hinter := inter_eq_singleton_of_disjoint_erase (hpin i hi) (hpin j hj) hd
    have hsumcard := Finset.card_union_add_card_inter (N i) (N j)
    rw [hinter, Finset.card_singleton, hcard i hi, hcard j hj] at hsumcard
    have hkpos : 0 < k := by
      rw [← hcard i hi]
      exact Finset.card_pos.mpr ⟨q, hpin i hi⟩
    have hijcard : (N i ∪ N j).card - 1 = (k - 1) * 2 := by omega
    have hijsize : ((N i ∪ N j).card : ℝ) ≤ Real.log (x : ℝ) := by
      have hle : (N i ∪ N j).card ≤ 2 * k := by omega
      have hleR : ((N i ∪ N j).card : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast hle
      exact hleR.trans hk
    have hijheight : ∀ n ∈ N i ∪ N j, |(n : ℝ)| ≤ (x : ℝ) ^ A := by
      intro n hn
      rcases Finset.mem_union.mp hn with hn | hn
      · exact hheight i hi n hn
      · exact hheight j hj n hn
    have hc := conditionalResidue_correlation_absolute_error hσ
      (Finset.mem_union_left (N j) (hpin i hi))
      (hcor S hS hrough (N i ∪ N j) hijsize hijheight)
    rw [hijcard, pow_mul] at hc
    linarith [(abs_le.mp hc).2]

open scoped Classical in
theorem conditionalResidue_event_identity {S : Finset ℕ} (hσ : 0 < residueSieveDensity S)
    (q : ℤ) (E : ResidueAssignment S → Prop) :
    (∑ a : ResidueAssignment S,
      if residueAssignmentAvoids S {q} a ∧ E a then residueAssignmentMass S a else 0) =
        residueSieveDensity S *
          (∑ a : ResidueAssignment S, if E a then conditionalResidueMass S q a else 0) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases hq : residueAssignmentAvoids S {q} a <;> by_cases he : E a <;>
    simp [hq, he, conditionalResidueMass, residueAvoidanceIndicator]
  field_simp

end

end Erdos4b.FGKMT
