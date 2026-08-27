/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTConditionedTupleMass

/-! # Residue assignments conditioned on one surviving integer -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def conditionalResidueMass (S : Finset ℕ) (q : ℤ) (a : ResidueAssignment S) : ℝ :=
  residueAssignmentMass S a * residueAvoidanceIndicator S {q} a / residueSieveDensity S

def conditionalResidueExpectation (S : Finset ℕ) (q : ℤ)
    (f : ResidueAssignment S → ℝ) : ℝ :=
  ∑ a : ResidueAssignment S, conditionalResidueMass S q a * f a

def conditionalAvoidanceMass (S : Finset ℕ) (q : ℤ) (N : Finset ℤ) : ℝ :=
  residueAvoidanceMass S ({q} ∪ N) / residueSieveDensity S

theorem conditionalResidueMass_nonneg {S : Finset ℕ} (hS : ∀ p ∈ S, 1 < p)
    (q : ℤ) (a : ResidueAssignment S) : 0 ≤ conditionalResidueMass S q a := by
  exact div_nonneg (mul_nonneg (residueAssignmentMass_nonneg S a)
    (residueAvoidanceIndicator_nonneg S {q} a)) (residueSieveDensity_pos hS).le

theorem conditionalResidueMass_sum {S : Finset ℕ} (hS : ∀ p ∈ S, 1 < p) (q : ℤ) :
    (∑ a : ResidueAssignment S, conditionalResidueMass S q a) = 1 := by
  unfold conditionalResidueMass
  rw [← Finset.sum_div]
  change residueExpectation S (residueAvoidanceIndicator S {q}) / residueSieveDensity S = 1
  rw [residueExpectation_indicator, residueAvoidanceMass_singleton
    (fun p hp => lt_trans Nat.zero_lt_one (hS p hp))]
  exact div_self (residueSieveDensity_pos hS).ne'

theorem conditionalResidueExpectation_eq (S : Finset ℕ) (q : ℤ)
    (f : ResidueAssignment S → ℝ) :
    conditionalResidueExpectation S q f =
      residueExpectation S (fun a => residueAvoidanceIndicator S {q} a * f a) /
        residueSieveDensity S := by
  unfold conditionalResidueExpectation conditionalResidueMass residueExpectation
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

theorem conditionalResidueExpectation_indicator (S : Finset ℕ) (q : ℤ) (N : Finset ℤ) :
    conditionalResidueExpectation S q (residueAvoidanceIndicator S N) =
      conditionalAvoidanceMass S q N := by
  rw [conditionalResidueExpectation_eq]
  simp_rw [residueAvoidanceIndicator_mul]
  rw [residueExpectation_indicator]
  rfl

theorem conditionalAvoidanceMass_of_mem (S : Finset ℕ) {q : ℤ} {N : Finset ℤ}
    (hq : q ∈ N) :
    conditionalAvoidanceMass S q N = residueAvoidanceMass S N / residueSieveDensity S := by
  classical
  simp [conditionalAvoidanceMass, Finset.singleton_union, Finset.insert_eq_of_mem hq]

theorem conditionalAvoidanceMass_nonneg {S : Finset ℕ} (hS : ∀ p ∈ S, 1 < p)
    (q : ℤ) (N : Finset ℤ) : 0 ≤ conditionalAvoidanceMass S q N := by
  exact div_nonneg (residueAvoidanceMass_nonneg S _) (residueSieveDensity_pos hS).le

theorem conditionalAvoidanceMass_le_one {S : Finset ℕ} (hS : ∀ p ∈ S, 1 < p)
    (q : ℤ) (N : Finset ℤ) : conditionalAvoidanceMass S q N ≤ 1 := by
  rw [← conditionalResidueExpectation_indicator, ← conditionalResidueMass_sum hS q]
  unfold conditionalResidueExpectation
  apply Finset.sum_le_sum
  intro a _ha
  exact mul_le_of_le_one_right (conditionalResidueMass_nonneg hS q a)
    (residueAvoidanceIndicator_le_one S N a)

theorem conditionalResidueExpectation_sum {α : Type*} (S : Finset ℕ) (q : ℤ)
    (J : Finset α) (f : α → ResidueAssignment S → ℝ) :
    conditionalResidueExpectation S q (fun a => ∑ j ∈ J, f j a) =
      ∑ j ∈ J, conditionalResidueExpectation S q (f j) := by
  unfold conditionalResidueExpectation
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem conditionalResidueExpectation_const_mul (S : Finset ℕ) (q : ℤ) (b : ℝ)
    (f : ResidueAssignment S → ℝ) :
    conditionalResidueExpectation S q (fun a => b * f a) =
      b * conditionalResidueExpectation S q f := by
  unfold conditionalResidueExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

theorem conditionalResidueExpectation_weighted_sum {α : Type*} (S : Finset ℕ) (q : ℤ)
    (J : Finset α) (b : α → ℝ) (N : α → Finset ℤ) :
    conditionalResidueExpectation S q
        (fun a => ∑ j ∈ J, b j * residueAvoidanceIndicator S (N j) a) =
      ∑ j ∈ J, b j * conditionalAvoidanceMass S q (N j) := by
  rw [conditionalResidueExpectation_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [conditionalResidueExpectation_const_mul, conditionalResidueExpectation_indicator]

theorem conditionalResidueExpectation_weighted_square {α : Type*} (S : Finset ℕ) (q : ℤ)
    (J : Finset α) (b : α → ℝ) (N : α → Finset ℤ) :
    conditionalResidueExpectation S q
        (fun a => (∑ j ∈ J, b j * residueAvoidanceIndicator S (N j) a) ^ 2) =
      ∑ i ∈ J, ∑ j ∈ J, (b i * b j) * conditionalAvoidanceMass S q (N i ∪ N j) := by
  have hid (a : ResidueAssignment S) :
      (∑ j ∈ J, b j * residueAvoidanceIndicator S (N j) a) ^ 2 =
        ∑ i ∈ J, ∑ j ∈ J, (b i * b j) * residueAvoidanceIndicator S (N i ∪ N j) a := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _hj
    rw [← residueAvoidanceIndicator_mul]
    ring
  simp_rw [hid]
  rw [conditionalResidueExpectation_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  exact conditionalResidueExpectation_weighted_sum S q J
    (fun j => b i * b j) (fun j => N i ∪ N j)

theorem conditionalResidue_correlation_absolute_error {S : Finset ℕ} {N : Finset ℤ}
    {q : ℤ} {e : ℝ} (hσ : 0 < residueSieveDensity S) (hq : q ∈ N)
    (hcor : |residueAvoidanceMass S N / residueSieveDensity S ^ N.card - 1| ≤ e) :
    |conditionalAvoidanceMass S q N - residueSieveDensity S ^ (N.card - 1)| ≤
      e * residueSieveDensity S ^ (N.card - 1) := by
  have hcard : 0 < N.card := Finset.card_pos.mpr ⟨q, hq⟩
  have hpow : residueSieveDensity S ^ N.card =
      residueSieveDensity S ^ (N.card - 1) * residueSieveDensity S := by
    rw [← pow_succ]
    congr 1
    omega
  have hc := residue_correlation_absolute_error hσ hcor
  rw [hpow] at hc
  rw [conditionalAvoidanceMass_of_mem S hq]
  have heq : residueAvoidanceMass S N / residueSieveDensity S -
        residueSieveDensity S ^ (N.card - 1) =
      (residueAvoidanceMass S N -
        residueSieveDensity S ^ (N.card - 1) * residueSieveDensity S) /
          residueSieveDensity S := by field_simp
  rw [heq, abs_div, abs_of_pos hσ]
  apply (div_le_iff₀ hσ).mpr
  simpa only [mul_assoc] using hc

end

end Erdos4b.FGKMT
