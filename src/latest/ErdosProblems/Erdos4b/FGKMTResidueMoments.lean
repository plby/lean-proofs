/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTUniformResidueCorrelation

/-! # Exact finite moments of random-residue survival indicators -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def residueExpectation (S : Finset ℕ) (f : ResidueAssignment S → ℝ) : ℝ :=
  ∑ a : ResidueAssignment S, residueAssignmentMass S a * f a

open scoped Classical in
def residueAvoidanceIndicator (S : Finset ℕ) (N : Finset ℤ) (a : ResidueAssignment S) : ℝ :=
  if residueAssignmentAvoids S N a then 1 else 0

theorem residueAssignmentAvoids_union (S : Finset ℕ) (N M : Finset ℤ)
    (a : ResidueAssignment S) :
    residueAssignmentAvoids S (N ∪ M) a ↔ residueAssignmentAvoids S N a ∧
      residueAssignmentAvoids S M a := by
  simp only [residueAssignmentAvoids, occupiedResidues, Finset.image_union,
    Finset.mem_union, not_or, forall_and]

theorem residueAvoidanceIndicator_mul (S : Finset ℕ) (N M : Finset ℤ)
    (a : ResidueAssignment S) :
    residueAvoidanceIndicator S N a * residueAvoidanceIndicator S M a =
      residueAvoidanceIndicator S (N ∪ M) a := by
  classical
  unfold residueAvoidanceIndicator
  rw [residueAssignmentAvoids_union]
  by_cases hn : residueAssignmentAvoids S N a <;>
    by_cases hm : residueAssignmentAvoids S M a <;> simp [hn, hm]

theorem residueExpectation_indicator (S : Finset ℕ) (N : Finset ℤ) :
    residueExpectation S (residueAvoidanceIndicator S N) = residueAvoidanceMass S N := by
  classical
  unfold residueExpectation residueAvoidanceIndicator residueAvoidanceMass
  apply Finset.sum_congr rfl
  intro a _ha
  split_ifs <;> simp

theorem residueExpectation_sum {α : Type*} (S : Finset ℕ) (J : Finset α)
    (f : α → ResidueAssignment S → ℝ) :
    residueExpectation S (fun a => ∑ j ∈ J, f j a) = ∑ j ∈ J, residueExpectation S (f j) := by
  unfold residueExpectation
  simp only [Finset.mul_sum]
  exact Finset.sum_comm

theorem residueExpectation_const_mul (S : Finset ℕ) (b : ℝ) (f : ResidueAssignment S → ℝ) :
    residueExpectation S (fun a => b * f a) = b * residueExpectation S f := by
  unfold residueExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  ring

theorem residueExpectation_weighted_indicator_sum {α : Type*} (S : Finset ℕ) (J : Finset α)
    (b : α → ℝ) (N : α → Finset ℤ) :
    residueExpectation S (fun a => ∑ j ∈ J, b j * residueAvoidanceIndicator S (N j) a) =
      ∑ j ∈ J, b j * residueAvoidanceMass S (N j) := by
  rw [residueExpectation_sum]
  apply Finset.sum_congr rfl
  intro j _hj
  rw [residueExpectation_const_mul, residueExpectation_indicator]

theorem residueExpectation_weighted_indicator_square {α : Type*} (S : Finset ℕ) (J : Finset α)
    (b : α → ℝ) (N : α → Finset ℤ) :
    residueExpectation S (fun a => (∑ j ∈ J, b j * residueAvoidanceIndicator S (N j) a) ^ 2) =
      ∑ i ∈ J, ∑ j ∈ J, (b i * b j) * residueAvoidanceMass S (N i ∪ N j) := by
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
  rw [residueExpectation_sum]
  apply Finset.sum_congr rfl
  intro i _hi
  exact residueExpectation_weighted_indicator_sum S J (fun j => b i * b j) (fun j => N i ∪ N j)

theorem residueAvoidanceMass_singleton {S : Finset ℕ} (hS : ∀ p ∈ S, 0 < p) (n : ℤ) :
    residueAvoidanceMass S {n} = residueSieveDensity S := by
  rw [residueAvoidanceMass_eq_prod hS]
  simp only [occupiedResidues, Finset.image_singleton, Finset.card_singleton, Nat.cast_one]
  rfl

open scoped Classical in
def residueSurvivorSet (S : Finset ℕ) (T : Finset ℤ) (a : ResidueAssignment S) : Finset ℤ :=
  T.filter fun n => residueAssignmentAvoids S {n} a

theorem residueSurvivorSet_card_eq_sum (S : Finset ℕ) (T : Finset ℤ) (a : ResidueAssignment S) :
    ((residueSurvivorSet S T a).card : ℝ) = ∑ n ∈ T, residueAvoidanceIndicator S {n} a := by
  classical
  simp only [residueSurvivorSet, residueAvoidanceIndicator, Finset.card_filter,
    Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem residueExpectation_survivor_count {S : Finset ℕ} (hS : ∀ p ∈ S, 0 < p) (T : Finset ℤ) :
    residueExpectation S (fun a => ((residueSurvivorSet S T a).card : ℝ)) =
      (T.card : ℝ) * residueSieveDensity S := by
  simp_rw [residueSurvivorSet_card_eq_sum]
  rw [residueExpectation_sum]
  simp only [residueExpectation_indicator, residueAvoidanceMass_singleton hS,
    Finset.sum_const, nsmul_eq_mul]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.residueExpectation_weighted_indicator_square
#print axioms Erdos4b.FGKMT.residueExpectation_survivor_count
