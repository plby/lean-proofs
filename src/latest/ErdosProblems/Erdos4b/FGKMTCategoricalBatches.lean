/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTLabelRestriction

/-! # Finite categorical assignments and their exact batch-degree expectations -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {I J : Type*} [Fintype I] [Fintype J]

def categoricalMass (p : J → ℝ) : Option J → ℝ
  | none => 1 - ∑ j, p j
  | some j => p j

theorem categoricalMass_nonneg (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hsum : ∑ j, p j ≤ 1) (o : Option J) : 0 ≤ categoricalMass p o := by
  cases o with
  | none => exact sub_nonneg.mpr hsum
  | some j => exact hp j

theorem categoricalMass_sum_one (p : J → ℝ) : ∑ o : Option J, categoricalMass p o = 1 := by
  rw [Fintype.sum_option]
  simp only [categoricalMass]
  ring

theorem categorical_probability_le_one (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hsum : ∑ j, p j ≤ 1) (j : J) : p j ≤ 1 :=
  (Finset.single_le_sum (fun i _ => hp i) (Finset.mem_univ j)).trans hsum

def categoricalAssignmentMass (p : J → ℝ) (a : I → Option J) : ℝ :=
  ∏ i, categoricalMass p (a i)

theorem categoricalAssignmentMass_nonneg (p : J → ℝ) (hp : ∀ j, 0 ≤ p j)
    (hsum : ∑ j, p j ≤ 1) (a : I → Option J) : 0 ≤ categoricalAssignmentMass p a :=
  Finset.prod_nonneg fun i _ => categoricalMass_nonneg p hp hsum (a i)

variable [DecidableEq I]

theorem categoricalAssignmentMass_sum_one (p : J → ℝ) :
    (∑ a : I → Option J, categoricalAssignmentMass p a) = 1 :=
  assignmentWeight_sum (fun _ : I => categoricalMass p) (fun _ => categoricalMass_sum_one p)

variable [DecidableEq J]

theorem categoricalAssignment_coordinate (p : J → ℝ) (i : I) (j : J) :
    (∑ a : I → Option J, if a i = some j then categoricalAssignmentMass p a else 0) =
      p j := by
  have hevent (a : I → Option J) :
      (∀ k, k = i → a k = some j) ↔ a i = some j := by
    constructor
    · intro h
      exact h i rfl
    · intro h k hk
      subst k
      exact h
  have h := independent_assignment_miss_mass (fun _ : I => categoricalMass p)
    (fun k o => k = i → o = some j)
  simp_rw [hevent] at h
  change _ = p j
  rw [show (∑ a : I → Option J,
    if a i = some j then categoricalAssignmentMass p a else 0) = _ from h]
  rw [Finset.prod_eq_single i]
  · simp only [forall_true_left, Finset.sum_ite_eq', Finset.mem_univ, if_true, categoricalMass]
  · intro k _ hki
    simpa only [hki, false_implies, if_true] using categoricalMass_sum_one p
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

theorem categoricalAssignment_indicator_mean (p : J → ℝ) (i : I) (j : J) (c : ℝ) :
    (∑ a : I → Option J,
      categoricalAssignmentMass p a * (if a i = some j then c else 0)) = p j * c := by
  calc
    _ = (∑ a : I → Option J,
        if a i = some j then categoricalAssignmentMass p a else 0) * c := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : a i = some j <;> simp only [ha, if_true, if_false, mul_zero, zero_mul]
    _ = _ := by rw [categoricalAssignment_coordinate]

def categoricalDegree (w : I → ℝ) (a : I → Option J) (j : J) : ℝ :=
  ∑ i, if a i = some j then w i else 0

theorem categoricalDegree_mean (p : J → ℝ) (w : I → ℝ) (j : J) :
    (∑ a : I → Option J, categoricalAssignmentMass p a * categoricalDegree w a j) =
      p j * ∑ i, w i := by
  simp only [categoricalDegree, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [categoricalAssignment_indicator_mean]

omit [Fintype J] [DecidableEq I] in
theorem categoricalDegree_sub_of_agree (w : I → ℝ) (j : J) (i : I)
    (a b : I → Option J) (hab : ∀ k, k ≠ i → a k = b k) :
    categoricalDegree w a j - categoricalDegree w b j =
      (if a i = some j then w i else 0) - (if b i = some j then w i else 0) := by
  classical
  rw [categoricalDegree, categoricalDegree, ← Finset.sum_sub_distrib]
  apply Finset.sum_eq_single i
  · intro k _ hki
    rw [hab k hki, sub_self]
  · simp only [Finset.mem_univ, not_true_eq_false, false_implies]

omit [Fintype J] [DecidableEq I] in
theorem categoricalDegree_bounded_difference (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (j : J) (i : I) (a b : I → Option J) (hab : ∀ k, k ≠ i → a k = b k) :
    |categoricalDegree w a j - categoricalDegree w b j| ≤ w i := by
  rw [categoricalDegree_sub_of_agree w j i a b hab]
  by_cases ha : a i = some j <;> by_cases hb : b i = some j <;>
    simp only [ha, hb, if_true, if_false, sub_self, sub_zero, zero_sub,
      abs_zero, abs_neg, abs_of_nonneg (hw i), le_refl, hw i]

end

end Erdos4b.FGKMT
