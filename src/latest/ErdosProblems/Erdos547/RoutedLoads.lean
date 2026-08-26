import ErdosProblems.Erdos547.TargetCapacity

/-!
# Exact bookkeeping for objects assigned to groups and target bins
-/

namespace Erdos547

open Finset
open scoped BigOperators

variable {F A I : Type*} [DecidableEq F] [DecidableEq A] [DecidableEq I]

def routedLoad (E : Finset F) (group : F → A) (route : F → I) (w : F → ℕ)
    (a : A) (i : I) : ℕ :=
  ∑ x ∈ E, if group x = a ∧ route x = i then w x else 0

theorem routedLoad_sum_targets [Fintype I] (E : Finset F)
    (group : F → A) (route : F → I) (w : F → ℕ) (a : A) :
    (∑ i, routedLoad E group route w a i) = ∑ x ∈ E, if group x = a then w x else 0 := by
  unfold routedLoad
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : group x = a
  · simp only [h, true_and, if_true]
    simp
  · simp only [h, false_and, if_false, Finset.sum_const_zero]

theorem routedLoad_sum_groups [Fintype A] (E : Finset F)
    (group : F → A) (route : F → I) (w : F → ℕ) (i : I) :
    (∑ a, routedLoad E group route w a i) = ∑ x ∈ E, if route x = i then w x else 0 := by
  unfold routedLoad
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h : route x = i
  · simp only [h, and_true, if_true]
    simp
  · simp only [h, and_false, if_false, Finset.sum_const_zero]

theorem routedLoad_insert (E : Finset F) (group : F → A) (route : F → I)
    (w : F → ℕ) (x : F) (hx : x ∉ E) (j : I) (a : A) (i : I) :
    routedLoad (insert x E) group (Function.update route x j) w a i =
      routedLoad E group route w a i + (if group x = a ∧ j = i then w x else 0) := by
  rw [routedLoad, Finset.sum_insert hx]
  rw [Function.update_self]
  have he : (∑ y ∈ E, if group y = a ∧ Function.update route x j y = i then w y else 0) =
      routedLoad E group route w a i := by
    apply Finset.sum_congr rfl
    intro y hy
    have hyx : y ≠ x := fun he ↦ hx (he ▸ hy)
    rw [Function.update_of_ne hyx]
  rw [he, Nat.add_comm]

theorem routedLoad_le_group_demand [Fintype F] [Fintype I]
    (E : Finset F) (group : F → A) (route : F → I) (w : F → ℕ) (a : A) :
    (∑ i, routedLoad E group route w a i) ≤ ∑ x, if group x = a then w x else 0 := by
  rw [routedLoad_sum_targets]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    (fun _ _ _ ↦ Nat.zero_le _)

theorem routedLoad_mono (E F' : Finset F) (hEF : E ⊆ F')
    (group : F → A) (route : F → I) (w : F → ℕ) (a : A) (i : I) :
    routedLoad E group route w a i ≤ routedLoad F' group route w a i :=
  Finset.sum_le_sum_of_subset_of_nonneg hEF (fun _ _ _ ↦ Nat.zero_le _)

end Erdos547
