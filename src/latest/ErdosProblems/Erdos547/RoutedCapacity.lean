import ErdosProblems.Erdos547.RoutedLoads

/-!
# Selecting a target and preserving all routed capacities
-/

namespace Erdos547

open Finset
open scoped BigOperators

variable {F A I : Type*} [Fintype F] [Fintype I]
  [DecidableEq F] [DecidableEq A] [DecidableEq I]

theorem exists_routed_target (E : Finset F) (group : F → A) (route : F → I)
    (w : F → ℕ) (a : A) (capacity : I → ℝ) (s L : ℝ)
    (hs : 0 < s) (hsone : s ≤ 1) (hL : 0 ≤ L)
    (hpositive : 0 < ∑ i, capacity i)
    (hdemand : (∑ x, if group x = a then (w x : ℝ) else 0) ≤ (1 - s) * ∑ i, capacity i)
    (hsmall : L * Fintype.card I ≤ s / 4 * ∑ i, capacity i) :
    ∃ i, L ≤ capacity i ∧
      (routedLoad E group route w a i : ℝ) < (1 - s / 2) * capacity i := by
  have hh := routedLoad_le_group_demand E group route w a
  have hcast : (∑ i, (routedLoad E group route w a i : ℝ)) ≤
      ∑ x, if group x = a then (w x : ℝ) else 0 := by
    exact_mod_cast hh
  exact exists_target_capacity capacity (fun i ↦ (routedLoad E group route w a i : ℝ))
    (fun i ↦ Nat.cast_nonneg _) s L hs hsone hL hpositive (hcast.trans hdemand) hsmall

theorem routed_capacity_preserved (E : Finset F) (group : F → A) (route : F → I)
    (w : F → ℕ) (capacity : A → I → ℝ) (x : F) (hx : x ∉ E) (j : I) (s : ℝ)
    (hcap : ∀ a i, (routedLoad E group route w a i : ℝ) ≤ capacity a i)
    (hpositive : 0 < capacity (group x) j) (hs : 0 < s)
    (htarget : (routedLoad E group route w (group x) j : ℝ) <
      (1 - s / 2) * capacity (group x) j)
    (hsmall : (w x : ℝ) ≤ s / 4 * capacity (group x) j) :
    ∀ a i, (routedLoad (insert x E) group (Function.update route x j) w a i : ℝ) ≤
      capacity a i := by
  intro a i
  rw [routedLoad_insert E group route w x hx j a i, Nat.cast_add]
  by_cases h : group x = a ∧ j = i
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos ⟨rfl, rfl⟩]
    exact (target_capacity_after_extension _ _ _ _ hpositive hs htarget hsmall).le
  · rw [if_neg h, Nat.cast_zero, add_zero]
    exact hcap a i

theorem routedLoad_le_after_insert (E : Finset F) (group : F → A) (route : F → I)
    (w : F → ℕ) (x : F) (hx : x ∉ E) (j : I) (a : A) (i : I) :
    routedLoad E group route w a i ≤
      routedLoad (insert x E) group (Function.update route x j) w a i := by
  rw [routedLoad_insert E group route w x hx j a i]
  exact Nat.le_add_right _ _

end Erdos547

#print axioms Erdos547.exists_routed_target
#print axioms Erdos547.routed_capacity_preserved
