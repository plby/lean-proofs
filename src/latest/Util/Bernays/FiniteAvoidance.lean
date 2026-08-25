import Util.Bernays.FiniteVariance

/-!
# Exact finite inclusion-exclusion for avoided events
-/

open scoped Classical

namespace Bernays

theorem indicator_all_eq_prod {ι : Type*} (P : Finset ι) (E : ι → Prop) :
    (if ∀ p ∈ P, E p then (1 : ℝ) else 0) = ∏ p ∈ P, if E p then 1 else 0 := by
  classical
  by_cases h : ∀ p ∈ P, E p
  · rw [if_pos h]
    symm
    exact Finset.prod_eq_one (fun p hp => if_pos (h p hp))
  · rw [if_neg h]
    push_neg at h
    obtain ⟨p, hp, hE⟩ := h
    symm
    exact Finset.prod_eq_zero hp (if_neg hE)

theorem indicator_all_not_eq_prod {ι : Type*} (P : Finset ι) (E : ι → Prop) :
    (if ∀ p ∈ P, ¬E p then (1 : ℝ) else 0) = ∏ p ∈ P, (1 - if E p then 1 else 0) := by
  calc
    _ = ∏ p ∈ P, if ¬E p then (1 : ℝ) else 0 := by
      convert indicator_all_eq_prod P (fun p => ¬E p) using 1 <;> congr
      funext p
      split_ifs <;> rfl
    _ = _ := by
      apply Finset.prod_congr rfl
      intro p hp
      by_cases h : E p <;> simp only [h, not_true_eq_false, not_false_eq_true, if_true, if_false] <;> ring

theorem eventCount_avoid_eq_sum_powerset {α ι : Type*} [DecidableEq ι]
    (A : Finset α) (P : Finset ι) (E : ι → α → Prop) :
    (eventCount A (fun x => ∀ p ∈ P, ¬E p x) : ℝ) =
      ∑ T ∈ P.powerset, (-1 : ℝ) ^ T.card * eventCount A (fun x => ∀ p ∈ T, E p x) := by
  rw [← sum_event_indicator A (fun x => ∀ p ∈ P, ¬E p x)]
  simp_rw [indicator_all_not_eq_prod, Finset.prod_sub]
  simp only [Finset.prod_const_one, mul_one]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro T hT
  rw [← Finset.mul_sum]
  congr 1
  simp_rw [← indicator_all_eq_prod]
  exact sum_event_indicator A (fun x => ∀ p ∈ T, E p x)

end Bernays
