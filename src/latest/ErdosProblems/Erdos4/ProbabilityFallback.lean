import ErdosProblems.Erdos4.CoveringError

/-!
# Total probability choices when a surviving tuple mass vanishes

A zero mass uses a fixed fallback choice. Positive masses use ordinary
normalization. Every event receives at least its unnormalized mass
divided by the total mass, with division by zero interpreted as zero.
-/

open scoped BigOperators

namespace Erdos4.ProbabilityFallback

variable {A : Type*} [Fintype A] [DecidableEq A]

noncomputable def probability (w : A → ℝ) (a₀ a : A) : ℝ :=
  if (∑ b, w b) = 0 then (if a = a₀ then 1 else 0) else w a / ∑ b, w b

theorem probability_nonneg (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (a₀ a : A) :
    0 ≤ probability w a₀ a := by
  unfold probability
  split_ifs
  · exact zero_le_one
  · exact le_rfl
  · exact div_nonneg (hw a) (Finset.sum_nonneg (fun b _hb => hw b))

theorem sum_probability (w : A → ℝ) (a₀ : A) : (∑ a, probability w a₀ a) = 1 := by
  unfold probability
  by_cases hZ : (∑ b, w b) = 0
  · simp only [if_pos hZ]
    simp
  · simp only [if_neg hZ]
    rw [← Finset.sum_div, div_self hZ]

theorem event_mass_ge (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (a₀ : A)
    (E : A → Prop) [DecidablePred E] :
    (∑ a, if E a then w a else 0) / (∑ b, w b) ≤
      ∑ a, if E a then probability w a₀ a else 0 := by
  by_cases hZ : (∑ b, w b) = 0
  · rw [hZ, div_zero]
    apply Finset.sum_nonneg
    intro a _ha
    split_ifs
    · exact probability_nonneg w hw a₀ a
    · exact le_rfl
  · unfold probability
    simp only [if_neg hZ]
    rw [Finset.sum_div]
    apply le_of_eq
    apply Finset.sum_congr rfl
    intro a _ha
    by_cases ha : E a <;> simp [ha]

theorem event_mass_le_one (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (a₀ : A)
    (E : A → Prop) [DecidablePred E] :
    (∑ a, if E a then probability w a₀ a else 0) ≤ 1 := by
  rw [← sum_probability w a₀]
  apply Finset.sum_le_sum
  intro a _ha
  split_ifs
  · exact le_rfl
  · exact probability_nonneg w hw a₀ a

theorem miss_mass_le (w : A → ℝ) (hw : ∀ a, 0 ≤ w a) (a₀ : A)
    (E : A → Prop) [DecidablePred E] :
    (∑ a, if ¬E a then probability w a₀ a else 0) ≤
      1 - (∑ a, if E a then w a else 0) / (∑ b, w b) := by
  have hsplit : (∑ a, if ¬E a then probability w a₀ a else 0) +
      (∑ a, if E a then probability w a₀ a else 0) = 1 := by
    rw [← Finset.sum_add_distrib, ← sum_probability w a₀]
    apply Finset.sum_congr rfl
    intro a _ha
    by_cases ha : E a <;> simp [ha]
  have hh := event_mass_ge w hw a₀ E
  linarith

end Erdos4.ProbabilityFallback
