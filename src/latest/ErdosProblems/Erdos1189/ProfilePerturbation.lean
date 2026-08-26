/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The bounded entropy cost of the exceptional coordinates in a frame profile.
Informal source: BBMST Lemma 7.1.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.ProfileEntropy

namespace Erdos1189

open Finset

lemma log_nat_add_le (r s : ℕ) :
    Real.log ((r + s : ℕ) + 1 : ℝ) ≤ Real.log ((r : ℝ) + 1) + Real.log ((s : ℝ) + 1) := by
  rw [← Real.log_mul (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  push_cast
  have h := mul_nonneg (Nat.cast_nonneg r (α := ℝ)) (Nat.cast_nonneg s (α := ℝ))
  nlinarith

lemma profileEntropy_add_le (P : Finset ℕ) (γ θ : ℕ → ℕ) :
    profileEntropy P (fun p => γ p + θ p) ≤ profileEntropy P γ + profileEntropy P θ := by
  unfold profileEntropy
  rw [← sum_add_distrib]
  exact sum_le_sum fun p _ => log_nat_add_le (γ p) (θ p)

lemma profileEntropy_single (P : Finset ℕ) {p : ℕ} (hp : p ∈ P) :
    profileEntropy P (fun q => if p = q then 1 else 0) = Real.log 2 := by
  unfold profileEntropy
  rw [sum_eq_single p]
  · norm_num
  · intro q _ hqp
    simp [Ne.symm hqp]
  · exact fun h => False.elim (h hp)

lemma profileEntropy_small_increment (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (T : ℕ) :
    profileEntropy P (fun p => if p ≤ T then T else 0) ≤ T * Real.log ((T : ℝ) + 1) := by
  have hcard : (P.filter (fun p => p ≤ T)).card ≤ T := by
    have hsub : P.filter (fun p => p ≤ T) ⊆ Ioc 0 T := by
      intro p hp
      obtain ⟨hpP, hpT⟩ := mem_filter.mp hp
      exact mem_Ioc.mpr ⟨(hP p hpP).pos, hpT⟩
    simpa only [Nat.card_Ioc, Nat.sub_zero] using card_le_card hsub
  have heq : profileEntropy P (fun p => if p ≤ T then T else 0) =
      (P.filter (fun p => p ≤ T)).card * Real.log ((T : ℝ) + 1) := by
    unfold profileEntropy
    have hterms : ∀ p : ℕ, Real.log (((if p ≤ T then T else 0) : ℕ) + 1 : ℝ) =
        if p ≤ T then Real.log ((T : ℝ) + 1) else 0 := by
      intro p
      by_cases hp : p ≤ T <;> simp [hp]
    simp_rw [hterms]
    rw [← sum_filter]
    simp
  rw [heq]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard)
    (Real.log_nonneg (by have := Nat.cast_nonneg T (α := ℝ); linarith))

lemma profileEntropy_frame_increment (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime)
    (γ : ℕ → ℕ) {p : ℕ} (hp : p ∈ P) (T : ℕ) :
    profileEntropy P (fun q => γ q + (if p = q then 1 else 0) +
      if q ≤ T then T else 0) ≤ profileEntropy P γ + Real.log 2 +
        T * Real.log ((T : ℝ) + 1) := by
  have h₁ := profileEntropy_add_le P (fun q => γ q + if p = q then 1 else 0)
    (fun q => if q ≤ T then T else 0)
  have h₂ := profileEntropy_add_le P γ (fun q => if p = q then 1 else 0)
  rw [profileEntropy_single P hp] at h₂
  have h₃ := profileEntropy_small_increment P hP T
  linarith

end Erdos1189
