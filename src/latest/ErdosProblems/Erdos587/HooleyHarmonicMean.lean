import ErdosProblems.Erdos587.HooleySmoothMean
import ErdosProblems.Erdos896.Ford.Reduction
import ErdosProblems.Erdos896.Ford.SquarefullDivisorTail

/-!
# Unconditional harmonic mean of the Hooley Delta function

The canonical squarefree--squarefull decomposition and the convergent
divisor-weighted squarefull sum remove squarefreeness. Both arithmetic
inputs are already proved in the repository's Ford development.
-/

open scoped BigOperators

namespace Erdos587

lemma delta_harmonic_mul_le (a b : ℕ) :
    (hooleyDelta (a * b) : ℝ) / (a * b : ℕ) ≤
      ((a.divisors.card : ℝ) / a) * ((hooleyDelta b : ℝ) / b) := by
  have hdelta : (hooleyDelta (a * b) : ℝ) ≤ (a.divisors.card : ℝ) * hooleyDelta b := by
    exact_mod_cast hooleyDelta_mul_le a b
  calc
    _ ≤ ((a.divisors.card : ℝ) * hooleyDelta b) / (a * b : ℕ) :=
      div_le_div_of_nonneg_right hdelta (by positivity)
    _ = _ := by
      simp only [Nat.cast_mul, div_eq_mul_inv, mul_inv_rev]
      ring

theorem delta_harmonic_squarefull_reduction (X : ℕ) :
    (∑ n ∈ Finset.Ico 1 X, (hooleyDelta n : ℝ) / n) ≤
      (∑ a ∈ Erdos896.Ford.squarefullSet X, (a.divisors.card : ℝ) / a) *
        ∑ b ∈ deltaSmoothNumbers X, (hooleyDelta b : ℝ) / b := by
  classical
  let S := (Erdos896.Ford.squarefullSet X) ×ˢ deltaSmoothNumbers X
  let prod := fun z : ℕ × ℕ => z.1 * z.2
  have hcover : Finset.Ico 1 X ⊆ S.image prod := by
    intro n hn
    obtain ⟨hn1, hnX⟩ := Finset.mem_Ico.mp hn
    have hn0 : n ≠ 0 := by omega
    let a := Erdos896.Ford.squarefullComponent n
    let b := Erdos896.Ford.squarefreeComponent n
    have hab : a * b = n := by
      rw [mul_comm]
      exact Erdos896.Ford.squarefreeComponent_mul_squarefullComponent hn0
    have ha : 0 < a := Erdos896.Ford.pos_squarefullComponent n
    have hb : 0 < b := Erdos896.Ford.pos_squarefreeComponent n
    have hadvd : a ∣ n := hab ▸ dvd_mul_right a b
    have hbdvd : b ∣ n := hab ▸ dvd_mul_left b a
    have haX : a ≤ X := (Nat.le_of_dvd hn1 hadvd).trans hnX.le
    have hbX : b < X := (Nat.le_of_dvd hn1 hbdvd).trans_lt hnX
    have haS : a ∈ Erdos896.Ford.squarefullSet X :=
      Erdos896.Ford.mem_squarefullSet.mpr
        ⟨ha, haX, Erdos896.Ford.squarefull_squarefullComponent n⟩
    have hbS : b ∈ deltaSmoothNumbers X := by
      apply mem_deltaSmoothNumbers_iff.mpr
      refine ⟨Erdos896.Ford.squarefree_squarefreeComponent n, ?_⟩
      intro p hp
      exact (Nat.le_of_dvd hb (Nat.dvd_of_mem_primeFactors hp)).trans_lt hbX
    exact Finset.mem_image.mpr ⟨(a, b), Finset.mem_product.mpr ⟨haS, hbS⟩, hab⟩
  calc
    _ ≤ ∑ n ∈ S.image prod, (hooleyDelta n : ℝ) / n :=
      Finset.sum_le_sum_of_subset_of_nonneg hcover (fun n _ _ => by positivity)
    _ ≤ ∑ z ∈ S, (hooleyDelta (prod z) : ℝ) / prod z :=
      Finset.sum_image_le_of_nonneg (fun n _ => by positivity)
    _ ≤ ∑ z ∈ S, ((z.1.divisors.card : ℝ) / z.1) * ((hooleyDelta z.2 : ℝ) / z.2) :=
      Finset.sum_le_sum (fun z _ => delta_harmonic_mul_le z.1 z.2)
    _ = _ := by
      dsimp only [S]
      rw [Finset.sum_product, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum]

/-- The unconditional harmonic mean estimate needed by the short-
progression transfer. The upper endpoint is initially half-open. -/
theorem exists_hooleyDelta_harmonic_loglog_bound_Ico :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X →
      (∑ n ∈ Finset.Ico 1 X, (hooleyDelta n : ℝ) / n) ≤
        C * Real.log (X : ℝ) * (max 1 (Real.log (Real.log (X : ℝ)))) ^ 5 := by
  obtain ⟨C₁, hC₁, hmean⟩ := exists_deltaSmooth_harmonic_loglog_bound
  obtain ⟨C₂, hC₂, hfull⟩ := Erdos896.Ford.exists_uniform_squarefull_divisor_sum
  refine ⟨C₂ * C₁, mul_pos hC₂ hC₁, ?_⟩
  intro X hX
  have hfull' : (∑ a ∈ Erdos896.Ford.squarefullSet X, (a.divisors.card : ℝ) / a) ≤ C₂ := by
    simpa only [div_eq_mul_inv] using hfull X
  have hnonneg : 0 ≤ ∑ b ∈ deltaSmoothNumbers X, (hooleyDelta b : ℝ) / b :=
    Finset.sum_nonneg (fun b _ => by positivity)
  calc
    _ ≤ (∑ a ∈ Erdos896.Ford.squarefullSet X, (a.divisors.card : ℝ) / a) *
        ∑ b ∈ deltaSmoothNumbers X, (hooleyDelta b : ℝ) / b :=
      delta_harmonic_squarefull_reduction X
    _ ≤ C₂ * ∑ b ∈ deltaSmoothNumbers X, (hooleyDelta b : ℝ) / b :=
      mul_le_mul_of_nonneg_right hfull' hnonneg
    _ ≤ C₂ * (C₁ * Real.log (X : ℝ) * (max 1 (Real.log (Real.log (X : ℝ)))) ^ 5) :=
      mul_le_mul_of_nonneg_left (hmean X hX) hC₂.le
    _ = _ := by ring

lemma delta_log_succ_le {X : ℕ} (hX : 2 ≤ X) :
    Real.log ((X + 1 : ℕ) : ℝ) ≤ 2 * Real.log (X : ℝ) := by
  have hnat : X + 1 ≤ X ^ 2 := by nlinarith
  have h := Real.log_le_log (by positivity : (0 : ℝ) < ((X + 1 : ℕ) : ℝ))
    (show ((X + 1 : ℕ) : ℝ) ≤ (X : ℝ) ^ 2 by exact_mod_cast hnat)
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

lemma delta_loglog_succ_le {X : ℕ} (hX : 2 ≤ X) :
    max 1 (Real.log (Real.log ((X + 1 : ℕ) : ℝ))) ≤
      2 * max 1 (Real.log (Real.log (X : ℝ))) := by
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogXp : 0 < Real.log ((X + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X + 1 by omega))
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h
    exact h
  have h := Real.log_le_log hlogXp (delta_log_succ_le hX)
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hlogX.ne'] at h
  have hU : 1 ≤ max 1 (Real.log (Real.log (X : ℝ))) := le_max_left _ _
  have hlogU : Real.log (Real.log (X : ℝ)) ≤ max 1 (Real.log (Real.log (X : ℝ))) :=
    le_max_right _ _
  apply max_le <;> linarith

/-- Closed-endpoint form of the unconditional harmonic Delta estimate. -/
theorem exists_hooleyDelta_harmonic_loglog_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 2 ≤ X →
      (∑ n ∈ Finset.Icc 1 X, (hooleyDelta n : ℝ) / n) ≤
        C * Real.log (X : ℝ) * (max 1 (Real.log (Real.log (X : ℝ)))) ^ 5 := by
  obtain ⟨C, hC, hmean⟩ := exists_hooleyDelta_harmonic_loglog_bound_Ico
  refine ⟨64 * C, mul_pos (by norm_num) hC, ?_⟩
  intro X hX
  have hU : 1 ≤ max 1 (Real.log (Real.log (X : ℝ))) := le_max_left _ _
  have hUp : 1 ≤ max 1 (Real.log (Real.log ((X + 1 : ℕ) : ℝ))) := le_max_left _ _
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by omega))
  have hlogXp : 0 < Real.log ((X + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X + 1 by omega))
  calc
    _ = ∑ n ∈ Finset.Ico 1 (X + 1), (hooleyDelta n : ℝ) / n := by
      rw [Finset.Ico_add_one_right_eq_Icc]
    _ ≤ C * Real.log ((X + 1 : ℕ) : ℝ) *
        (max 1 (Real.log (Real.log ((X + 1 : ℕ) : ℝ)))) ^ 5 := hmean (X + 1) (by omega)
    _ ≤ C * (2 * Real.log (X : ℝ)) *
        (2 * max 1 (Real.log (Real.log (X : ℝ)))) ^ 5 := by
      gcongr
      · exact delta_log_succ_le hX
      · exact delta_loglog_succ_le hX
    _ = _ := by ring

end Erdos587
