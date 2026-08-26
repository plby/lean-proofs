import ErdosProblems.Erdos67b.MRLemma14ContinuousMixed

/-!
# Weighted vertical tails from finite mean values

Finite doubling and an explicit telescoping potential suffice. There is
no exchange of an infinite sum and an improper integral.
-/

open Finset MeasureTheory Set

namespace Erdos67b

noncomputable section

/-- The actual two-sided safe-weighted tail, truncated at `U`. -/
def lemma14TwoSidedWeightedTail (F : ℝ → ℂ) (T U : ℝ) : ℝ :=
  (∫ t in -U..-T, lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) +
    ∫ t in T..U, lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)

theorem lemma14TwoSidedWeightedTail_double
    (F : ℝ → ℂ) (hF : Continuous F) {T : ℝ} (hT : 0 < T) (V : ℝ) :
    lemma14TwoSidedWeightedTail F T (2 * V) =
      lemma14TwoSidedWeightedTail F T V +
      (∫ t in -2 * V..-V, lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) +
      ∫ t in V..2 * V, lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t) := by
  let e : ℝ → ℝ := fun t ↦ lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)
  have he : Continuous e :=
    (continuous_lemma14SafeReciprocalSqWeight hT).mul (Complex.continuous_normSq.comp hF)
  have hneg := intervalIntegral.integral_add_adjacent_intervals
    (he.intervalIntegrable (μ := volume) (-2 * V) (-V))
    (he.intervalIntegrable (μ := volume) (-V) (-T))
  have hpos := intervalIntegral.integral_add_adjacent_intervals
    (he.intervalIntegrable (μ := volume) T V)
    (he.intervalIntegrable (μ := volume) V (2 * V))
  unfold lemma14TwoSidedWeightedTail
  rw [show -(2 * V) = -2 * V by ring, ← hneg, ← hpos]
  ring

/-- A shell estimate retaining both the slope and intercept of the mean bound. -/
theorem lemma14TwoSidedWeightedTail_shell_le
    (F : ℝ → ℂ) (hF : Continuous F) {a b T V : ℝ}
    (hT : 0 < T) (hTV : T ≤ V)
    (hmean : ∀ W : ℝ, 0 ≤ W → (∫ t in -W..W, Complex.normSq (F t)) ≤ a * W + b) :
    (∫ t in -2 * V..-V, lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) +
      (∫ t in V..2 * V, lemma14SafeReciprocalSqWeight T t * Complex.normSq (F t)) ≤
        4 * a / V + 2 * b / V ^ 2 := by
  have hV : 0 < V := hT.trans_le hTV
  have he := Complex.continuous_normSq.comp hF
  have hneg : (∫ t in -2 * V..-V, Complex.normSq (F t)) ≤ a * (2 * V) + b := by
    refine (intervalIntegral.integral_mono_interval ?_ ?_ ?_
      (Filter.Eventually.of_forall fun t ↦ Complex.normSq_nonneg (F t))
      (he.intervalIntegrable (-(2 * V)) (2 * V))).trans (hmean (2 * V) (by positivity))
    all_goals linarith
  have hpos : (∫ t in V..2 * V, Complex.normSq (F t)) ≤ a * (2 * V) + b := by
    refine (intervalIntegral.integral_mono_interval ?_ ?_ (le_refl _)
      (Filter.Eventually.of_forall fun t ↦ Complex.normSq_nonneg (F t))
      (he.intervalIntegrable (-(2 * V)) (2 * V))).trans (hmean (2 * V) (by positivity))
    all_goals linarith
  have hsneg := intervalIntegral_safeReciprocalSqWeight_mul_normSq_negShell_le F hF hT hV hTV
  have hspos := intervalIntegral_safeReciprocalSqWeight_mul_normSq_posShell_le F hF hT hV hTV
  calc
    _ ≤ V⁻¹ ^ 2 * ((a * (2 * V) + b) + (a * (2 * V) + b)) := by
      have hn := mul_le_mul_of_nonneg_left hneg (sq_nonneg V⁻¹)
      have hp := mul_le_mul_of_nonneg_left hpos (sq_nonneg V⁻¹)
      nlinarith
    _ = _ := by field_simp; ring

/-- The finite doubling telescope; its remaining potential is kept explicit. -/
theorem lemma14TwoSidedWeightedTail_dyadic_le
    (F : ℝ → ℂ) (hF : Continuous F) {a b T : ℝ}
    (hb : 0 ≤ b) (hT : 0 < T)
    (hmean : ∀ W : ℝ, 0 ≤ W → (∫ t in -W..W, Complex.normSq (F t)) ≤ a * W + b)
    (k : ℕ) :
    lemma14TwoSidedWeightedTail F T (2 ^ k * T) ≤
      (8 * a / T + 4 * b / T ^ 2) -
        (8 * a / (2 ^ k * T) + 4 * b / (2 ^ k * T) ^ 2) := by
  induction k with
  | zero => simp [lemma14TwoSidedWeightedTail]
  | succ k ih =>
    let V : ℝ := 2 ^ k * T
    have hV : 0 < V := by dsimp only [V]; positivity
    have hTV : T ≤ V := by
      dsimp only [V]
      exact le_mul_of_one_le_left hT.le (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2))
    have hstep := lemma14TwoSidedWeightedTail_shell_le F hF hT hTV hmean
    have hscale : (2 : ℝ) ^ (k + 1) * T = 2 * V := by dsimp only [V]; rw [pow_succ]; ring
    have hbudget : 4 * a / V + 2 * b / V ^ 2 ≤
        (8 * a / V + 4 * b / V ^ 2) -
          (8 * a / (2 * V) + 4 * b / (2 * V) ^ 2) := by
      have heq : (8 * a / V + 4 * b / V ^ 2) -
          (8 * a / (2 * V) + 4 * b / (2 * V) ^ 2) =
            4 * a / V + 3 * b / V ^ 2 := by field_simp; ring
      rw [heq]
      exact add_le_add (le_refl _)
        (div_le_div_of_nonneg_right (by nlinarith) (sq_nonneg V))
    rw [hscale, lemma14TwoSidedWeightedTail_double F hF hT V]
    change lemma14TwoSidedWeightedTail F T V ≤ _ at ih
    linarith

/-- Uniform control of every finite far tail by a linear prefix mean. -/
theorem lemma14TwoSidedWeightedTail_le_of_mean
    (F : ℝ → ℂ) (hF : Continuous F) {a b T U : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hT : 0 < T) (hTU : T ≤ U)
    (hmean : ∀ W : ℝ, 0 ≤ W → (∫ t in -W..W, Complex.normSq (F t)) ≤ a * W + b) :
    lemma14TwoSidedWeightedTail F T U ≤ 8 * a / T + 4 * b / T ^ 2 := by
  have hratio : 1 ≤ U / T := (one_le_div hT).2 hTU
  obtain ⟨k, _, hk⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
  have hU : U ≤ 2 ^ (k + 1) * T := ((div_lt_iff₀ hT).1 hk).le
  have hmono := safeReciprocalSqWeight_twoSided_mono_outer F hF hT hTU hU
  have hdyadic := lemma14TwoSidedWeightedTail_dyadic_le F hF hb hT hmean (k + 1)
  have hrest : 0 ≤ 8 * a / (2 ^ (k + 1) * T) + 4 * b / (2 ^ (k + 1) * T) ^ 2 := by
    positivity
  change lemma14TwoSidedWeightedTail F T U ≤ lemma14TwoSidedWeightedTail F T _ at hmono
  exact hmono.trans (hdyadic.trans (sub_le_self _ hrest))

end

end Erdos67b
