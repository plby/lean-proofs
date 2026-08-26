import ErdosProblems.Erdos67b.MRPrimeLogFirstDerivative

/-! # The overlap between first derivatives and fixed-depth Weyl estimates -/

open scoped BigOperators
open Filter

namespace Erdos67b

noncomputable section

open Erdos1149 LogPhaseHigherDerivative LogSecondDerivativeReal
open LogWeylParameters LogBandCoverage ResidueLogPhase

theorem mrNorm_positiveLogBlock_le_transition_sqrt
    {a U : ℝ} {L H : ℕ} (hH : 0 < H) (hHL : H ≤ L)
    (ha : 0 < a) (hU : 0 < U) (hL : (L : ℝ) ≤ U)
    (hUa : U ≤ 2 * a) (hscale : 8 * (H : ℝ) * a ≤ U ^ 2) :
    ‖∑ j ∈ Finset.range L, realBlockPhase a U j‖ ≤
      U * Real.sqrt (76 * (1 + Real.log (H : ℝ)) / H) := by
  have hHR : (0 : ℝ) < H := by exact_mod_cast hH
  have hlog : 0 ≤ Real.log (H : ℝ) := Real.log_nonneg (by exact_mod_cast hH)
  have hratio : U ^ 2 / a ≤ 2 * U := by
    apply (div_le_iff₀ ha).2
    nlinarith
  have hLH : ((L + H : ℕ) : ℝ) ≤ 2 * U := by
    have hh : (H : ℝ) ≤ L := by exact_mod_cast hHL
    push_cast
    linarith
  have hins : (H : ℝ) * L +
      18 * H * (U ^ 2 / a) * (1 + Real.log (H : ℝ)) ≤
      38 * H * U * (1 + Real.log (H : ℝ)) := by
    have hfirst : (H : ℝ) * L ≤ H * U :=
      mul_le_mul_of_nonneg_left hL hHR.le
    have hsecond : 18 * (H : ℝ) * (U ^ 2 / a) * (1 + Real.log (H : ℝ)) ≤
        36 * H * U * (1 + Real.log (H : ℝ)) := by
      calc
        _ ≤ 18 * (H : ℝ) * (2 * U) * (1 + Real.log (H : ℝ)) := by gcongr
        _ = _ := by ring
    have hprod : 0 ≤ (H : ℝ) * U * Real.log (H : ℝ) := by positivity
    nlinarith
  have hvdc := norm_realLogBlock_sq_vanDerCorput hH hHL ha hU hL hscale
  have hscaled : (H : ℝ) ^ 2 *
      ‖∑ j ∈ Finset.range L, realBlockPhase a U j‖ ^ 2 ≤
      76 * H * U ^ 2 * (1 + Real.log (H : ℝ)) := by
    calc
      _ ≤ ((L + H : ℕ) : ℝ) * ((H : ℝ) * L +
        18 * H * (U ^ 2 / a) * (1 + Real.log (H : ℝ))) := hvdc
      _ ≤ (2 * U) * (38 * H * U * (1 + Real.log (H : ℝ))) := by gcongr
      _ = _ := by ring
  have hcancel : (H : ℝ) * ‖∑ j ∈ Finset.range L, realBlockPhase a U j‖ ^ 2 ≤
      76 * U ^ 2 * (1 + Real.log (H : ℝ)) := by
    apply le_of_mul_le_mul_left (a := (H : ℝ)) _ hHR
    nlinarith only [hscaled]
  have hsq : ‖∑ j ∈ Finset.range L, realBlockPhase a U j‖ ^ 2 ≤
      U ^ 2 * (76 * (1 + Real.log (H : ℝ)) / H) := by
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hHR).2
    nlinarith only [hcancel]
  have hrad : 0 ≤ 76 * (1 + Real.log (H : ℝ)) / (H : ℝ) := by positivity
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).1
  simpa only [mul_pow, Real.sq_sqrt hrad] using hsq

theorem mrNorm_positiveLogBlock_le_transition_sqrt_add_one
    {a U : ℝ} {L H : ℕ} (hH : 0 < H) (hHL : H + 1 ≤ L)
    (ha : 0 < a) (hU : 0 < U) (hL : (L : ℝ) ≤ U + 1)
    (hUa : U ≤ 2 * a) (hscale : 8 * (H : ℝ) * a ≤ U ^ 2) :
    ‖∑ j ∈ Finset.range L, realBlockPhase a U j‖ ≤
      U * Real.sqrt (76 * (1 + Real.log (H : ℝ)) / H) + 1 := by
  obtain ⟨L', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show L ≠ 0 by omega)
  have hb := mrNorm_positiveLogBlock_le_transition_sqrt (L := L') hH
    (by omega) ha hU (by push_cast at hL; linarith) hUa hscale
  rw [Finset.sum_range_succ]
  exact (norm_add_le _ _).trans (by simpa using add_le_add_right hb 1)

theorem mrExists_primeMellin_transition_power_bound (R : ℕ) (hR : 2 ≤ R) :
    ∃ A₀ : ℕ, 1 ≤ A₀ ∧ ∀ {A M : ℕ}, A₀ ≤ A → M ≤ 2 * A →
      ∀ {t : ℝ}, (A : ℝ) ≤ 2 * positiveLogCoefficient t →
        positiveLogCoefficient t ≤ (A : ℝ) →
        ‖∑ n ∈ Finset.Icc A M, mrPrimeMellinMonomial 0 t n‖ ≤
          20 * (A : ℝ) ^ (1 - savingExponent R) := by
  obtain ⟨A₀, hA₀⟩ := eventually_atTop.1 eventually_eight_mul_rOneLagBudget_le
  refine ⟨max 1 A₀, Nat.le_max_left _ _, ?_⟩
  intro A M hA hM t hl hu
  have hAone : 1 ≤ A := (Nat.le_max_left 1 A₀).trans hA
  have hAR : (1 : ℝ) ≤ A := by exact_mod_cast hAone
  have hApos : (0 : ℝ) < A := zero_lt_one.trans_le hAR
  have ha : 0 < positiveLogCoefficient t := by linarith
  have hd := mrSavingExponent_le_one_div_sixtyFour hR
  let V : ℝ := (A : ℝ) ^ (1 - savingExponent R)
  have hV : 1 ≤ V := Real.one_le_rpow hAR (by linarith)
  have hpower : (A : ℝ) ^ (63 / 64 : ℝ) ≤ V :=
    Real.rpow_le_rpow_of_exponent_le hAR (by linarith)
  have hH : (rOneLagBudget A : ℝ) ≤ 2 * V := by
    calc
      _ ≤ 2 * (A : ℝ) ^ (1 / 16 : ℝ) :=
        Erdos1149.AnalyticParameters.natCeil_le_two_mul
          (Real.one_le_rpow hAR (by norm_num))
      _ ≤ 2 * V := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Real.rpow_le_rpow_of_exponent_le hAR
        linarith
  by_cases hAM : A ≤ M
  · rw [mrNorm_primeMellin_Icc_eq_positiveLogBlock (by omega) hAM]
    let L : ℕ := M - A + 1
    have hL : (L : ℝ) ≤ (A : ℝ) + 1 := by
      have hh : L ≤ A + 1 := by dsimp [L]; omega
      exact_mod_cast hh
    by_cases hlong : rOneLagBudget A + 1 ≤ L
    · have hscale : 8 * (rOneLagBudget A : ℝ) * positiveLogCoefficient t ≤
          (A : ℝ) ^ 2 := by
        have hh := hA₀ A ((Nat.le_max_right 1 A₀).trans hA)
        have hp : (A : ℝ) ^ (1 / 4 : ℝ) ≤ A := by
          calc
            _ ≤ (A : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hAR (by norm_num)
            _ = _ := Real.rpow_one _
        have hlin : 8 * (rOneLagBudget A : ℝ) ≤ A := hh.trans hp
        have hmul := mul_le_mul hlin hu (by positivity) hApos.le
        nlinarith
      have hb := mrNorm_positiveLogBlock_le_transition_sqrt_add_one
        (L := L) (rOneLagBudget_pos (by omega)) hlong ha hApos hL hl hscale
      have hlog : 0 ≤ Real.log (rOneLagBudget A : ℝ) :=
        Real.log_nonneg (by exact_mod_cast rOneLagBudget_pos (show 0 < A by omega))
      have hrad : 0 ≤ 38 * (1 + Real.log (rOneLagBudget A : ℝ)) /
          (rOneLagBudget A : ℝ) := by positivity
      have hradTwo : 0 ≤ 76 * (1 + Real.log (rOneLagBudget A : ℝ)) /
          (rOneLagBudget A : ℝ) := by positivity
      have hsqrt : Real.sqrt (76 * (1 + Real.log (rOneLagBudget A : ℝ)) /
          (rOneLagBudget A : ℝ)) ≤
          2 * Real.sqrt (38 * (1 + Real.log (rOneLagBudget A : ℝ)) /
          (rOneLagBudget A : ℝ)) := by
        have htwice : 76 * (1 + Real.log (rOneLagBudget A : ℝ)) /
            (rOneLagBudget A : ℝ) =
            2 * (38 * (1 + Real.log (rOneLagBudget A : ℝ)) /
              (rOneLagBudget A : ℝ)) := by ring
        apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).1
        rw [mul_pow, Real.sq_sqrt hrad, Real.sq_sqrt hradTwo, htwice]
        nlinarith only [hrad]
      have hcoeff := hsqrt.trans (mul_le_mul_of_nonneg_left
        (rOneLagBudget_sqrt_le_power hAone) (by norm_num : (0 : ℝ) ≤ 2))
      have hcollapse : (A : ℝ) * (A : ℝ) ^ (-1 / 64 : ℝ) =
          (A : ℝ) ^ (63 / 64 : ℝ) := by
        calc
          _ = (A : ℝ) ^ ((1 : ℝ) + (-1 / 64 : ℝ)) := by
            rw [Real.rpow_add hApos, Real.rpow_one]
          _ = _ := by norm_num
      have hmain : (A : ℝ) * Real.sqrt
          (76 * (1 + Real.log (rOneLagBudget A : ℝ)) / (rOneLagBudget A : ℝ)) ≤
          18 * V := by
        calc
          _ ≤ (A : ℝ) * (2 * (9 * (A : ℝ) ^ (-1 / 64 : ℝ))) :=
            mul_le_mul_of_nonneg_left hcoeff hApos.le
          _ = 18 * (A : ℝ) ^ (63 / 64 : ℝ) := by rw [← hcollapse]; ring
          _ ≤ 18 * V := mul_le_mul_of_nonneg_left hpower (by norm_num)
      change ‖∑ j ∈ Finset.range L,
        HigherDerivative.phase (shiftedLogPhase (positiveLogCoefficient t) A j)‖ ≤ 20 * V
      change ‖∑ j ∈ Finset.range L,
        HigherDerivative.phase (shiftedLogPhase (positiveLogCoefficient t) A j)‖ ≤ _ at hb
      linarith
    · have hshort : L ≤ rOneLagBudget A := by omega
      have hb : ‖∑ j ∈ Finset.range L,
          HigherDerivative.phase (shiftedLogPhase (positiveLogCoefficient t) A j)‖ ≤ L := by
        exact (norm_sum_le _ _).trans (by simp)
      have hh : (L : ℝ) ≤ rOneLagBudget A := by exact_mod_cast hshort
      change ‖∑ j ∈ Finset.range L,
        HigherDerivative.phase (shiftedLogPhase (positiveLogCoefficient t) A j)‖ ≤ 20 * V
      linarith
  · simp only [Finset.Icc_eq_empty_of_lt (by omega : M < A), Finset.sum_empty, norm_zero]
    positivity

end

end Erdos67b
