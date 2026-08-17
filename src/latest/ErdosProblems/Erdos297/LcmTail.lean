/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.FiniteHoeffding

/-!
# Subexponential size of the common denominator

For the Liu--Sawhney smoothness cutoff
`S(N) = floor (N / (log N)^4)`, the common denominator
`Q(N) = lcm(1,...,S(N))` is `exp(o(N))`.  This file records the precise
eventual estimate used when an exponentially small exceptional mass has to
be compared with `1 / (4 Q(N))`.
-/

open Filter

namespace Erdos297.LcmTail

open Erdos297.GoodFactorization Erdos297.FiniteHoeffding

noncomputable section

/-- The elementary numerical estimate behind the subexponential LCM bound.
The term `log 4` is included so that exponentiating gives the factor `4`
needed in the local-limit argument. -/
lemma eventually_log_four_add_five_S_le_mul (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      Real.log 4 + 5 * (Erdos297.S N : ℝ) ≤ eta * (N : ℝ) := by
  have hlog := Erdos297.tendsto_logScale.eventually_ge_atTop
    (max 1 (10 / eta))
  have hN := tendsto_natCast_atTop_atTop.eventually_ge_atTop
    (2 * Real.log 4 / eta)
  filter_upwards [hlog, hN, Erdos297.eventually_pos_scales]
      with N hlog hN hpos
  rcases hpos with ⟨hNpos, hlogOne, -⟩
  have hlogPos : 0 < Erdos297.logScale N := zero_lt_one.trans hlogOne
  have hlogPowPos : 0 < Erdos297.logScale N ^ 4 := pow_pos hlogPos _
  have hlogLePow : Erdos297.logScale N ≤ Erdos297.logScale N ^ 4 := by
    calc
      Erdos297.logScale N = Erdos297.logScale N * 1 := by ring
      _ ≤ Erdos297.logScale N * Erdos297.logScale N ^ 3 :=
        mul_le_mul_of_nonneg_left (one_le_pow₀ hlogOne.le) hlogPos.le
      _ = Erdos297.logScale N ^ 4 := by ring
  have htenDiv : 10 / eta ≤ Erdos297.logScale N ^ 4 :=
    (le_max_right 1 (10 / eta)).trans hlog |>.trans hlogLePow
  have hten : (10 : ℝ) ≤ eta * Erdos297.logScale N ^ 4 := by
    simpa [mul_comm] using (div_le_iff₀ heta).mp htenDiv
  have hSRealNonneg : 0 ≤ Erdos297.SReal N := by
    exact div_nonneg hNpos.le hlogPowPos.le
  have hSfloor : (Erdos297.S N : ℝ) ≤ Erdos297.SReal N := by
    simpa [Erdos297.S] using Nat.floor_le hSRealNonneg
  have hfiveDiv : 5 / Erdos297.logScale N ^ 4 ≤ eta / 2 := by
    rw [div_le_iff₀ hlogPowPos]
    nlinarith
  have hfiveS :
      5 * (Erdos297.S N : ℝ) ≤ eta * (N : ℝ) / 2 := by
    calc
      5 * (Erdos297.S N : ℝ) ≤ 5 * Erdos297.SReal N :=
        mul_le_mul_of_nonneg_left hSfloor (by norm_num)
      _ = (N : ℝ) * (5 / Erdos297.logScale N ^ 4) := by
        rw [Erdos297.SReal]
        ring
      _ ≤ (N : ℝ) * (eta / 2) :=
        mul_le_mul_of_nonneg_left hfiveDiv hNpos.le
      _ = eta * (N : ℝ) / 2 := by ring
  have hlogFour : Real.log 4 ≤ eta * (N : ℝ) / 2 := by
    have hmul := mul_le_mul_of_nonneg_left hN heta.le
    have hetaNe : eta ≠ 0 := ne_of_gt heta
    field_simp [hetaNe] at hmul ⊢
    linarith
  linarith

/-- `Q(S(N)) = lcm(1,...,S(N))` is subexponential in the exact form needed
for the lower-bound assembly: every prescribed exponential saving eventually
dominates the factor `4 Q(S(N))`. -/
theorem eventually_exp_neg_mul_le_inv_four_smoothLcm
    (eta : ℝ) (heta : 0 < eta) :
    ∀ᶠ N : ℕ in atTop,
      Real.exp (-(eta * (N : ℝ))) ≤
        1 / (4 * (smoothLcm (Erdos297.S N) : ℝ)) := by
  have hQ := tendsto_S_atTop.eventually
    eventually_smoothLcm_le_exp_five_mul
  filter_upwards [eventually_log_four_add_five_S_le_mul eta heta, hQ]
      with N hnum hQ
  have hQpos : 0 < (smoothLcm (Erdos297.S N) : ℝ) := by
    exact_mod_cast Nat.lcmUpto_pos (Erdos297.S N)
  rw [le_div_iff₀ (mul_pos (by norm_num) hQpos)]
  calc
    Real.exp (-(eta * (N : ℝ))) *
          (4 * (smoothLcm (Erdos297.S N) : ℝ)) =
        4 * (smoothLcm (Erdos297.S N) : ℝ) *
          Real.exp (-(eta * (N : ℝ))) := by ring
    _ ≤ 4 * Real.exp (5 * (Erdos297.S N : ℝ)) *
          Real.exp (-(eta * (N : ℝ))) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hQ (by norm_num)) (Real.exp_nonneg _)
    _ = Real.exp
          (Real.log 4 + 5 * (Erdos297.S N : ℝ) + -(eta * (N : ℝ))) := by
      rw [Real.exp_add, Real.exp_add,
        Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    _ ≤ Real.exp 0 := Real.exp_monotone (by linarith)
    _ = 1 := Real.exp_zero

end

end Erdos297.LcmTail
