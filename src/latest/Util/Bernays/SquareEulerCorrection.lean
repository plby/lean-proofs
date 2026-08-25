import Util.Bernays.LocalEulerFactor
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The convergent square Euler correction

The inert-prime correction to the square of the local Dirichlet series is
positive and continuous at `s = 1`. Uniform summability is proved on a whole
neighborhood of `1`, using the convergent `p^(-3/2)` majorant.
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

theorem neg_log_one_sub_bound {u : ℝ} (hu₀ : 0 ≤ u) (hu₁ : u ≤ 1 / 2) :
    0 ≤ -log (1 - u) ∧ -log (1 - u) ≤ 2 * u := by
  have hpos : 0 < 1 - u := by linarith
  refine ⟨neg_nonneg.mpr (log_nonpos hpos.le (by linarith)), ?_⟩
  have hlog : -log (1 - u) ≤ (1 - u)⁻¹ - 1 := by
    simpa only [log_inv] using log_le_sub_one_of_pos (inv_pos.mpr hpos)
  have heq : (1 - u)⁻¹ - 1 = u / (1 - u) := by
    field_simp
    ring
  rw [heq] at hlog
  refine hlog.trans ((div_le_iff₀ hpos).mpr ?_)
  nlinarith [mul_nonneg hu₀ (by linarith : 0 ≤ 1 - 2 * u)]

theorem squarePrimePower_bounds (p : Nat.Primes) (s : ℝ) :
    0 ≤ (((p : ℕ) : ℝ) ^ (-(2 * max (3 / 4) s))) ∧
    (((p : ℕ) : ℝ) ^ (-(2 * max (3 / 4) s))) ≤ (((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ∧
    (((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) ≤ 1 / 2 := by
  have hp₂ : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast p.property.two_le
  have hp₁ : (1 : ℝ) ≤ (p : ℕ) := by linarith
  have hp₀ : (0 : ℝ) < (p : ℕ) := by linarith
  refine ⟨rpow_nonneg hp₀.le _, rpow_le_rpow_of_exponent_le hp₁ ?_, ?_⟩
  · have := le_max_left (3 / 4 : ℝ) s
    linarith
  · calc
      _ ≤ (((p : ℕ) : ℝ) ^ (-1 : ℝ)) := rpow_le_rpow_of_exponent_le hp₁ (by norm_num)
      _ = 1 / ((p : ℕ) : ℝ) := by rw [rpow_neg_one, one_div]
      _ ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hp₂

noncomputable def squareLogTerm (S : ℕ → Prop) (p : Nat.Primes) (s : ℝ) : ℝ :=
  if S p then -log (1 - ((p : ℕ) : ℝ) ^ (-(2 * max (3 / 4) s))) else 0

theorem squareLogTerm_norm_le (S : ℕ → Prop) (p : Nat.Primes) (s : ℝ) :
    ‖squareLogTerm S p s‖ ≤ 2 * ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
  obtain ⟨hu₀, hu₁, hu₂⟩ := squarePrimePower_bounds p s
  have hlog := neg_log_one_sub_bound hu₀ (hu₁.trans hu₂)
  unfold squareLogTerm
  split_ifs
  · rw [Real.norm_of_nonneg hlog.1]
    exact hlog.2.trans (mul_le_mul_of_nonneg_left hu₁ (by norm_num))
  · rw [norm_zero]
    positivity

theorem squareLogMajorant_summable :
    Summable (fun p : Nat.Primes => 2 * ((p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))) := by
  have h : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    summable_nat_rpow.mpr (by norm_num)
  exact (h.subtype Nat.Prime).mul_left 2

theorem squareLogTerm_summable (S : ℕ → Prop) (s : ℝ) :
    Summable (fun p : Nat.Primes => squareLogTerm S p s) :=
  Summable.of_norm_bounded squareLogMajorant_summable (fun p => squareLogTerm_norm_le S p s)

theorem continuous_squareLogTerm (S : ℕ → Prop) (p : Nat.Primes) :
    Continuous (squareLogTerm S p) := by
  unfold squareLogTerm
  split_ifs
  · apply Continuous.neg
    apply Continuous.log
    · apply continuous_const.sub
      exact (continuous_const_rpow (by exact_mod_cast p.property.ne_zero)).comp
        ((continuous_const.mul (continuous_const.max continuous_id)).neg)
    · intro s
      obtain ⟨_, h₁, h₂⟩ := squarePrimePower_bounds p s
      linarith
  · exact continuous_const

noncomputable def squareCorrection (S : ℕ → Prop) (s : ℝ) : ℝ :=
  exp (∑' p : Nat.Primes, squareLogTerm S p s)

theorem squareCorrection_pos (S : ℕ → Prop) (s : ℝ) : 0 < squareCorrection S s := exp_pos _

theorem continuous_squareCorrection (S : ℕ → Prop) : Continuous (squareCorrection S) :=
  continuous_exp.comp (continuous_tsum (continuous_squareLogTerm S)
    squareLogMajorant_summable (squareLogTerm_norm_le S))

theorem squareCorrection_hasProd (S : ℕ → Prop) {s : ℝ} (hs : 3 / 4 ≤ s) :
    HasProd (fun p : Nat.Primes =>
      if S p then (1 - ((((p : ℕ) : ℝ) ^ s)⁻¹) ^ 2)⁻¹ else 1)
      (squareCorrection S s) := by
  change HasProd _ (exp (∑' p : Nat.Primes, squareLogTerm S p s))
  apply (squareLogTerm_summable S s).hasSum.rexp.congr_fun
  intro p
  change (if S p then _ else 1) = exp (squareLogTerm S p s)
  unfold squareLogTerm
  by_cases hS : S p
  · rw [if_pos hS, if_pos hS, exp_neg]
    have hpos : 0 < 1 - ((p : ℕ) : ℝ) ^ (-(2 * max (3 / 4) s)) := by
      have h := (squarePrimePower_bounds p s).2.1.trans (squarePrimePower_bounds p s).2.2
      linarith
    rw [exp_log hpos, max_eq_right hs]
    have hpow : ((p : ℕ) : ℝ) ^ (-(2 * s)) = ((((p : ℕ) : ℝ) ^ s)⁻¹) ^ 2 := by
      let x : ℝ := (p : ℕ)
      have hx : 0 ≤ x := Nat.cast_nonneg (p : ℕ)
      change x ^ (-(2 * s)) = ((x ^ s)⁻¹) ^ 2
      rw [rpow_neg hx, mul_comm (2 : ℝ) s]
      exact (congrArg (fun t : ℝ => t⁻¹) (rpow_mul_natCast hx s 2)).trans (inv_pow _ _).symm
    exact (congrArg (fun t : ℝ => (1 - t)⁻¹) hpow).symm
  · simp only [if_neg hS, exp_zero]

end Bernays
