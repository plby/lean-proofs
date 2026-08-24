import ErdosProblems.Erdos587.UnconditionalUpperBound
import ErdosProblems.Erdos587.LowerBoundMax

/-! The explicit bounds and the weaker asymptotic consequences in the source. -/

open Filter

namespace Erdos587

theorem upper_bound : ∃ O : ℕ, 0 < O ∧ ∃ K : ℝ, 0 < K ∧ ∃ N₀ : ℕ,
    ∀ N ≥ N₀, (MaxNotSqSum N : ℝ) ≤ K * (N : ℝ) ^ (1 / 3 : ℝ) * Real.log N ^ O := by
  obtain ⟨O, hO, K, hK, hbound⟩ := unconditional_nguyen_vu
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hbound
  refine ⟨O, hO, K, hK, N₀, ?_⟩
  intro N hN
  simpa only [nthRoot_three_natCast, one_div] using hN₀ N hN

theorem subpolynomial_upper_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      (MaxNotSqSum N : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) *
        Real.exp (C * Real.log N / Real.log (Real.log N)) := by
  obtain ⟨O, hO, K, hK, hbound⟩ := unconditional_nguyen_vu
  let c : ℝ := |Real.log K| + O + 1
  have hc : 0 < c := by dsimp [c]; positivity
  have hlittle := (Real.isLittleO_pow_log_id_atTop (n := 2)).const_mul_left c
  have hpoly : ∀ᶠ x : ℝ in atTop, c * Real.log x ^ 2 ≤ x := by
    filter_upwards [hlittle.bound (show (0 : ℝ) < 1 by norm_num),
      eventually_ge_atTop 0] with x hx hx0
    have hnonneg : 0 ≤ c * Real.log x ^ 2 := by positivity
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg, abs_of_nonneg hx0,
      one_mul, id_eq] using hx
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨1, by norm_num, ?_⟩
  filter_upwards [hbound, hlog.eventually hpoly,
    (Real.tendsto_log_atTop.comp hlog).eventually_ge_atTop 1,
    hlog.eventually_gt_atTop 0] with N hupper hpolyN hloglog hlogN
  change 1 ≤ Real.log (Real.log (N : ℝ)) at hloglog
  have hloglog0 : 0 < Real.log (Real.log N) := by linarith
  have hcoeff : Real.log K + (O : ℝ) * Real.log (Real.log N) ≤
      Real.log N / Real.log (Real.log N) := by
    apply (le_div_iff₀ hloglog0).mpr
    have ha : Real.log K ≤ |Real.log K| := le_abs_self _
    have hc' : (Real.log K + (O : ℝ) * Real.log (Real.log N)) * Real.log (Real.log N) ≤
        c * Real.log (Real.log N) ^ 2 := by
      have hu : Real.log (Real.log N) ≤ Real.log (Real.log N) ^ 2 := by
        nlinarith only [hloglog]
      have hterm : Real.log K * Real.log (Real.log N) ≤
          |Real.log K| * Real.log (Real.log N) ^ 2 :=
        (mul_le_mul_of_nonneg_right ha hloglog0.le).trans
          (mul_le_mul_of_nonneg_left hu (abs_nonneg _))
      dsimp [c]
      nlinarith only [hterm, sq_nonneg (Real.log (Real.log N))]
    exact hc'.trans hpolyN
  have hexp : K * Real.log N ^ O ≤ Real.exp (Real.log N / Real.log (Real.log N)) := by
    calc
      K * Real.log N ^ O = Real.exp (Real.log K + (O : ℝ) * Real.log (Real.log N)) := by
        rw [Real.exp_add, Real.exp_nat_mul, Real.exp_log hK, Real.exp_log hlogN]
      _ ≤ _ := Real.exp_le_exp.mpr hcoeff
  have hroot : 0 ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by positivity
  calc
    (MaxNotSqSum N : ℝ) ≤ K * Real.nthRoot 3 N * Real.log N ^ O := hupper
    _ = (N : ℝ) ^ (1 / 3 : ℝ) * (K * Real.log N ^ O) := by
      rw [nthRoot_three_natCast]
      simp only [one_div]
      ring
    _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) * Real.exp (Real.log N / Real.log (Real.log N)) :=
      mul_le_mul_of_nonneg_left hexp hroot
    _ = _ := by rw [one_mul]

theorem eventually_power_bounds (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ (1 / 3 - ε) ≤ (MaxNotSqSum N : ℝ) ∧
      (MaxNotSqSum N : ℝ) ≤ (N : ℝ) ^ (1 / 3 + ε) := by
  obtain ⟨O, hO, K, hK, hbound⟩ := unconditional_nguyen_vu
  have hlittle := (isLittleO_log_rpow_rpow_atTop (O : ℝ) hε).const_mul_left K
  have hlogbound : ∀ᶠ x : ℝ in atTop, K * Real.log x ^ O ≤ x ^ ε := by
    filter_upwards [hlittle.bound (show (0 : ℝ) < 1 by norm_num),
      eventually_ge_atTop 1] with x hx hx1
    have hx0 : 0 ≤ x := by linarith
    have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
    simpa only [Real.rpow_natCast, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ K * Real.log x ^ O by positivity),
      abs_of_nonneg (Real.rpow_nonneg hx0 ε), one_mul] using hx
  have hpow : ∀ᶠ N : ℕ in atTop, (4 : ℝ) ≤ (N : ℝ) ^ ε :=
    ((tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 4
  filter_upwards [hbound, tendsto_natCast_atTop_atTop.eventually hlogbound,
    hpow, eventually_ge_atTop 64] with N hupper hlog hpowN hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hroot : 0 ≤ (N : ℝ) ^ (1 / 3 : ℝ) := by positivity
  constructor
  · calc
      (N : ℝ) ^ (1 / 3 - ε) = (N : ℝ) ^ (1 / 3 : ℝ) / (N : ℝ) ^ ε :=
        Real.rpow_sub hN0 _ _
      _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) / 4 :=
        div_le_div_of_nonneg_left hroot (by norm_num) hpowN
      _ ≤ (MaxNotSqSum N : ℝ) := by
        simpa only [nthRoot_three_natCast, one_div] using lower_bound N hN
  · calc
      (MaxNotSqSum N : ℝ) ≤ K * Real.nthRoot 3 N * Real.log N ^ O := hupper
      _ = (N : ℝ) ^ (1 / 3 : ℝ) * (K * Real.log N ^ O) := by
        rw [nthRoot_three_natCast]
        simp only [one_div]
        ring
      _ ≤ (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ ε :=
        mul_le_mul_of_nonneg_left hlog hroot
      _ = (N : ℝ) ^ (1 / 3 + ε) := (Real.rpow_add hN0 _ _).symm

end Erdos587
