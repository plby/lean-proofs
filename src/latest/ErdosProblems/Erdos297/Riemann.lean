/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.Statement

/-!
# One-dimensional Riemann sums for Erdős Problem 297

This file records the analytic Riemann-sum input in the normalization used by
the counting argument.  The generic theorem is stated for a function continuous
on `[0,1]`; the endpoint-extended logistic functions are then instances.
-/

namespace Erdos297

open Filter Finset MeasureTheory Set
open scoped BigOperators Topology Interval

noncomputable section

/-- The normalized right-endpoint Riemann sum on `[0,1]`. -/
def rightRiemannSum (f : ℝ → ℝ) (N : ℕ) : ℝ :=
  (∑ k ∈ range N, f (((k + 1 : ℕ) : ℝ) / N)) / N

/-- Right-endpoint Riemann sums of a continuous function on `[0,1]` converge
to its integral. -/
theorem tendsto_rightRiemannSum {f : ℝ → ℝ} (hf : ContinuousOn f (Icc 0 1)) :
    Tendsto (rightRiemannSum f) atTop (nhds (∫ x in (0 : ℝ)..1, f x)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have huc : UniformContinuousOn f (Icc (0 : ℝ) 1) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf
  rcases (Metric.uniformContinuousOn_iff.mp huc) (ε / 2) (by positivity) with ⟨δ, hδ, hδf⟩
  obtain ⟨N₀ : ℕ, hN₀⟩ : ∃ N₀ : ℕ, 0 < N₀ ∧ (N₀ : ℝ)⁻¹ < δ := by
    have hlim : Tendsto (fun N : ℕ ↦ (N : ℝ)⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_nhds_zero_nat
    rcases (Metric.tendsto_atTop.mp hlim) δ hδ with ⟨N, hN⟩
    refine ⟨max 1 N, by omega, ?_⟩
    have hd := hN _ (Nat.le_max_right 1 N)
    rw [Real.dist_eq, sub_zero, abs_of_nonneg] at hd
    · exact hd
    · positivity
  refine ⟨N₀, fun N hN ↦ ?_⟩
  have hNpos : 0 < N := hN₀.1.trans_le hN
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hinv : (N : ℝ)⁻¹ < δ := by
    calc
      (N : ℝ)⁻¹ ≤ (N₀ : ℝ)⁻¹ :=
        inv_anti₀ (by exact_mod_cast hN₀.1) (by exact_mod_cast hN)
      _ < δ := hN₀.2
  have hcell (k : ℕ) (hk : k < N) :
      ‖(∫ x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N,
          f (((k + 1 : ℕ) : ℝ) / N) - f x)‖ ≤ (ε / 2) / N := by
    have hleft : (0 : ℝ) ≤ (k : ℝ) / N := by positivity
    have hright : (((k + 1 : ℕ) : ℝ) / N) ≤ 1 := by
      rw [div_le_one hNreal]
      exact_mod_cast Nat.succ_le_iff.mpr hk
    have horder : (k : ℝ) / N ≤ ((k + 1 : ℕ) : ℝ) / N := by
      gcongr
      exact_mod_cast Nat.le_succ k
    calc
      ‖(∫ x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N,
          f (((k + 1 : ℕ) : ℝ) / N) - f x)‖
          ≤ (ε / 2) * |(((k + 1 : ℕ) : ℝ) / N) - (k : ℝ) / N| := by
            apply intervalIntegral.norm_integral_le_of_norm_le_const
            intro x hx
            simp only [uIoc_of_le horder] at hx
            have hxI : x ∈ Icc (0 : ℝ) 1 :=
              ⟨hleft.trans hx.1.le, hx.2.trans hright⟩
            have hrI : (((k + 1 : ℕ) : ℝ) / N) ∈ Icc (0 : ℝ) 1 :=
              ⟨by positivity, hright⟩
            rw [Real.norm_eq_abs, abs_sub_comm]
            exact le_of_lt (hδf x hxI (((k + 1 : ℕ) : ℝ) / N) hrI (by
              rw [Real.dist_eq, abs_of_nonpos (sub_nonpos.mpr hx.2)]
              simp only [neg_sub]
              calc
                (((k + 1 : ℕ) : ℝ) / N) - x
                    ≤ (((k + 1 : ℕ) : ℝ) / N) - (k : ℝ) / N :=
                  sub_le_sub_left hx.1.le _
                _ = (N : ℝ)⁻¹ := by field_simp; norm_num
                _ < δ := hinv))
      _ = (ε / 2) / N := by
        rw [abs_of_nonneg (sub_nonneg.mpr horder)]
        simp only [Nat.cast_add, Nat.cast_one]
        field_simp
        ring
  have hfint : IntervalIntegrable f volume (0 : ℝ) 1 :=
    hf.intervalIntegrable_of_Icc zero_le_one
  have hsumint :
      ∑ k ∈ range N, ∫ x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N, f x =
        ∫ x in (0 : ℝ)..1, f x := by
    simpa [hNpos.ne'] using intervalIntegral.sum_integral_adjacent_intervals
      (a := fun k : ℕ ↦ (k : ℝ) / N)
      (f := f) (n := N) (fun k hk ↦
        hfint.mono_set (by
          rw [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le (by
            gcongr
            exact_mod_cast Nat.le_succ k)]
          intro x hx
          have hx0 : (0 : ℝ) ≤ x :=
            (show (0 : ℝ) ≤ (k : ℝ) / N by positivity).trans hx.1
          exact ⟨hx0,
            hx.2.trans (by
              rw [div_le_one hNreal]
              exact_mod_cast Nat.succ_le_iff.mpr hk)⟩))
  have hsumconst :
      rightRiemannSum f N =
        ∑ k ∈ range N, ∫ _x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N,
          f (((k + 1 : ℕ) : ℝ) / N) := by
    simp only [rightRiemannSum, intervalIntegral.integral_const, smul_eq_mul]
    rw [sum_div]
    apply sum_congr rfl
    intro k hk
    have hkN : k < N := mem_range.mp hk
    simp only [Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  rw [Real.dist_eq, hsumconst, ← hsumint, ← sum_sub_distrib]
  calc
    ‖∑ k ∈ range N,
        ((∫ _x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N,
            f (((k + 1 : ℕ) : ℝ) / N)) -
          ∫ x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N, f x)‖
        ≤ ∑ k ∈ range N, ‖
          ((∫ _x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N,
              f (((k + 1 : ℕ) : ℝ) / N)) -
            ∫ x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N, f x)‖ :=
      norm_sum_le _ _
    _ = ∑ k ∈ range N, ‖
        ∫ x in (k : ℝ) / N..((k + 1 : ℕ) : ℝ) / N,
          f (((k + 1 : ℕ) : ℝ) / N) - f x‖ := by
      apply sum_congr rfl
      intro k hk
      have hflocal : IntervalIntegrable f volume
          ((k : ℝ) / N) (((k + 1 : ℕ) : ℝ) / N) :=
        hfint.mono_set (by
          have hkN := mem_range.mp hk
          rw [Set.uIcc_of_le zero_le_one, Set.uIcc_of_le (by
            gcongr
            exact_mod_cast Nat.le_succ k)]
          intro x hx
          have hx0 : (0 : ℝ) ≤ x :=
            (show (0 : ℝ) ≤ (k : ℝ) / N by positivity).trans hx.1
          exact ⟨hx0,
            hx.2.trans (by
              rw [div_le_one hNreal]
              exact_mod_cast Nat.succ_le_iff.mpr hkN)⟩)
      rw [intervalIntegral.integral_sub intervalIntegrable_const hflocal]
    _ ≤ ∑ _k ∈ range N, (ε / 2) / N := by
      apply sum_le_sum
      intro k hk
      exact hcell k (mem_range.mp hk)
    _ = ε / 2 := by
      simp only [sum_const, card_range, nsmul_eq_mul, div_eq_mul_inv]
      field_simp
    _ < ε := by linarith

/-! ### The two endpoint-extended kernels -/

/-- A scaled copy of Mathlib's smooth flat function.  On the positive
half-line this is `exp (-lam / x)`. -/
private def scaledGlue (lam x : ℝ) : ℝ :=
  expNegInvGlue (x / lam)

/-- The flat quotient needed for the moment kernel.  On the positive
half-line this is `exp (-lam / x) / x`. -/
private def scaledGlueDiv (lam x : ℝ) : ℝ :=
  lam⁻¹ * ((x / lam)⁻¹ * expNegInvGlue (x / lam))

private theorem continuous_scaledGlue (lam : ℝ) : Continuous (scaledGlue lam) := by
  have hglue : Continuous expNegInvGlue := by
    simpa using
      (expNegInvGlue.continuous_polynomial_eval_inv_mul (1 : Polynomial ℝ))
  exact hglue.comp (continuous_id.div_const lam)

private theorem continuous_scaledGlueDiv (lam : ℝ) : Continuous (scaledGlueDiv lam) := by
  have hflat : Continuous (fun y : ℝ ↦ y⁻¹ * expNegInvGlue y) := by
    simpa using
      (expNegInvGlue.continuous_polynomial_eval_inv_mul (Polynomial.X : Polynomial ℝ))
  exact continuous_const.mul (hflat.comp (continuous_id.div_const lam))

private theorem scaledGlue_nonneg (lam x : ℝ) : 0 ≤ scaledGlue lam x :=
  expNegInvGlue.nonneg _

private theorem selectionProbability_eq_scaledGlue {lam x : ℝ} (hlam : 0 < lam)
    (hx : 0 ≤ x) :
    selectionProbability lam x = scaledGlue lam x / (1 + scaledGlue lam x) := by
  by_cases hx0 : x = 0
  · subst x
    simp [selectionProbability, scaledGlue]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hquot : 0 < x / lam := div_pos hxpos hlam
    simp only [selectionProbability, hx0, if_false, scaledGlue, expNegInvGlue,
      if_neg (not_le.mpr hquot)]
    rw [show lam / x = -(-lam / x) by ring, Real.exp_neg]
    have hexp : Real.exp (-lam / x) ≠ 0 := (Real.exp_pos _).ne'
    field_simp
    ring

private theorem momentKernel_eq_scaledGlue {lam x : ℝ} (hlam : 0 < lam)
    (hx : 0 ≤ x) :
    momentKernel lam x = scaledGlueDiv lam x / (1 + scaledGlue lam x) := by
  by_cases hx0 : x = 0
  · subst x
    simp [momentKernel, scaledGlueDiv, scaledGlue]
  · rw [momentKernel, if_neg hx0, selectionProbability_eq_scaledGlue hlam hx]
    have hlam0 : lam ≠ 0 := ne_of_gt hlam
    have hnum : scaledGlueDiv lam x = scaledGlue lam x / x := by
      simp only [scaledGlueDiv, scaledGlue, div_eq_mul_inv]
      field_simp
    rw [hnum]
    ring

private theorem freeEnergyKernel_eq_scaledGlue {lam x : ℝ} (hlam : 0 < lam)
    (hx : 0 ≤ x) :
    freeEnergyKernel lam x = Real.log (1 + scaledGlue lam x) := by
  by_cases hx0 : x = 0
  · subst x
    simp [freeEnergyKernel, scaledGlue]
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have hquot : 0 < x / lam := div_pos hxpos hlam
    simp [freeEnergyKernel, hx0, scaledGlue, expNegInvGlue, not_le.mpr hquot]
    ring_nf

/-- The endpoint extension of the moment kernel is continuous on `[0,1]`.
The exponential decay at zero is supplied by `expNegInvGlue`. -/
theorem continuousOn_momentKernel {lam : ℝ} (hlam : 0 < lam) :
    ContinuousOn (momentKernel lam) (Icc 0 1) := by
  have hden : Continuous (fun x ↦ 1 + scaledGlue lam x) :=
    continuous_const.add (continuous_scaledGlue lam)
  have hrepr : Continuous
      (fun x ↦ scaledGlueDiv lam x / (1 + scaledGlue lam x)) :=
    (continuous_scaledGlueDiv lam).div hden fun x ↦ by
      exact ne_of_gt (by linarith [scaledGlue_nonneg lam x])
  exact hrepr.continuousOn.congr fun x hx ↦ momentKernel_eq_scaledGlue hlam hx.1

/-- The endpoint extension of the free-energy kernel is continuous on
`[0,1]`. -/
theorem continuousOn_freeEnergyKernel {lam : ℝ} (hlam : 0 < lam) :
    ContinuousOn (freeEnergyKernel lam) (Icc 0 1) := by
  have hinner : Continuous (fun x ↦ 1 + scaledGlue lam x) :=
    continuous_const.add (continuous_scaledGlue lam)
  have hlog : Continuous (fun x ↦ Real.log (1 + scaledGlue lam x)) := by
    rw [continuous_iff_continuousAt]
    intro x
    exact hinner.continuousAt.log <| ne_of_gt <| by
      linarith [scaledGlue_nonneg lam x]
  exact hlog.continuousOn.congr fun x hx ↦
    freeEnergyKernel_eq_scaledGlue hlam hx.1

/-- The normalized discrete moment-kernel sum converges to the moment
integral. -/
theorem tendsto_rightRiemannSum_momentKernel {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (rightRiemannSum (momentKernel lam)) atTop (nhds (moment lam)) := by
  have h := tendsto_rightRiemannSum (continuousOn_momentKernel hlam)
  simpa only [moment, intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc] using h

/-- The normalized discrete free-energy sum converges to its defining
integral. -/
theorem tendsto_rightRiemannSum_freeEnergyKernel {lam : ℝ} (hlam : 0 < lam) :
    Tendsto (rightRiemannSum (freeEnergyKernel lam)) atTop
      (nhds (∫ x in Icc (0 : ℝ) 1, freeEnergyKernel lam x)) := by
  have h := tendsto_rightRiemannSum (continuousOn_freeEnergyKernel hlam)
  simpa only [intervalIntegral.integral_of_le zero_le_one,
    ← integral_Icc_eq_integral_Ioc] using h

/-- Reindexing the moment Riemann sum gives the unnormalized reciprocal
sum used by the probabilistic model. -/
theorem tendsto_sum_Icc_selectionProbability_div {lam : ℝ} (hlam : 0 < lam) :
    Tendsto
      (fun N : ℕ ↦ ∑ n ∈ Icc 1 N,
        selectionProbability lam ((n : ℝ) / N) / (n : ℝ))
      atTop (nhds (moment lam)) := by
  apply (tendsto_rightRiemannSum_momentKernel hlam).congr'
  filter_upwards [eventually_gt_atTop 0] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← Finset.Ico_succ_right_eq_Icc 1 N]
  change rightRiemannSum (momentKernel lam) N =
    ∑ n ∈ Ico 1 (N + 1), selectionProbability lam ((n : ℝ) / N) / (n : ℝ)
  rw [← Finset.sum_Ico_add
      (fun n : ℕ ↦ selectionProbability lam ((n : ℝ) / N) / (n : ℝ)) 0 N 1]
  simp only [Nat.Ico_zero_eq_range]
  rw [rightRiemannSum, sum_div]
  apply sum_congr rfl
  intro k hk
  have hkpos : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  simp only [momentKernel, div_ne_zero (by positivity : ((k + 1 : ℕ) : ℝ) ≠ 0) hN0,
    if_false]
  field_simp
  simp [Nat.add_comm]
  ring

#print axioms Erdos297.tendsto_rightRiemannSum_momentKernel
#print axioms Erdos297.tendsto_rightRiemannSum_freeEnergyKernel
#print axioms Erdos297.tendsto_sum_Icc_selectionProbability_div

end

end Erdos297
