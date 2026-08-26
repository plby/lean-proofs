import UnitFractions.ForMathlib.BasicEstimates

/-!
# Prime harmonic estimates

The imported Mertens estimate is proved in the repository. This module only changes its
finite-sum notation and packages its bounded-error consequences.
-/

namespace Erdos856b

open Real Filter Asymptotics
open scoped BigOperators Topology

noncomputable def primeHarmonic (x : ℝ) : ℝ :=
  ∑ p ∈ Nat.primesLE ⌊x⌋₊, (p : ℝ)⁻¹

theorem primeHarmonic_eq_prime_summatory (x : ℝ) :
    primeHarmonic x = prime_summatory (fun p => (p : ℝ)⁻¹) 1 x := by
  unfold primeHarmonic prime_summatory
  apply Finset.sum_congr
  · ext p
    simp only [Nat.mem_primesLE, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨fun h => ⟨⟨h.2.one_le, h.1⟩, h.2⟩, fun h => ⟨h.1.2, h.2⟩⟩
  · intro p _
    rfl

theorem primeHarmonic_error_bounded :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ x : ℝ in atTop, |primeHarmonic x - log (log x)| ≤ K := by
  have hO := prime_reciprocal.trans (is_o_log_inv_one (by norm_num : (1 : ℝ) ≠ 0)).isBigO
  obtain ⟨K, hK, hbound⟩ := hO.exists_pos
  refine ⟨K + |meissel_mertens|, by positivity, ?_⟩
  filter_upwards [hbound.bound] with x hx
  rw [primeHarmonic_eq_prime_summatory]
  have heq : prime_summatory (fun p => (p : ℝ)⁻¹) 1 x - log (log x) =
      (prime_summatory (fun p => (p : ℝ)⁻¹) 1 x - (log (log x) + meissel_mertens)) +
        meissel_mertens := by ring
  rw [heq]
  apply (abs_add_le _ _).trans
  simpa only [Real.norm_eq_abs, norm_one, mul_one, add_comm] using
    add_le_add_right hx |meissel_mertens|

theorem tendsto_primeHarmonic_div_log_log :
    Tendsto (fun x : ℝ => primeHarmonic x / log (log x)) atTop (𝓝 1) := by
  obtain ⟨K, hK, hbound⟩ := primeHarmonic_error_bounded
  have hL : Tendsto (fun x : ℝ => log (log x)) atTop atTop :=
    tendsto_log_atTop.comp tendsto_log_atTop
  have hzero : Tendsto (fun x : ℝ => (primeHarmonic x - log (log x)) / log (log x))
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun x : ℝ => K / log (log x)) ?_
      (tendsto_const_nhds.div_atTop hL)
    filter_upwards [hbound, hL.eventually_gt_atTop 0] with x hx hpos
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hpos]
    exact div_le_div_of_nonneg_right hx hpos.le
  have h := hzero.add_const 1
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [hL.eventually_gt_atTop 0] with x hx
  field_simp
  ring

theorem primeHarmonic_nonneg (x : ℝ) : 0 ≤ primeHarmonic x := by
  exact Finset.sum_nonneg (fun p _ => by positivity)

theorem primeHarmonic_mono : Monotone primeHarmonic := by
  intro x y hxy
  apply Finset.sum_le_sum_of_subset_of_nonneg (Nat.primesLE_mono (Nat.floor_mono hxy))
  intro p _ _
  positivity

end Erdos856b
