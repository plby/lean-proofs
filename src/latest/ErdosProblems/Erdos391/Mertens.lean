import UnitFractions.ForMathlib.BasicEstimates

open Filter Real
open scoped BigOperators Topology

namespace Erdos391.Mertens

noncomputable def M : ℝ := meissel_mertens

noncomputable def E₂p (x : ℝ) : ℝ :=
  prime_summatory (fun p : ℕ ↦ (p : ℝ)⁻¹) 1 x -
    (Real.log (Real.log x) + M)

theorem sum_prime_div_eq (x : ℝ) :
    (∑ p ∈ Finset.Ioc 0 ⌊x⌋₊ with p.Prime, (1 : ℝ) / p) =
      Real.log (Real.log x) + M + E₂p x := by
  rw [E₂p]
  have hsets : (Finset.Ioc 0 ⌊x⌋₊).filter Nat.Prime =
      (Finset.Icc 1 ⌊x⌋₊).filter Nat.Prime := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hp, hpx⟩, hprime⟩
      exact ⟨⟨hp, hpx⟩, hprime⟩
    · rintro ⟨⟨hp, hpx⟩, hprime⟩
      exact ⟨⟨hp, hpx⟩, hprime⟩
  rw [prime_summatory, ← hsets]
  simp only [one_div]
  ring

theorem eventually_abs_E₂p_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ x : ℝ in atTop,
      |E₂p x| ≤ C / Real.log x := by
  obtain ⟨C, hC⟩ := prime_reciprocal.bound
  refine ⟨|C|, abs_nonneg C, ?_⟩
  filter_upwards [hC, eventually_gt_atTop (1 : ℝ)] with x hx hlarge
  have hlog : 0 < Real.log x := Real.log_pos hlarge
  change |prime_summatory (fun p : ℕ ↦ (p : ℝ)⁻¹) 1 x -
    (Real.log (Real.log x) + meissel_mertens)| ≤ |C| / Real.log x
  rw [Real.norm_eq_abs] at hx
  have hinv : ‖(Real.log x)⁻¹‖ = (Real.log x)⁻¹ :=
    norm_of_nonneg (inv_nonneg.mpr hlog.le)
  rw [hinv] at hx
  exact hx.trans (by
    rw [div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_right (le_abs_self C) (inv_nonneg.mpr hlog.le))

end Erdos391.Mertens
