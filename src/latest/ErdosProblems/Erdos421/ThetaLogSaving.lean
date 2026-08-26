import ErdosProblems.Erdos421.ChebyshevLogSaving

/-! # Removing the prime powers from the quantitative prime number theorem -/

namespace Erdos421

open Filter Topology

theorem chebyshev_psi_theta_log_saving (A : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop, |Chebyshev.psi x - Chebyshev.theta x| ≤ ε * x / (Real.log x) ^ A := by
  have hhalf : 0 < ε / 2 := by positivity
  have hratio := (isLittleO_log_rpow_rpow_atTop (A + 1)
    (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  filter_upwards [hratio.eventually (gt_mem_nhds hhalf), eventually_ge_atTop (2 : ℝ)]
    with x hsmall hx
  have hxp : 0 < x := by linarith
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hp : 0 < (Real.log x) ^ A := Real.rpow_pos_of_pos hL A
  have hnum := (div_le_iff₀ (Real.rpow_pos_of_pos hxp (1 / 2 : ℝ))).mp hsmall.le
  rw [← Real.sqrt_eq_rpow, Real.rpow_add hL, Real.rpow_one] at hnum
  have hb : 2 * Real.sqrt x * Real.log x ≤ ε * x / (Real.log x) ^ A := by
    apply (le_div_iff₀ hp).mpr
    calc
      _ = (2 * Real.sqrt x) * ((Real.log x) ^ A * Real.log x) := by ring
      _ ≤ (2 * Real.sqrt x) * ((ε / 2) * Real.sqrt x) :=
        mul_le_mul_of_nonneg_left hnum (by positivity)
      _ = ε * (Real.sqrt x) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hxp.le]
  exact (Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (by linarith : 1 ≤ x)).trans hb

theorem chebyshev_theta_log_saving {A ε : ℝ} (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ X₀ > 1, ∀ x : ℝ, X₀ ≤ x → |Chebyshev.theta x - x| ≤ ε * x / (Real.log x) ^ A := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨X₁, _, hpsi⟩ := chebyshev_psi_log_saving hA hhalf
  have hlarge : ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x - x| ≤ ε * x / (Real.log x) ^ A := by
    filter_upwards [eventually_ge_atTop X₁, chebyshev_psi_theta_log_saving A hhalf] with x hx hdiff
    calc
      _ = |(Chebyshev.theta x - Chebyshev.psi x) + (Chebyshev.psi x - x)| := by congr 1; ring
      _ ≤ |Chebyshev.theta x - Chebyshev.psi x| + |Chebyshev.psi x - x| := abs_add_le _ _
      _ = |Chebyshev.psi x - Chebyshev.theta x| + |Chebyshev.psi x - x| := by rw [abs_sub_comm]
      _ ≤ ((ε / 2) * x / (Real.log x) ^ A) + ((ε / 2) * x / (Real.log x) ^ A) :=
        add_le_add hdiff (hpsi x hx)
      _ = _ := by ring
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hlarge
  refine ⟨max X₀ 2, lt_of_lt_of_le (by norm_num : (1 : ℝ) < 2) (le_max_right _ _), ?_⟩
  intro x hx
  exact hX₀ x ((le_max_left X₀ 2).trans hx)

end Erdos421
