import BoundedGaps.PrimeNumberTheorem.Analytic.StrongChebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Two complementary bounds for the principal Chebyshev error

The ordinary prime number theorem gives arbitrary logarithmic savings.
The explicit formula gives a second bound which can exploit repulsion of
zeta zeros by an exceptional Dirichlet zero.
-/

namespace Linnik

open Filter Complex BoundedGaps.Maynard BoundedGaps.PrimeNumberTheorem
open scoped Topology

theorem eventually_abs_psi_sub_mul_log_sq_le
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ x : ℕ in atTop,
      |Chebyshev.psi (x : ℝ) - (x : ℝ)| * Real.log (x : ℝ) ^ 2 ≤ epsilon * x := by
  obtain ⟨C, c, hC, hc, X₀, hX₀, hpsi⟩ :=
    exists_abs_chebyshevPsi_sub_natCast_le_exp_neg_sqrtLog
  have hu : Tendsto (fun x : ℕ ↦ Real.sqrt (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlim := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (4 : ℝ) c hc).comp hu
  have hlim' : Tendsto (fun x : ℕ ↦ C * (Real.log (x : ℝ) ^ 2 *
      Real.exp (-c * Real.sqrt (Real.log (x : ℝ))))) atTop (nhds 0) := by
    have h := hlim.const_mul C
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop 1] with x hx
    have hlog : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast hx)
    simp only [Function.comp_apply, Real.rpow_ofNat]
    rw [show Real.sqrt (Real.log (x : ℝ)) ^ 4 = Real.log (x : ℝ) ^ 2 by
      rw [show 4 = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hlog]]
  have hsmall := hlim'.eventually (gt_mem_nhds hepsilon)
  filter_upwards [hsmall, eventually_ge_atTop X₀] with x hsmall hx
  have h := mul_le_mul_of_nonneg_right (hpsi x hx) (sq_nonneg (Real.log (x : ℝ)))
  calc
    |Chebyshev.psi (x : ℝ) - (x : ℝ)| * Real.log (x : ℝ) ^ 2 ≤
        (x : ℝ) * (C * (Real.log (x : ℝ) ^ 2 *
          Real.exp (-c * Real.sqrt (Real.log (x : ℝ))))) := by nlinarith [h]
    _ ≤ (x : ℝ) * epsilon := mul_le_mul_of_nonneg_left hsmall.le (Nat.cast_nonneg x)
    _ = epsilon * x := by ring

theorem exists_nat_abs_psi_sub_le_error_add_zetaKernel :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ T : ℝ, 2 ≤ T →
      ∀ x : ℕ, 4 ≤ x → T ≤ (x : ℝ) →
        |Chebyshev.psi (x : ℝ) - (x : ℝ)| ≤
          (K : ℝ) * ((x : ℝ) * Real.log (x : ℝ) ^ 2 / T) +
            ‖dirichletNontrivialZeroKernelSum (1 : DirichletCharacter ℂ 1) (x : ℝ) T‖ := by
  obtain ⟨K, hK, hformula⟩ :=
    exists_nat_norm_twistedChebyshevSum_sub_dirichletExplicitFormulaMainZeroTerms_le
  refine ⟨K, hK, ?_⟩
  intro T hT x hx hTx
  have h := hformula 1 1 T hT x hx hTx
  rw [twistedChebyshevSum_one_eq_psi, dirichletExplicitFormulaMainZeroTerms,
    if_pos rfl, dirichletExplicitFormulaErrorScale] at h
  norm_num only [Nat.cast_one, mul_one] at h
  let Z := dirichletNontrivialZeroKernelSum (1 : DirichletCharacter ℂ 1) (x : ℝ) T
  calc
    |Chebyshev.psi (x : ℝ) - (x : ℝ)| =
        ‖(Chebyshev.psi (x : ℝ) : ℂ) - (x : ℂ)‖ := by
      rw [← Complex.ofReal_natCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    _ = ‖((Chebyshev.psi (x : ℝ) : ℂ) - ((x : ℂ) - Z)) - Z‖ := by congr 1; ring
    _ ≤ ‖(Chebyshev.psi (x : ℝ) : ℂ) - ((x : ℂ) - Z)‖ + ‖Z‖ := norm_sub_le _ _
    _ ≤ _ := add_le_add h le_rfl

end Linnik
