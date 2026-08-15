import ErdosProblems.Erdos321.UniformKernel

namespace Erdos321

open Filter Asymptotics
open scoped Topology

/-- The class-independent kernel error tends to zero. -/
theorem tendsto_uniformKernelError (C : ℝ) :
    Tendsto (uniformKernelError C) atTop (𝓝 0) := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hlog2 : Tendsto (fun x : ℝ => Real.log x ^ 2 / x) atTop (𝓝 0) :=
    Real.isLittleO_pow_log_id_atTop.tendsto_div_nhds_zero
  have hlog1 : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hfirstR : Tendsto
      (fun x : ℝ => Real.log x * (Real.log x + 1) / x) atTop (𝓝 0) := by
    convert hlog2.add hlog1 using 1
    · funext x
      ring
    · ring
  have hLtop : Tendsto (fun x : ℝ => Real.log x) atTop atTop :=
    Real.tendsto_log_atTop
  have hinvL : Tendsto (fun x : ℝ => (Real.log x)⁻¹) atTop (𝓝 0) :=
    hLtop.inv_tendsto_atTop
  have hsecondR : Tendsto (fun x : ℝ => 16 * C / Real.log x) atTop (𝓝 0) := by
    convert (hinvL.const_mul (16 * C)) using 1
    · funext x
      simp [div_eq_mul_inv]
    · ring
  have hratio : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hratioComp : Tendsto
      (fun x : ℝ => Real.log (Real.log x) / Real.log x) atTop (𝓝 0) := by
    exact hratio.comp hLtop
  have hconstComp : Tendsto
      (fun x : ℝ => Real.log 4 / Real.log x) atTop (𝓝 0) := by
    convert (hinvL.const_mul (Real.log 4)) using 1
    · funext x
      simp [div_eq_mul_inv]
    · ring
  have hthirdR : Tendsto
      (fun x : ℝ => Real.log (4 * Real.log x) / Real.log x) atTop (𝓝 0) := by
    have hsum : Tendsto
        (fun x : ℝ => Real.log 4 / Real.log x +
          Real.log (Real.log x) / Real.log x) atTop (𝓝 0) := by
      simpa using hconstComp.add hratioComp
    apply Tendsto.congr' _ hsum
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_gt_atTop 0)] with x hx
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (ne_of_gt hx)]
    ring
  have hreal : Tendsto
      (fun x : ℝ => Real.log x * (Real.log x + 1) / x +
        16 * C / Real.log x +
        Real.log (4 * Real.log x) / Real.log x) atTop (𝓝 0) := by
    simpa using (hfirstR.add hsecondR).add hthirdR
  have hnat := hreal.comp hcast
  change Tendsto
    (fun n : ℕ => Real.log (n : ℝ) * (Real.log (n : ℝ) + 1) / n +
      16 * C / Real.log (n : ℝ) +
      Real.log (4 * Real.log (n : ℝ)) / Real.log (n : ℝ)) atTop (𝓝 0)
  exact hnat

/-- In particular the `1/4` small-error hypothesis is eventually automatic. -/
theorem eventually_uniformKernelError_le_quarter (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, uniformKernelError C N ≤ 1 / 4 := by
  have h := (tendsto_uniformKernelError C).eventually
    (Iic_mem_nhds (show (0 : ℝ) < 1 / 4 by norm_num))
  simpa using h

end Erdos321
