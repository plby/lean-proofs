/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Analysis.SpecialFunctions.CompareExp

/-!
# The endpoint in BNPZ Theorem 1.4

This file verifies the elementary asymptotic step converting the quantitative
endpoint `241 * log (log k) / log k` into an arbitrary positive constant.
-/

namespace Erdos387

/-- The coefficient of `n` in the forbidden interval of BNPZ Theorem 1.4. -/
noncomputable def BNPZEndpoint (k : ℕ) : ℝ :=
  241 * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ))

/-- The BNPZ endpoint tends to zero. -/
theorem tendsto_BNPZEndpoint :
    Filter.Tendsto BNPZEndpoint Filter.atTop (nhds 0) := by
  have hreal : Filter.Tendsto
      (fun x : ℝ => Real.log (Real.log x) / Real.log x)
      Filter.atTop (nhds 0) := by
    have ho := Real.isLittleO_log_id_atTop.comp_tendsto Real.tendsto_log_atTop
    simpa only [Function.comp_apply, id_eq] using ho.tendsto_div_nhds_zero
  have hnat := hreal.comp tendsto_natCast_atTop_atTop
  change Filter.Tendsto
    (fun k : ℕ => 241 * (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ)))
    Filter.atTop (nhds 0)
  simpa only [Function.comp_apply, mul_zero] using hnat.const_mul 241

/-- Hence the endpoint is eventually below any prescribed positive real
number. -/
theorem eventually_BNPZEndpoint_lt {c : ℝ} (hc : 0 < c) :
    ∀ᶠ k : ℕ in Filter.atTop, BNPZEndpoint k < c := by
  exact tendsto_BNPZEndpoint.eventually (Iio_mem_nhds hc)

end Erdos387
