/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceDyadicArithmetic

/-!
# Uniform verification of the source normalization parameters

All numerical Fourier and endpoint conditions hold on the saved dyadic
ray, uniformly over the full cofactor and auxiliary-prime ranges. The
fixed interval multiplier remains arbitrary.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped Topology

theorem eventually_sourceNormalizationConditions_dyadic (K a D : ℕ) :
    ∀ᶠ r in atTop, ∀ m q : ℕ,
      0 < m → Even m → m ≤ D * fullResidualCofactorCutoff r → q.Prime →
      primaryFrontier a r ≤ 2 * q → q ≤ primaryFrontier a r →
      SourceNormalizationConditions K (sourcePreSieveCutoff r) m q
        (D * intervalLength a r / m) (dyadicAmbientScale a r) (dyadicCompanionScale r) := by
  filter_upwards [eventually_ge_atTop 1, eventually_scaled_cofactor_cutoff_le_primary a D,
    eventually_dyadicCompanionScale_small a 1, eventually_dyadicCompanionScale_small a K,
    eventually_sourcePreSieve_primorial_le_exp_ambient a,
    eventually_dyadicCompanionScale_threeQuarter_lower a] with r hr hcof hLE hKLE hP hLlower
  intro m q hm heven hmB hq hlo hhi
  have hqlog := source_auxiliary_log_bounds hq.pos hlo hhi
  have hmX := hmB.trans hcof
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hV := one_le_dyadicAmbientScale a r
  have hLEupper : dyadicCompanionScale r ≤ dyadicAmbientScale a r := by
    simp only [Nat.cast_one, one_mul] at hLE
    linarith
  refine ⟨hm, heven, hq, hqlog.2.2,
    Real.log_le_log hmR (by exact_mod_cast hmX), hqlog.1, hqlog.2.1,
    dyadicCompanionScale_pos (by omega), hLEupper, hKLE, hP, ?_,
    sourcePreSieveCutoff_le_log_ambient_add_one a r, hLlower⟩
  exact (exp_half_ambient_le_residualPrimeFrontier a r).trans
    (by exact_mod_cast residualPrimeFrontier_le_scaled_interval_div hm hmB)

end

end Erdos4b.SmoothParameters
