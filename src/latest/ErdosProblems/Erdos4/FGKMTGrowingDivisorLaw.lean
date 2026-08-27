import ErdosProblems.Erdos4.FGKMTGrowingRadius
import ErdosProblems.Erdos4.FGKMTHarmonicErrorBudget

/-!
# Unconditional concentration for the concrete growing divisor family

The dimension, lower prime cutoff, and radius are explicit functions of
every sufficiently large natural endpoint. The estimate is uniform in
the prime selected by the excised distribution theorem.
-/

open scoped BigOperators

namespace Erdos4.FGKMT

open Filter

theorem eventually_growing_divisor_probability :
    ∀ᶠ x : ℕ in atTop, ∃ hR : 1 ≤ growingRadius x,
      ∀ a : ℝ, a ≤ 1 / 4 → ∀ B : ℕ,
        (B = 1 ∨ B.Prime) → B ≤ exponentialConductorCutoff a x →
        (1 / 2 : ℝ) ≤
          (FiniteLaw.independent (fun _ : Fin (sieveDimension (growingIndex x)) =>
            rationalSquareLaw (harmonicModulus (growingPrecutoff x) B)
              (sieveSlope (growingIndex x) (growingRadius x)) (growingRadius x) hR)).prob
            (fun v => (∑ i, Real.log (v i : ℕ)) ≤ Real.log (growingRadius x : ℝ) / 2 ∧
              Pairwise (fun i j => (v i : ℕ).Coprime (v j : ℕ))) := by
  have hlogTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_sieve_harmonic_error, eventually_growingRadius_bounds,
    eventually_growingPrecutoff_bounds, eventually_growingDimension_bounds,
    growingIndex_tendsto.eventually (eventually_ge_atTop 16),
    hlogTop.eventually (eventually_ge_atTop 1)] with x herror hR hD hk hj hlog
  have hR1 : 1 ≤ growingRadius x := by omega
  refine ⟨hR1, ?_⟩
  intro a ha B hB hBx
  have hkupper : (sieveDimension (growingIndex x) : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 16 : ℝ) :=
    hk.2.trans (Real.rpow_le_rpow_of_exponent_le hlog (by norm_num))
  have he := herror (growingIndex x) (growingRadius x) (growingPrecutoff x) B a
    hj hR.1 hD.1 ha hkupper hD.2.2 hR.2 hB hBx
  have hcollision : 4 * sieveDimension (growingIndex x) ^ 2 ≤ growingPrecutoff x - 1 := by
    have hsmall : 4 * sieveDimension (growingIndex x) ^ 2 ≤
        4 * (sieveDimension (growingIndex x) + 1) ^ 2 :=
      Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (Nat.le_succ _) 2)
    exact hsmall.trans hD.2.1
  exact sieveDivisorLaw_good_probability hj hR.1 hD.1 hB hcollision he

end Erdos4.FGKMT
