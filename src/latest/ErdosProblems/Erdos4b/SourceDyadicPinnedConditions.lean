/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SourceDyadicArithmetic
import ErdosProblems.Erdos4b.GeneralFourierPinnedPrimeNormalization

/-!
# Pinned residual parameter conditions on the dyadic ray

The interval multiplier remains arbitrary. Residual primes may exceed
the auxiliary-prime frontier; their logarithms are bounded by twice
the ambient scale, not by the ambient scale itself.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped Topology

theorem sourcePreSieveCutoff_le_smoothFrontier (r : ℕ) :
    sourcePreSieveCutoff r ≤ smoothFrontier r := by
  have hrS : r ≤ smoothExponent r := Nat.le_mul_of_pos_right r (rankinDenominator_pos r)
  exact (Nat.div_le_self r 100).trans
    (hrS.trans (smoothExponent r).lt_two_pow_self.le)

theorem eventually_scaled_interval_le_primary_sq (a D : ℕ) :
    ∀ᶠ r in atTop, D * intervalLength a r ≤ primaryFrontier a r ^ 2 := by
  filter_upwards [eventually_scaled_cofactor_cutoff_le_primary a D] with r hr
  have hsmall : core r * r ≤ fullResidualCofactorCutoff r := by
    unfold fullResidualCofactorCutoff
    rw [mul_assoc]
    exact Nat.le_mul_of_pos_left _ (by positivity)
  have h := (Nat.mul_le_mul_left D hsmall).trans hr
  calc
    D * intervalLength a r = primaryFrontier a r * (D * (core r * r)) := by
      unfold intervalLength
      ring
    _ ≤ primaryFrontier a r * primaryFrontier a r := Nat.mul_le_mul_left _ h
    _ = primaryFrontier a r ^ 2 := (pow_two _).symm

theorem residual_pinned_log_lower {a r p₀ : ℕ}
    (hp : residualPrimeFrontier a r ≤ p₀) :
    dyadicAmbientScale a r / 2 ≤ Real.log p₀ := by
  have hp₀ : (0 : ℝ) < p₀ := by exact_mod_cast (residualPrimeFrontier_pos a r).trans_le hp
  apply (Real.le_log_iff_exp_le hp₀).mpr
  exact (exp_half_ambient_le_residualPrimeFrontier a r).trans (by exact_mod_cast hp)

theorem eventually_sourcePinnedNormalizationConditions_dyadic (K a D J : ℕ) (δ : ℝ) :
    ∀ᶠ r in atTop, ∀ m p₀ A B : ℕ,
      0 < m → m ≤ D * fullResidualCofactorCutoff r → p₀.Prime →
      residualPrimeFrontier a r ≤ p₀ → p₀ ≤ D * intervalLength a r / m →
      (m * p₀ - 1).Coprime (primorial (smoothFrontier r)) →
      primaryFrontier a r ≤ 2 * A → A ≤ B → B ≤ primaryFrontier a r →
      δ * (primaryFrontier a r : ℝ) / dyadicAmbientScale a r ^ J ≤ (B : ℝ) - A →
      SourcePinnedNormalizationConditions K (sourcePreSieveCutoff r) m p₀
        (smoothFrontier r) (primaryFrontier a r) A B J δ := by
  filter_upwards [eventually_ge_atTop 1, eventually_scaled_cofactor_cutoff_le_primary a D,
    eventually_scaled_interval_le_primary_sq a D, eventually_dyadicCompanionScale_small a 1,
    eventually_dyadicCompanionScale_small a K,
    eventually_dyadicCompanionScale_threeQuarter_lower a] with r hr hcof hU hLE hKLE hLlower
  intro m p₀ A B hm hmB hp₀ hp₀lo hp₀hi hcop hA hAB hB hlen
  have hV := one_le_dyadicAmbientScale a r
  have hLpos := dyadicCompanionScale_pos (by omega : 0 < r)
  have hplog := residual_pinned_log_lower hp₀lo
  simp only [Nat.cast_one, one_mul] at hLE
  have hYp : smoothFrontier r < p₀ := by
    apply_mod_cast (Real.log_lt_log_iff (by exact_mod_cast smoothFrontier_pos r)
      (by exact_mod_cast hp₀.pos)).mp (show Real.log (smoothFrontier r) < Real.log p₀ by
        change dyadicCompanionScale r < Real.log p₀
        linarith)
  have hpupper : p₀ ≤ primaryFrontier a r ^ 2 :=
    hp₀hi.trans ((Nat.div_le_self _ _).trans hU)
  have hplogupper : Real.log p₀ ≤ 2 * dyadicAmbientScale a r := by
    change Real.log p₀ ≤ 2 * Real.log (primaryFrontier a r)
    have hb := Real.log_le_log (by exact_mod_cast hp₀.pos)
      (show (p₀ : ℝ) ≤ (primaryFrontier a r : ℝ) ^ 2 by exact_mod_cast hpupper)
    simpa only [Real.log_pow, Nat.cast_ofNat] using hb
  refine ⟨hm, hp₀, sourcePreSieveCutoff_le_smoothFrontier r, hYp, hcop,
    sourcePreSieveCutoff_le_log_ambient_add_one a r,
    Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmB.trans hcof),
    hplogupper, hplog, hLpos, ?_, hKLE, hLlower, hA, hAB, hB, hlen⟩
  change dyadicCompanionScale r ≤ dyadicAmbientScale a r
  linarith

end

end Erdos4b.SmoothParameters
