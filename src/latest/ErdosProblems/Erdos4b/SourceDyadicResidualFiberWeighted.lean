/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.ResidualPrimeFiberWeightedError
import ErdosProblems.Erdos4b.SourceDyadicArithmetic
import ErdosProblems.Erdos4b.GeneralFourierPinnedUnconditionalDistribution

/-!
# Uniform dyadic residual-fibre proxy bound

The constant is independent of the interval multiplier, cofactor and
dyadic ray. Only the eventual threshold depends on the fixed parameters.
The cofactor correction is kept exactly for allocation and cancellation.
-/

namespace Erdos4b.SmoothParameters

noncomputable section

open Filter
open scoped Topology

theorem eventually_dyadicSmoothPower_le_twoFifthsResidualCutoff (a S : ℕ) :
    ∀ᶠ r in atTop, smoothFrontier r ^ S ≤
      BoundedGaps.Maynard.modulusCutoff (2 / 5) (residualPrimeFrontier a r) := by
  filter_upwards [eventually_dyadicCompanionScale_small a S] with r hsmall
  have hzpos : (0 : ℝ) < residualPrimeFrontier a r :=
    by exact_mod_cast residualPrimeFrontier_pos a r
  have hypos : (0 : ℝ) < smoothFrontier r ^ S :=
    by exact_mod_cast pow_pos (smoothFrontier_pos r) S
  have hV := one_le_dyadicAmbientScale a r
  have hzlog : dyadicAmbientScale a r / 2 ≤ Real.log (residualPrimeFrontier a r) :=
    (Real.le_log_iff_exp_le hzpos).mpr (exp_half_ambient_le_residualPrimeFrontier a r)
  apply (Nat.le_floor_iff (Real.rpow_nonneg hzpos.le (2 / 5))).mpr
  rw [Real.rpow_def_of_pos hzpos, Nat.cast_pow]
  apply (Real.log_le_iff_le_exp hypos).mp
  rw [Real.log_pow]
  change (S : ℝ) * dyadicCompanionScale r ≤ _
  linarith

theorem eventually_residualPrimeFrontier_ge (a N : ℕ) :
    ∀ᶠ r in atTop, N ≤ residualPrimeFrontier a r := by
  have hV := (tendsto_dyadicAmbientScale_atTop a).eventually_ge_atTop
    (2 * Real.log (N + 1 : ℕ))
  filter_upwards [hV] with r hr
  have hN : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hn : ((N + 1 : ℕ) : ℝ) ≤ residualPrimeFrontier a r := by
    calc
      _ = Real.exp (Real.log (N + 1 : ℕ)) := (Real.exp_log hN).symm
      _ ≤ Real.exp (dyadicAmbientScale a r / 2) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ _ := exp_half_ambient_le_residualPrimeFrontier a r
  exact (Nat.le_succ N).trans (by exact_mod_cast hn)

theorem exists_uniform_dyadicResidualPrimeFiber_weighted_endpoint_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ a : ℕ, ∀ᶠ r in atTop, ∀ U m : ℕ,
      0 < m → Even m → residualPrimeFrontier a r ≤ U / m →
      residualCofactorLocalProduct (smoothFrontier r) m *
          (residualPrimeFiber U (smoothFrontier r)
            (residualPrimeFrontier a r) m).card ≤
        C * (U / m : ℕ) /
          (dyadicAmbientScale a r * dyadicCompanionScale r) := by
  obtain ⟨Aβ, Cπ, CV, hAβ, hCπ, hCV, hbound⟩ :=
    exists_residualPrimeFiber_cofactor_weighted_upper_bound
  obtain ⟨s, hs⟩ := exists_nat_gt (99 * Real.log Aβ / 2)
  let S := s + 101
  have hS : 101 ≤ S := by dsimp only [S]; omega
  have hlogA : Real.log Aβ ≤ 2 * (S - 100 : ℕ) / 99 := by
    rw [show S - 100 = s + 1 by dsimp only [S]; omega, Nat.cast_add, Nat.cast_one]
    linarith
  let eta : ℝ := (4 * Aβ / 3) * (1 / 4 : ℝ) ^ (S - 100)
  have heta : 0 ≤ eta := by dsimp only [eta]; positivity
  let C₀ := Cπ * (1 + eta) * CV
  have hC₀ : 0 < C₀ := by dsimp only [C₀]; positivity
  obtain ⟨CBV, X₀, hw⟩ := exists_pinnedTwoFifthsPrimeLevelWitness (by norm_num : (0 : ℝ) < 3)
  refine ⟨2 * C₀ + 1, by positivity, ?_⟩
  intro a
  filter_upwards [eventually_ge_atTop 1,
    eventually_dyadicSmoothPower_le_twoFifthsResidualCutoff a S,
    eventually_residualPrimeFrontier_ge a X₀,
    (tendsto_dyadicAmbientScale_atTop a).eventually_ge_atTop (16 * CBV),
    eventually_dyadicCompanionScale_small a 1] with r hr hlevel hxz hlarge hLsmall
  intro U m hm heven hzT
  let T := U / m
  have hT : 2 ≤ T := (residualPrimeFrontier_one_lt a r).trans_le hzT
  have hY : 1 < smoothFrontier r := by
    unfold smoothFrontier
    apply one_lt_pow₀ (by norm_num)
    unfold smoothExponent
    exact (Nat.mul_pos (by omega : 0 < r) (rankinDenominator_pos r)).ne'
  have hV : 0 < dyadicAmbientScale a r := lt_of_lt_of_le (by norm_num)
    (one_le_dyadicAmbientScale a r)
  have hL : 0 < dyadicCompanionScale r := dyadicCompanionScale_pos (by omega)
  have hLV : dyadicCompanionScale r ≤ dyadicAmbientScale a r := by
    simp only [Nat.cast_one, one_mul] at hLsmall
    linarith
  have hzlog : dyadicAmbientScale a r / 2 ≤ Real.log (residualPrimeFrontier a r) :=
    (Real.le_log_iff_exp_le (by exact_mod_cast residualPrimeFrontier_pos a r)).mpr
      (exp_half_ambient_le_residualPrimeFrontier a r)
  have hTlog : dyadicAmbientScale a r / 2 ≤ Real.log T := hzlog.trans
    (Real.log_le_log (by exact_mod_cast residualPrimeFrontier_pos a r) (by exact_mod_cast hzT))
  have hfinite := hbound hm heven hzT hY hS hlogA hw (hxz.trans hzT) hxz
    (hlevel.trans (BoundedGaps.Maynard.modulusCutoff_mono (by norm_num) hzT)) hlevel hT
  have hmain := residualWeightedMainTerm_le hC₀.le hV hL hTlog
  have herr := residualEndpointErrors_three_le hw.1 hV hL hLV hlarge hzT hTlog hzlog
  change residualCofactorLocalProduct (smoothFrontier r) m *
      (residualPrimeFiber U (smoothFrontier r)
        (residualPrimeFrontier a r) m).card ≤
    C₀ * T / (Real.log T * dyadicCompanionScale r) +
      CBV * T / Real.rpow (Real.log T) 3 +
      CBV * (residualPrimeFrontier a r) / Real.rpow (Real.log (residualPrimeFrontier a r)) 3
    at hfinite
  calc
    _ ≤ C₀ * T / (Real.log T * dyadicCompanionScale r) +
        (CBV * T / Real.rpow (Real.log T) 3 +
          CBV * (residualPrimeFrontier a r) /
            Real.rpow (Real.log (residualPrimeFrontier a r)) 3) := by
      simpa only [add_assoc] using hfinite
    _ ≤ 2 * C₀ * T / (dyadicAmbientScale a r * dyadicCompanionScale r) +
        (T : ℝ) / (dyadicAmbientScale a r * dyadicCompanionScale r) := add_le_add hmain herr
    _ = _ := by ring

theorem exists_uniform_dyadicResidualPrimeFiber_cofactor_weighted_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ a D : ℕ, ∀ᶠ r in atTop, ∀ m : ℕ,
      0 < m → Even m → m ≤ D * fullResidualCofactorCutoff r →
      residualCofactorLocalProduct (smoothFrontier r) m *
          (residualPrimeFiber (D * intervalLength a r) (smoothFrontier r)
            (residualPrimeFrontier a r) m).card ≤
        C * (D * intervalLength a r / m : ℕ) /
          (dyadicAmbientScale a r * dyadicCompanionScale r) := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_dyadicResidualPrimeFiber_weighted_endpoint_bound
  refine ⟨C, hC, ?_⟩
  intro a D
  filter_upwards [hbound a] with r hr
  intro m hm heven hmB
  exact hr (D * intervalLength a r) m hm heven (residualPrimeFrontier_le_scaled_interval_div hm hmB)

end

end Erdos4b.SmoothParameters
