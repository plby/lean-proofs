import ErdosProblems.Erdos4.SelbergOptimization
import BoundedGaps.Maynard.WirsingFixedModulusNormalization

/-!
# Logarithmic size of the Selberg harmonic mass

The reciprocal-totient asymptotic imported here is an existing proved
theorem. The normalization is identified with the concrete finite sum,
and the bound used by the prime mean-square argument is derived below.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos4.SelbergHarmonicMass

open SelbergCoefficients SieveMajorant SelbergOptimization

theorem harmonicMass_eq_squarefreeMean (D : ℕ) :
    harmonicMass D = BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean 1 D := by
  classical
  unfold harmonicMass BoundedGaps.Maynard.squarefreeCoprimeInvTotientMean
  apply Finset.sum_congr rfl
  intro r _hr
  by_cases hs : Squarefree r
  · have hm : mu r ^ 2 = 1 := by
      unfold mu
      exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hs
    simp [hs, hm]
  · have hm : mu r = 0 := by
      simp only [mu, ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs, Int.cast_zero]
    simp only [hs, false_and, ↓reduceIte, hm, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_div]

theorem harmonicMass_div_log_tendsto_one :
    Tendsto (fun D : ℕ => harmonicMass D / Real.log D) atTop (nhds 1) := by
  have h := BoundedGaps.Maynard.tendsto_squarefreeCoprimeInvTotientMean_div_log
    (W := 1) (by norm_num) (by simp)
  simpa only [← harmonicMass_eq_squarefreeMean, BoundedGaps.Maynard.coprimeHarmonicDensity,
    Nat.totient_one, Nat.cast_one, div_self one_ne_zero] using h

theorem eventually_log_div_two_le_harmonicMass :
    ∀ᶠ D : ℕ in atTop, 2 ≤ D ∧ Real.log D / 2 ≤ harmonicMass D := by
  have hratio : ∀ᶠ D : ℕ in atTop, (1 : ℝ) / 2 < harmonicMass D / Real.log D :=
    (tendsto_order.mp harmonicMass_div_log_tendsto_one).1 (1 / 2) (by norm_num)
  filter_upwards [hratio, eventually_ge_atTop 2] with D hD htwo
  have hlog : 0 < Real.log (D : ℝ) := Real.log_pos (by exact_mod_cast htwo)
  have hh := (lt_div_iff₀ hlog).mp hD
  exact ⟨htwo, by linarith⟩

/-- The elementary majorant has the `N / log D` mass required for the
prime-supported mean-square estimate. -/
theorem eventually_sum_weight_le :
    ∀ᶠ D : ℕ in atTop, ∀ N : ℕ,
      (∑ n ∈ Finset.Icc 1 N, weight D (coefficient D) n) ≤
        2 * (N : ℝ) / Real.log D + (D : ℝ) ^ 4 := by
  filter_upwards [eventually_log_div_two_le_harmonicMass] with D hD N
  have hlog : 0 < Real.log (D : ℝ) := Real.log_pos (by exact_mod_cast hD.1)
  have hrecip : (N : ℝ) / harmonicMass D ≤ 2 * (N : ℝ) / Real.log D := by
    calc
      (N : ℝ) / harmonicMass D ≤ (N : ℝ) / (Real.log D / 2) :=
        div_le_div_of_nonneg_left (Nat.cast_nonneg N) (by positivity) hD.2
      _ = 2 * (N : ℝ) / Real.log D := by ring
  exact (sum_weight_coefficient_le (by omega) N).trans (add_le_add hrecip le_rfl)

end Erdos4.SelbergHarmonicMass
