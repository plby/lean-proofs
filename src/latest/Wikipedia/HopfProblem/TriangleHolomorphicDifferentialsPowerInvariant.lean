import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsPowerCoefficients
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsPowerInvariantSeries

/-!
# Analytic scalar descent through a cyclic power map

For a primitive `m`-th root of unity, an invariant holomorphic germ is an
actual holomorphic germ in `s ^ m`.  This is the scalar descent assertion
of Lemma 9.17 (D0), proved from Taylor coefficients and a convergent
power subseries.
-/

noncomputable section

open Filter
open scoped Topology

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

/-- A scalar analytic germ invariant under a primitive finite rotation
descends analytically through the power map. -/
theorem analyticAt_factor_through_pow {F : ℂ → ℂ} {ζ : ℂ} {m : ℕ}
    (hm : 0 < m) (hζ : IsPrimitiveRoot ζ m) (hF : AnalyticAt ℂ F 0)
    (hcov : ∀ᶠ s in 𝓝 0, F (ζ * s) = F s) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ F =ᶠ[𝓝 0] (fun s => H (s ^ m)) := by
  obtain ⟨p, hp⟩ := hF
  apply analyticAt_factor_through_pow_of_coeff_support hm hp
  intro n hn
  apply powerSeries_coefficient_eq_zero_of_not_dvd (k := 0) hζ hp
  · simpa only [pow_zero, mul_one] using hcov
  · simpa only [Nat.add_zero] using hn

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
