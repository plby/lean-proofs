import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsPowerCoefficients
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsPowerFactor
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsPowerInvariant
import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsPowerPole

/-!
# Cyclic descent of analytic functions and differential coefficients

These are the scalar statements of Lemma 9.17.  The only inputs are
analyticity at the fixed point and the actual root-of-unity covariance.
Taylor-series uniqueness forces the coefficient support, the initial
monomial is removed analytically, and the invariant factor is reconstructed
as a convergent power series in `t = s ^ m`.

For a one-form the descended coefficient is analytic.  For a cubic
differential at elliptic order `m ≥ 3`, its coefficient is meromorphic with
order at least `-2`.  The actual elliptic orders `3` and `4` are both covered.
-/

noncomputable section

open Filter
open scoped Topology

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

/-- Weighted scalar cyclic descent, with the normalization by the derivative
of the power map.  For `k = 1` this is the coefficient of a holomorphic
one-form; for `k = 3` the numerator regularizes a pole of order at most two. -/
theorem analyticAt_weighted_power_descent {m k : ℕ} {ζ : ℂ} {F : ℂ → ℂ}
    (hm : 0 < m) (hk : 0 < k) (hkm : k ≤ m)
    (hζ : IsPrimitiveRoot ζ m) (hF : AnalyticAt ℂ F 0)
    (hcov : ∀ᶠ s in 𝓝 (0 : ℂ), F (ζ * s) * ζ ^ k = F s) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℂ), F s = (m : ℂ) ^ k * s ^ (m - k) * H (s ^ m) := by
  obtain ⟨p, hp⟩ := hF
  have hzero : ∀ n < m - k, p n (fun _ => 1) = 0 := by
    intro n hn
    exact powerSeries_coefficient_eq_zero_of_lt_sub hζ hp hcov hk hkm hn
  have hperiod : ζ ^ (m - k + k) = 1 := by
    rw [Nat.sub_add_cancel hkm]
    exact hζ.pow_eq_one
  obtain ⟨A, hA, hfactor, hAcov⟩ :=
    analyticAt_invariant_pow_factor_of_coeff_zero hp hzero hperiod hcov
  obtain ⟨H, hH, hH_eq⟩ := analyticAt_factor_through_pow hm hζ hA hAcov
  have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  refine ⟨fun t => H t / (m : ℂ) ^ k,
    hH.div analyticAt_const (pow_ne_zero k hmC), ?_⟩
  filter_upwards [hH_eq] with s hs
  rw [hfactor s, hs]
  field_simp [hmC]

/-- An invariant holomorphic one-form descends holomorphically through the
power map: `F(s) ds = H(s^m) d(s^m)`. -/
theorem analyticAt_oneForm_power_descent {m : ℕ} {ζ : ℂ} {F : ℂ → ℂ}
    (hm : 0 < m) (hζ : IsPrimitiveRoot ζ m) (hF : AnalyticAt ℂ F 0)
    (hcov : ∀ᶠ s in 𝓝 (0 : ℂ), F (ζ * s) * ζ = F s) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℂ), F s = (m : ℂ) * s ^ (m - 1) * H (s ^ m) := by
  have hcov' : ∀ᶠ s in 𝓝 (0 : ℂ), F (ζ * s) * ζ ^ 1 = F s := by
    simpa only [pow_one] using hcov
  simpa only [pow_one] using
    analyticAt_weighted_power_descent hm (by decide : 0 < 1) (by omega) hζ hF hcov'

/-- The analytic numerator of the descended cubic coefficient.  Dividing
`H(t)` by `t^2` gives the literal meromorphic coefficient on the base. -/
theorem analyticAt_cubic_power_descent {m : ℕ} {ζ : ℂ} {F : ℂ → ℂ}
    (hm : 3 ≤ m) (hζ : IsPrimitiveRoot ζ m) (hF : AnalyticAt ℂ F 0)
    (hcov : ∀ᶠ s in 𝓝 (0 : ℂ), F (ζ * s) * ζ ^ 3 = F s) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧
      ∀ᶠ s in 𝓝 (0 : ℂ), F s = (m : ℂ) ^ 3 * s ^ (m - 3) * H (s ^ m) :=
  analyticAt_weighted_power_descent (by omega) (by decide : 0 < 3) hm hζ hF hcov

/-- An invariant holomorphic cubic differential descends to an actual
meromorphic coefficient of order at least `-2`, with its literal scalar
pullback along `s ↦ s^m`.  No descended coefficient is assumed as input. -/
theorem meromorphicAt_cubic_power_descent {m : ℕ} {ζ : ℂ} {F : ℂ → ℂ}
    (hm : 3 ≤ m) (hζ : IsPrimitiveRoot ζ m) (hF : AnalyticAt ℂ F 0)
    (hcov : ∀ᶠ s in 𝓝 (0 : ℂ), F (ζ * s) * ζ ^ 3 = F s) :
    ∃ K : ℂ → ℂ, MeromorphicAt K 0 ∧
      (-2 : WithTop ℤ) ≤ meromorphicOrderAt K 0 ∧
      ∀ᶠ s in 𝓝[≠] (0 : ℂ),
        F s = ((m : ℂ) * s ^ (m - 1)) ^ 3 * K (s ^ m) := by
  obtain ⟨H, hH, hformula⟩ := analyticAt_cubic_power_descent hm hζ hF hcov
  refine ⟨fun t => H t / t ^ 2, meromorphicAt_div_coordinate_pow hH 2,
    meromorphicOrderAt_div_coordinate_pow_ge hH 2, ?_⟩
  filter_upwards [hformula.filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s hs hs0
  have hsne : s ≠ 0 := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hs0
  exact hs.trans (cubic_power_pullback_identity m hm s (H (s ^ m)) hsne)

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
