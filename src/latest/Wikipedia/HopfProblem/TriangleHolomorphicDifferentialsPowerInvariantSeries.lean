import Mathlib.Analysis.Analytic.Basic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Complex.Basic

/-!
# Convergent power subseries

An analytic germ whose Taylor coefficients are supported on multiples of
`m > 0` is an analytic function of the power `s ^ m`.  The descended germ
is the actual convergent series obtained by keeping those coefficients.
-/

noncomputable section

open Filter Set
open scoped Topology NNReal ENNReal

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentials

/-- The scalar power series with coefficients at the multiples of `m`. -/
def powerSubseries (p : FormalMultilinearSeries ℂ ℂ ℂ) (m : ℕ) :
    FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ (fun n => p (m * n) (fun _ => 1))

@[simp] theorem powerSubseries_coeff (p : FormalMultilinearSeries ℂ ℂ ℂ) (m n : ℕ) :
    (powerSubseries p m).coeff n = p.coeff (m * n) :=
  FormalMultilinearSeries.coeff_ofScalars

/-- A positive convergence radius remains positive after keeping every
`m`-th coefficient and removing the gaps between their exponents. -/
theorem powerSubseries_radius_pos {p : FormalMultilinearSeries ℂ ℂ ℂ} {m : ℕ}
    (hp : 0 < p.radius) : 0 < (powerSubseries p m).radius := by
  obtain ⟨r, hr0, hrp⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp
  obtain ⟨C, _, hC⟩ := p.norm_mul_pow_le_of_lt_radius hrp
  have hr : (0 : ℝ≥0) < r := ENNReal.coe_pos.mp hr0
  have hbound : ((r ^ m : ℝ≥0) : ℝ≥0∞) ≤ (powerSubseries p m).radius := by
    apply FormalMultilinearSeries.le_radius_of_bound _ C
    intro n
    simpa only [FormalMultilinearSeries.norm_apply_eq_norm_coef, powerSubseries_coeff,
      NNReal.coe_pow, ← pow_mul] using hC (m * n)
  exact lt_of_lt_of_le (ENNReal.coe_pos.mpr (pow_pos hr m)) hbound

/-- If the omitted coefficients vanish, reindexing the original sum
gives the sum of the power subseries at `s ^ m`. -/
theorem hasSum_powerSubseries_pow {p : FormalMultilinearSeries ℂ ℂ ℂ}
    {m : ℕ} (hm : 0 < m)
    (hsupport : ∀ n, ¬m ∣ n → p n (fun _ => 1) = 0)
    {s a : ℂ} (hs : HasSum (fun n => p n (fun _ => s)) a) :
    HasSum (fun n => powerSubseries p m n (fun _ => s ^ m)) a := by
  have hi : Function.Injective (fun n : ℕ => m * n) := by
    intro a b hab
    exact Nat.eq_of_mul_eq_mul_left hm hab
  have hzero : ∀ n, n ∉ Set.range (fun n : ℕ => m * n) →
      p n (fun _ => s) = 0 := by
    intro n hn
    have hndvd : ¬m ∣ n := by
      rintro ⟨k, hk⟩
      exact hn ⟨k, hk.symm⟩
    rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff]
    change s ^ n • p n (fun _ => 1) = 0
    rw [hsupport n hndvd, smul_zero]
  convert (hi.hasSum_iff hzero).mpr hs using 1
  ext n
  simp only [Function.comp_def, FormalMultilinearSeries.apply_eq_pow_smul_coeff,
    powerSubseries_coeff, pow_mul]

/-- Coefficient support on multiples of a positive integer gives an
actual analytic factorization of germs through the corresponding power. -/
theorem analyticAt_factor_through_pow_of_coeff_support {F : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ} {m : ℕ} (hm : 0 < m)
    (hp : HasFPowerSeriesAt F p 0)
    (hsupport : ∀ n, ¬m ∣ n → p n (fun _ => 1) = 0) :
    ∃ H : ℂ → ℂ, AnalyticAt ℂ H 0 ∧ F =ᶠ[𝓝 0] (fun s => H (s ^ m)) := by
  refine ⟨(powerSubseries p m).sum,
    ((powerSubseries p m).hasFPowerSeriesOnBall
      (powerSubseries_radius_pos hp.radius_pos)).hasFPowerSeriesAt.analyticAt, ?_⟩
  filter_upwards [hp.eventually_hasSum] with s hs
  have hs' : HasSum (fun n => p n (fun _ => s)) (F s) := by
    simpa only [zero_add] using hs
  exact (hasSum_powerSubseries_pow hm hsupport hs').tsum_eq.symm

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentials
