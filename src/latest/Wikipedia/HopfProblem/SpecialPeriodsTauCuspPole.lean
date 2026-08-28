import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Meromorphic.Order

/-!
# The analytic numerator of an actual simple pole

Meromorphic order `-1` supplies an analytic nonvanishing numerator; it is
not additional cusp-germ data. A specified punctured limit of `t * F t`
determines the numerator's value at zero uniquely.
-/

open Filter Set Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.TauCusp

/-- An actual meromorphic simple pole has an analytic nonvanishing numerator
on a punctured disc. -/
theorem simplePole_factorization {F : ℂ → ℂ} (hF : MeromorphicAt F 0)
    (horder : meromorphicOrderAt F 0 = (-1 : ℤ)) :
    ∃ a : ℂ → ℂ, AnalyticAt ℂ a 0 ∧ a 0 ≠ 0 ∧
      ∃ r > 0, ∀ t ∈ Metric.ball 0 r, t ≠ 0 → F t = a t / t := by
  obtain ⟨a, ha, ha0, heq⟩ := (meromorphicOrderAt_eq_int_iff hF).mp horder
  have heq' : ∀ᶠ t in 𝓝[≠] (0 : ℂ), F t = a t / t := by
    filter_upwards [heq] with t ht
    simpa [sub_zero, zpow_neg_one, smul_eq_mul, div_eq_mul_inv, mul_comm] using ht
  rw [eventually_nhdsWithin_iff] at heq'
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp heq'
  exact ⟨a, ha, ha0, r, hr, fun t ht hne => hball ht hne⟩

/-- The punctured normalization limit is the actual value of the analytic
numerator supplied by the simple-pole factorization. -/
theorem simplePole_factorization_of_tendsto {F : ℂ → ℂ} (hF : MeromorphicAt F 0)
    (horder : meromorphicOrderAt F 0 = (-1 : ℤ)) {c : ℂ}
    (hc : Tendsto (fun t => t * F t) (𝓝[≠] 0) (𝓝 c)) :
    ∃ a : ℂ → ℂ, AnalyticAt ℂ a 0 ∧ a 0 ≠ 0 ∧ a 0 = c ∧
      ∃ r > 0, ∀ t ∈ Metric.ball 0 r, t ≠ 0 → F t = a t / t := by
  obtain ⟨a, ha, ha0, r, hr, hball⟩ := simplePole_factorization hF horder
  have heq : (fun t => t * F t) =ᶠ[𝓝[≠] (0 : ℂ)] a := by
    have hnear : ∀ᶠ t in 𝓝[≠] (0 : ℂ), t ∈ Metric.ball 0 r :=
      nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℂ) hr)
    filter_upwards [hnear, self_mem_nhdsWithin] with t ht hne
    have ht0 : t ≠ 0 := hne
    rw [hball t ht ht0]
    field_simp [ht0]
  have hvalue : a 0 = c := tendsto_nhds_unique
    ha.continuousAt.continuousWithinAt (hc.congr' heq)
  exact ⟨a, ha, ha0, hvalue, r, hr, hball⟩

end Wikipedia.HopfProblem.SpecialPeriods.TauCusp
