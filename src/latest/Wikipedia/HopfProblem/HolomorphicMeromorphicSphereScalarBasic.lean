import Mathlib.Analysis.Meromorphic.FactorizedRational
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Normed.Field.Lemmas

/-!
# Scalar meromorphic functions at infinity

The hypotheses in this file use Mathlib's analytic definition of
`MeromorphicAt`.  Values at a pole, or at a removable discontinuity, are not
part of the meromorphic germ.
-/

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereScalar

open Filter Set Function Bornology
open scoped Topology

/-- Near a meromorphic germ, all other orders are zero, unless the germ is
identically zero.  In the latter case all those orders are infinite. -/
lemma eventually_order_zero_or_top {f : ℂ → ℂ} {x : ℂ}
    (hf : MeromorphicAt f x) :
    ∀ᶠ z in 𝓝[≠] x, meromorphicOrderAt f z = 0 ∨ meromorphicOrderAt f z = ⊤ := by
  rcases hf.eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · have hzero' : ∀ᶠ y in 𝓝 x, y ≠ x → f y = 0 := by
      simpa only [eventually_nhdsWithin_iff, mem_compl_iff, mem_singleton_iff] using hzero
    filter_upwards [(eventually_eventually_nhds.2 hzero').filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hzx
    right
    apply meromorphicOrderAt_eq_top_iff.2
    have hzx' : z ≠ x := hzx
    exact ((hz.and (eventually_ne_nhds hzx')).mono fun y hy => hy.1 hy.2).filter_mono
      nhdsWithin_le_nhds
  · filter_upwards [hf.eventually_analyticAt, hne] with z hz hzne
    left
    rw [hz.meromorphicOrderAt_eq, hz.analyticOrderAt_eq_zero.2 hzne]
    rfl

/-- Inversion preserves the meromorphic order at a nonzero point. -/
lemma order_comp_inv {f : ℂ → ℂ} {x : ℂ} (hx : x ≠ 0) :
    meromorphicOrderAt (fun z => f z⁻¹) x = meromorphicOrderAt f x⁻¹ := by
  apply meromorphicOrderAt_comp_of_deriv_ne_zero (analyticAt_id.inv hx)
  change deriv (fun z : ℂ => z⁻¹) x ≠ 0
  rw [(hasDerivAt_inv hx).deriv]
  exact neg_ne_zero.mpr (inv_ne_zero (pow_ne_zero 2 hx))

/-- A function meromorphic at infinity has zero divisor outside a bounded set. -/
lemma divisor_eventually_zero_at_infinity {f : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hinf : MeromorphicAt (fun z => f z⁻¹) 0) :
    ∀ᶠ z in cobounded ℂ, MeromorphicOn.divisor f univ z = 0 := by
  filter_upwards [tendsto_inv₀_cobounded'.eventually (eventually_order_zero_or_top hinf),
    tendsto_inv₀_cobounded'.eventually self_mem_nhdsWithin] with z hz hzne
  have hi : z⁻¹ ≠ 0 := hzne
  rw [order_comp_inv hi, inv_inv] at hz
  rw [hf.divisor_apply (mem_univ z)]
  rcases hz with hz | hz <;> simp [hz]

/-- The finite-plane divisor of a function meromorphic on the sphere is finite.
This derives finiteness from the analytic germ at infinity, not from a rational
presentation of the function. -/
theorem divisor_support_finite {f : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hinf : MeromorphicAt (fun z => f z⁻¹) 0) :
    (MeromorphicOn.divisor f univ).support.Finite := by
  let d := MeromorphicOn.divisor f univ
  have hb : IsBounded d.support := by
    change {z | d z ≠ 0}ᶜ ∈ cobounded ℂ
    change ∀ᶠ z in cobounded ℂ, ¬ d z ≠ 0
    simpa only [not_not, d] using divisor_eventually_zero_at_infinity hf hinf
  exact (Metric.isCompact_of_isClosed_isBounded (d.closedSupport isClosed_univ) hb).finite
    d.discreteSupport

/-- A nowhere-zero entire function whose reciprocal-coordinate expression is
meromorphic at zero is constant.  A pole at infinity is excluded by applying
Liouville to the reciprocal entire function. -/
theorem entire_nonvanishing_eq_const {g : ℂ → ℂ}
    (hg : Differentiable ℂ g) (hne : ∀ z, g z ≠ 0)
    (hinf : MeromorphicAt (fun z => g z⁻¹) 0) :
    ∀ z, g z = g 0 := by
  rcases lt_or_ge (meromorphicOrderAt (fun z => g z⁻¹) 0) 0 with ho | ho
  · have hlim : Tendsto (fun z => (g z)⁻¹) (cocompact ℂ) (𝓝 0) := by
      rw [← Metric.cobounded_eq_cocompact]
      simpa only [Function.comp_def, inv_inv] using
        (tendsto_inv₀_cobounded.comp (tendsto_cobounded_of_meromorphicOrderAt_neg ho)).comp
          tendsto_inv₀_cobounded'
    have hbad := (hg.inv hne).apply_eq_of_tendsto_cocompact 0 hlim
    exact (inv_ne_zero (hne 0) hbad).elim
  · obtain ⟨c, hc⟩ := tendsto_nhds_of_meromorphicOrderAt_nonneg hinf ho
    have hlim : Tendsto g (cocompact ℂ) (𝓝 c) := by
      rw [← Metric.cobounded_eq_cocompact]
      simpa only [Function.comp_def, inv_inv] using hc.comp tendsto_inv₀_cobounded'
    intro z
    exact (hg.apply_eq_of_tendsto_cocompact z hlim).trans
      (hg.apply_eq_of_tendsto_cocompact 0 hlim).symm

end Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereScalar
