import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereScalarBasic

/-!
# Removing the finite divisor on the sphere

We use the analytic zero-and-pole extraction theorem, then prove that its
nowhere-zero entire factor is meromorphic at infinity.  This last assertion
requires upgrading germ equality to actual equality at the regular points
near infinity; arbitrary values at isolated singularities are not ignored.
-/

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereScalar

open Filter Set Function Bornology
open scoped Topology

/-- Codiscrete equality on the whole plane gives equality of each meromorphic
germ, without asserting equality of the values at its center. -/
lemma eventuallyEq_nhdsNE_of_codiscrete {f g : ℂ → ℂ}
    (h : f =ᶠ[codiscreteWithin univ] g) (z : ℂ) : f =ᶠ[𝓝[≠] z] g := by
  have hh := mem_codiscreteWithin_iff_forall_mem_nhdsNE.1 h z (mem_univ z)
  change {w | f w = g w} ∈ 𝓝[≠] z
  simpa only [compl_univ, union_empty] using hh

/-- A finite factorized rational function is meromorphic at infinity. -/
lemma factorizedRational_meromorphicAt_infinity (d : ℂ → ℤ) (hd : d.HasFiniteSupport) :
    MeromorphicAt (fun z => (∏ᶠ u, (· - u) ^ d u) z⁻¹) 0 := by
  have hs : (fun u => (fun z : ℂ => z - u) ^ d u).mulSupport ⊆ hd.toFinset := by
    intro u hu
    apply hd.mem_toFinset.mpr
    simpa only [Function.FactorizedRational.mulSupport] using hu
  rw [finprod_eq_prod_of_mulSupport_subset _ hs]
  simp only [Finset.prod_apply, Pi.pow_apply]
  apply MeromorphicAt.fun_prod
  intro u hu
  exact (((MeromorphicAt.id 0).inv.sub (.const u 0)).zpow (d u))

/-- Such a factorized function does not vanish near infinity. -/
lemma factorizedRational_eventually_ne_zero_at_infinity (d : ℂ → ℤ)
    (hd : d.HasFiniteSupport) :
    ∀ᶠ z in 𝓝[≠] (0 : ℂ), (∏ᶠ u, (· - u) ^ d u) z⁻¹ ≠ 0 := by
  have hbound : IsBounded d.support := hd.isBounded
  have hzero : ∀ᶠ z in cobounded ℂ, d z = 0 := by
    have hh : d.supportᶜ ∈ cobounded ℂ := hbound
    change ∀ᶠ z in cobounded ℂ, ¬ d z ≠ 0 at hh
    simpa only [not_not] using hh
  have hne : ∀ᶠ z in cobounded ℂ, (∏ᶠ u, (· - u) ^ d u) z ≠ 0 := by
    filter_upwards [hzero] with z hz
    exact Function.FactorizedRational.ne_zero hz
  exact tendsto_inv₀_nhdsNE_zero.eventually hne

/-- The entire factor obtained after removing a finite divisor remains
meromorphic at infinity.  Both the divisor and the comparison are genuine
analytic data; no rational presentation of `f` is assumed. -/
lemma entire_factor_meromorphicAt_infinity {f g : ℂ → ℂ} (d : ℂ → ℤ)
    (hd : d.HasFiniteSupport) (hinf : MeromorphicAt (fun z => f z⁻¹) 0)
    (hg : AnalyticOnNhd ℂ g univ) (hne : ∀ z, g z ≠ 0)
    (hfg : f =ᶠ[codiscreteWithin univ] (∏ᶠ u, (· - u) ^ d u) * g) :
    MeromorphicAt (fun z => g z⁻¹) 0 := by
  let φ : ℂ → ℂ := ∏ᶠ u, (· - u) ^ d u
  have hregular : ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z⁻¹ = φ z⁻¹ * g z⁻¹ := by
    filter_upwards [hinf.eventually_analyticAt, self_mem_nhdsWithin] with z hz hz0
    have hz0' : z ≠ 0 := hz0
    have hfa : AnalyticAt ℂ f z⁻¹ := by
      have hz' : AnalyticAt ℂ (fun w => f w⁻¹) (z⁻¹)⁻¹ := by
        simpa only [inv_inv] using hz
      simpa only [Function.comp_def, inv_inv] using
        hz'.comp (analyticAt_id.inv (inv_ne_zero hz0'))
    have hpa : MeromorphicNFAt (φ * g) z⁻¹ :=
      (meromorphicNFAt_mul_iff_left (hg _ (mem_univ _)) (hne _)).2
        (Function.FactorizedRational.meromorphicNFOn_univ d (mem_univ _))
    exact ((hfa.meromorphicNFAt.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hpa).1
      (eventuallyEq_nhdsNE_of_codiscrete hfg z⁻¹)).eq_of_nhds
  have hquot : (fun z => f z⁻¹ / φ z⁻¹) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => g z⁻¹) := by
    filter_upwards [hregular, factorizedRational_eventually_ne_zero_at_infinity d hd]
      with z hz hp
    rw [hz]
    exact mul_div_cancel_left₀ _ hp
  exact (hinf.div (factorizedRational_meromorphicAt_infinity d hd)).congr hquot

/-- A scalar function meromorphic in both sphere charts is, as a meromorphic
germ at every finite point, a constant times the finite product specified by
its actual divisor. -/
theorem exists_const_mul_factorizedRational {f : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hinf : MeromorphicAt (fun z => f z⁻¹) 0) :
    ∃ c : ℂ, ∀ z : ℂ, f =ᶠ[𝓝[≠] z]
      (fun w => c * (∏ᶠ u, (· - u) ^ MeromorphicOn.divisor f univ u) w) := by
  by_cases hnonzero : ∃ z, meromorphicOrderAt f z ≠ ⊤
  · obtain ⟨z, hz⟩ := hnonzero
    have hnotop : ∀ u : (univ : Set ℂ), meromorphicOrderAt f u ≠ ⊤ :=
      (hf.exists_meromorphicOrderAt_ne_top_iff_forall isConnected_univ).1
        ⟨⟨z, mem_univ z⟩, hz⟩
    have hd := divisor_support_finite hf hinf
    obtain ⟨g, hg, hgne, hfg⟩ := hf.extract_zeros_poles hnotop hd
    have hgne' : ∀ z, g z ≠ 0 := fun z => hgne ⟨z, mem_univ z⟩
    have hmul : f =ᶠ[codiscreteWithin univ]
        (∏ᶠ u, (· - u) ^ MeromorphicOn.divisor f univ u) * g := by
      simpa only [smul_eq_mul] using hfg
    have hginf := entire_factor_meromorphicAt_infinity _ hd hinf hg hgne' hmul
    have hconst := entire_nonvanishing_eq_const
      (fun z => (hg z (mem_univ z)).differentiableAt) hgne' hginf
    refine ⟨g 0, fun z => ?_⟩
    filter_upwards [eventuallyEq_nhdsNE_of_codiscrete hmul z] with w hw
    simpa only [Pi.mul_apply, hconst w, mul_comm] using hw
  · refine ⟨0, fun z => ?_⟩
    have hz : meromorphicOrderAt f z = ⊤ := by
      by_contra hn
      exact hnonzero ⟨z, hn⟩
    filter_upwards [meromorphicOrderAt_eq_top_iff.1 hz] with w hw
    simpa only [zero_mul] using hw

end Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereScalar
