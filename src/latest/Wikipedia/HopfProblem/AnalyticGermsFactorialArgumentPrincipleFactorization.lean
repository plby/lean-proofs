import Wikipedia.HopfProblem.RiemannMappingHurwitzFactorization

/-!
# The actual finite zeros used by the weighted argument principle

The zero set and its positive analytic multiplicities are obtained from
analytic factorization on the closed disc. The logarithmic-derivative
identity is proved for that genuine factorization, without a preparation
or factoriality assumption.
-/

noncomputable section

open Set Metric Function Filter Complex
open scoped Topology Real BigOperators

namespace Wikipedia.HopfProblem.AnalyticGermsFactorial.ArgumentPrinciple

/-- A boundary-nonvanishing analytic function has finitely many interior
zeros, positive actual multiplicities, and an analytic nonvanishing factor. -/
theorem exists_finset_factorization {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hf : AnalyticOnNhd ℂ f (closedBall c R))
    (hf₀ : ∀ z ∈ sphere c R, f z ≠ 0) (hR : 0 < R) :
    ∃ t : Finset ℂ,
      (∀ a, a ∈ t ↔ a ∈ ball c R ∧ f a = 0) ∧
      (∀ a ∈ t, 0 < analyticOrderNatAt f a) ∧
      ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (closedBall c R) ∧
        (f = fun z ↦ (∏ a ∈ t, (z - a) ^ analyticOrderNatAt f a) * g z) ∧
        (∀ z ∈ closedBall c R, g z ≠ 0) := by
  have hf_nonzero : ¬EqOn f 0 (closedBall c R) := by
    intro hfzero
    obtain ⟨z, hz⟩ := (NormedSpace.sphere_nonempty (x := c)).mpr hR.le
    exact hf₀ z hz (hfzero (sphere_subset_closedBall hz))
  obtain ⟨t, ht, g, hg, hfg, hg₀⟩ :=
    hf.exists_finset_eq_prod_smul_nonzero (isCompact_closedBall c R)
      isPreconnected_closedBall hf_nonzero
  have htball : ∀ a, a ∈ t ↔ a ∈ ball c R ∧ f a = 0 := by
    intro a
    rw [ht]
    constructor
    · rintro ⟨ha, hfa⟩
      rw [← sphere_union_ball, mem_union] at ha
      exact ⟨ha.resolve_left (fun ha' ↦ hf₀ a ha' hfa), hfa⟩
    · rintro ⟨ha, hfa⟩
      exact ⟨ball_subset_closedBall ha, hfa⟩
  refine ⟨t, htball, ?_, g, hg, ?_, hg₀⟩
  · intro a ha
    obtain ⟨haR, hfa⟩ := (ht a).mp ha
    change 0 < (analyticOrderAt f a).toNat
    apply ENat.toNat_pos
    · simp [analyticOrderAt_eq_zero, hf a haR, hfa]
    · intro htop
      exact hf_nonzero (hf.eqOn_zero_of_preconnected_of_eventuallyEq_zero
        isPreconnected_closedBall haR (analyticOrderAt_eq_top.mp htop))
  · simpa only [smul_eq_mul] using hfg

/-- On the boundary circle, the logarithmic derivative of the genuine
finite factorization is the sum of its root poles and the unit term. -/
theorem logDeriv_eq_sum_of_factorization {f g : ℂ → ℂ} {c : ℂ} {R : ℝ}
    {t : Finset ℂ} (hg : AnalyticOnNhd ℂ g (closedBall c R))
    (hg₀ : ∀ z ∈ closedBall c R, g z ≠ 0) (ht : (t : Set ℂ) ⊆ ball c R)
    (hfg : f = fun z ↦ (∏ a ∈ t, (z - a) ^ analyticOrderNatAt f a) * g z) :
    EqOn (logDeriv f)
      (fun z ↦ (∑ a ∈ t, (analyticOrderNatAt f a : ℂ) / (z - a)) + logDeriv g z)
      (sphere c R) := by
  intro z hz
  have hznot : z ∉ ball c R := by
    rw [mem_ball, mem_sphere.mp hz]
    exact lt_irrefl _
  have hne : ∀ a ∈ t, z - a ≠ 0 := by
    intro a ha
    exact sub_ne_zero.mpr (ne_of_mem_of_not_mem (ht ha) hznot).symm
  conv_lhs => rw [hfg]
  rw [logDeriv_mul, logDeriv_prod]
  · congr 1
    refine Finset.sum_congr rfl fun a ha ↦ ?_
    rw [logDeriv_fun_pow (by fun_prop), logDeriv, Pi.div_apply,
      deriv_sub_const, deriv_id'']
    simp [div_eq_mul_inv]
  · intro a ha
    exact pow_ne_zero _ (hne a ha)
  · intros
    fun_prop
  · rw [Finset.prod_ne_zero_iff]
    exact fun a ha ↦ pow_ne_zero _ (hne a ha)
  · exact hg₀ z (sphere_subset_closedBall hz)
  · fun_prop
  · exact (hg z (sphere_subset_closedBall hz)).differentiableAt

end Wikipedia.HopfProblem.AnalyticGermsFactorial.ArgumentPrinciple
