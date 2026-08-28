import Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsRemovableUpdate

/-!
# Removability from vanishing after multiplication by a local parameter

An analytic punctured function with `(z-b)F(z) → 0` has a finite limit
and extends analytically by its actual punctured limit. This is the
little-o form of removable singularity, not a boundedness assumption.
-/

noncomputable section

open Filter Asymptotics
open scoped Topology

namespace Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsRemovable

/-- Vanishing of the local-parameter product rules out even a simple
pole and gives the actual finite punctured limit. -/
theorem tendsto_limUnder_of_sub_mul_tendsto_zero {F : ℂ → ℂ} {b : ℂ}
    (hF : ∀ᶠ z in 𝓝[≠] b, AnalyticAt ℂ F z)
    (ht : Tendsto (fun z => (z - b) * F z) (𝓝[≠] b) (𝓝 0)) :
    Tendsto F (𝓝[≠] b) (𝓝 (limUnder (𝓝[≠] b) F)) := by
  apply Complex.tendsto_limUnder_of_differentiable_on_punctured_nhds_of_isLittleO
    (hF.mono fun _ hz => hz.differentiableAt)
  apply (Asymptotics.isLittleO_iff_tendsto ?_).mpr
  · have hz : Tendsto (fun z : ℂ => z - b) (𝓝[≠] b) (𝓝 0) := by
      have hid : Tendsto (fun z : ℂ => z) (𝓝[≠] b) (𝓝 b) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa only [sub_self] using hid.sub_const b
    have hdiff : Tendsto (fun z => (z - b) * F z - (z - b) * F b)
        (𝓝[≠] b) (𝓝 0) := by
      simpa only [zero_mul, sub_zero] using ht.sub (hz.mul_const (F b))
    convert hdiff using 1
    ext z
    simp only [div_eq_mul_inv, inv_inv]
    ring
  · intro z hz
    have hzb : z = b := sub_eq_zero.mp (inv_eq_zero.mp hz)
    simp only [hzb, sub_self]

theorem analyticAt_update_limUnder_of_sub_mul_tendsto_zero {F : ℂ → ℂ} {b : ℂ}
    (hF : ∀ᶠ z in 𝓝[≠] b, AnalyticAt ℂ F z)
    (ht : Tendsto (fun z => (z - b) * F z) (𝓝[≠] b) (𝓝 0)) :
    AnalyticAt ℂ (Function.update F b (limUnder (𝓝[≠] b) F)) b :=
  analyticAt_update_of_tendsto hF (tendsto_limUnder_of_sub_mul_tendsto_zero hF ht)

theorem exists_analytic_extension_of_sub_mul_tendsto_zero {F : ℂ → ℂ} {b : ℂ}
    (hF : ∀ᶠ z in 𝓝[≠] b, AnalyticAt ℂ F z)
    (ht : Tendsto (fun z => (z - b) * F z) (𝓝[≠] b) (𝓝 0)) :
    ∃ Fext : ℂ → ℂ, AnalyticAt ℂ Fext b ∧
      Fext =ᶠ[𝓝[≠] b] F ∧ Fext b = limUnder (𝓝[≠] b) F :=
  exists_analytic_extension_of_tendsto hF (tendsto_limUnder_of_sub_mul_tendsto_zero hF ht)

/-- Vanishing local-parameter products at two punctures give an actual
entire two-point update, with the punctured limits as its values. -/
theorem patchTwo_entire_of_sub_mul_tendsto_zero {F : ℂ → ℂ} {a b : ℂ} (hab : a ≠ b)
    (hF : ∀ z, z ≠ a → z ≠ b → AnalyticAt ℂ F z)
    (ha : Tendsto (fun z => (z - a) * F z) (𝓝[≠] a) (𝓝 0))
    (hb : Tendsto (fun z => (z - b) * F z) (𝓝[≠] b) (𝓝 0)) :
    ∀ z, AnalyticAt ℂ
      (patchTwo F a b (limUnder (𝓝[≠] a) F) (limUnder (𝓝[≠] b) F)) z := by
  have hFa : ∀ᶠ z in 𝓝[≠] a, AnalyticAt ℂ F z := by
    filter_upwards [self_mem_nhdsWithin, eventually_ne_nhdsWithin hab] with z hza hzb
    exact hF z hza hzb
  have hFb : ∀ᶠ z in 𝓝[≠] b, AnalyticAt ℂ F z := by
    filter_upwards [self_mem_nhdsWithin, eventually_ne_nhdsWithin hab.symm] with z hzb hza
    exact hF z hza hzb
  exact patchTwo_entire hab hF (tendsto_limUnder_of_sub_mul_tendsto_zero hFa ha)
    (tendsto_limUnder_of_sub_mul_tendsto_zero hFb hb)

end Wikipedia.HopfProblem.TriangleHolomorphicDifferentialsRemovable
