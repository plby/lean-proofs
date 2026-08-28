import Wikipedia.HopfProblem.SpecialPeriodsMuGeneratorCuspFactors
import Wikipedia.HopfProblem.SpecialPeriodsMuGeneratorCuspRoot
import Wikipedia.HopfProblem.SpecialPeriodsTriangleHorodisc
import Mathlib.Topology.Algebra.Field

/-!
# The simple cusp pole of the actual μ-generator

Given the exact cusp expansion of a supplied upper-half-plane map `τ`,
the actual function `E₄(τ)² * r / Δ(τ)` is `q⁻¹` times an analytic unit.
The unit is constructed from the modular q-expansions. The square-root
branch agrees with the global root up to one constant sign on a connected
high horodisc; no periodicity or asymptotic formula for the generator is
assumed.
-/

noncomputable section

open Function Set Filter Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.MuGenerator

/-- A nonnegative-height horodisc is connected because its image in the
ordinary complex plane is a convex open half-plane. -/
theorem cuspHorodisc_isPreconnected (Y : ℝ) (hY : 0 ≤ Y) :
    IsPreconnected (Triangle.horodisc Y : Set ℍ) := by
  apply UpperHalfPlane.isOpenEmbedding_coe.toIsEmbedding.toIsInducing.isPreconnected_image.mp
  have he : (UpperHalfPlane.coe '' (Triangle.horodisc Y : Set ℍ)) =
      {w : ℂ | Y < w.im} := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact hz
    · intro hw
      exact ⟨⟨w, hY.trans_lt hw⟩, hw, rfl⟩
  rw [he]
  exact (convex_halfSpace_im_gt Y).isPreconnected

namespace Root

variable {τ : ℍ → ℍ} (r : Root τ)

/-- The global root agrees with one analytic root in the source cusp
coordinate, up to a single sign on the entire sufficiently high horodisc. -/
theorem exists_cusp_root_unit {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0)
    (hq : ∀ᶠ z in atImInfty,
      Periodic.qParam 1 (τ z) = Triangle.cuspQ z * u (Triangle.cuspQ z)) :
    ∃ b : ℂ → ℂ, AnalyticAt ℂ b 0 ∧ (b 0 = 1 ∨ b 0 = -1) ∧
      ∀ᶠ z in atImInfty, r z = b (Triangle.cuspQ z) := by
  obtain ⟨R, hR, b, hb, hb0, hbne, hbsq⟩ := exists_analytic_sqrt_ball_one
    (cuspEisensteinSix_analyticAt hu) (cuspEisensteinSix_zero u)
  have hsmall : ∀ᶠ z in atImInfty, Triangle.cuspQ z ∈ Metric.ball 0 R :=
    (qParam_tendsto_atImInfty Triangle.width_pos).eventually (Metric.ball_mem_nhds 0 hR)
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).mp (hq.and hsmall)
  let Y := max A Triangle.width
  have hY : 0 ≤ Y := Triangle.width_pos.le.trans (le_max_right _ _)
  have hhigh : ∀ z ∈ Triangle.horodisc Y,
      Periodic.qParam 1 (τ z) = Triangle.cuspQ z * u (Triangle.cuspQ z) ∧
        Triangle.cuspQ z ∈ Metric.ball 0 R := by
    intro z hz
    change Y < z.im at hz
    exact hA z ((le_max_left _ _).trans hz.le)
  have hcont : ContinuousOn (b ∘ Triangle.cuspQ) (Triangle.horodisc Y : Set ℍ) :=
    hb.continuousOn.comp Triangle.cuspQ_continuous.continuousOn
      (fun z hz => (hhigh z hz).2)
  have hsq : EqOn ((r : ℍ → ℂ) ^ 2) ((b ∘ Triangle.cuspQ) ^ 2)
      (Triangle.horodisc Y : Set ℍ) := by
    intro z hz
    change r z ^ 2 = b (Triangle.cuspQ z) ^ 2
    exact (r.square_eq_cuspEisensteinSix u z (hhigh z hz).1).trans
      (hbsq (hhigh z hz).2).symm
  have hne : ∀ {z : ℍ}, z ∈ Triangle.horodisc Y → (b ∘ Triangle.cuspQ) z ≠ 0 :=
    fun {z} hz => hbne _ (hhigh z hz).2
  have hYe : ∀ᶠ z in atImInfty, z ∈ Triangle.horodisc Y := by
    apply (UpperHalfPlane.atImInfty_mem _).mpr
    refine ⟨Y + 1, fun z hz => ?_⟩
    change Y < z.im
    linarith
  have hbAt : AnalyticAt ℂ b 0 := hb 0 (Metric.mem_ball_self hR)
  rcases (cuspHorodisc_isPreconnected Y hY).eq_or_eq_neg_of_sq_eq
    r.holomorphic.continuous.continuousOn hcont hsq hne with h | h
  · exact ⟨b, hbAt, Or.inl hb0, hYe.mono fun z hz => h hz⟩
  · refine ⟨-b, hbAt.neg, Or.inr ?_, ?_⟩
    · simp only [Pi.neg_apply, hb0]
    · filter_upwards [hYe] with z hz
      simpa only [Pi.neg_apply, Function.comp_apply] using h hz

/-- The source's actual μ-generator has the derived cusp form `q⁻¹ v(q)`,
where `v` is an analytic unit at zero. -/
theorem exists_cusp_unit {u : ℂ → ℂ} (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hq : ∀ᶠ z in atImInfty,
      Periodic.qParam 1 (τ z) = Triangle.cuspQ z * u (Triangle.cuspQ z)) :
    ∃ v : ℂ → ℂ, AnalyticAt ℂ v 0 ∧ v 0 ≠ 0 ∧
      ∀ᶠ z in atImInfty, r.generator z = (Triangle.cuspQ z)⁻¹ * v (Triangle.cuspQ z) := by
  obtain ⟨b, hb, hb0, hrb⟩ := r.exists_cusp_root_unit hu hq
  have hbne : b 0 ≠ 0 := by rcases hb0 with h | h <;> simp [h]
  refine ⟨cuspGeneratorUnit u b, cuspGeneratorUnit_analyticAt hu hb hu0,
    cuspGeneratorUnit_zero_ne_zero hu0 hbne, ?_⟩
  filter_upwards [hq, hrb] with z hqz hrz
  exact r.generator_eq_inv_q_mul_unit u b z hqz hrz

/-- The unit and the factorization hold on an actual disc and an actual
horodisc above the triangle cusp height, with nonvanishing throughout the disc. -/
theorem exists_cusp_unit_on_horodisc {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hq : ∀ᶠ z in atImInfty,
      Periodic.qParam 1 (τ z) = Triangle.cuspQ z * u (Triangle.cuspQ z)) :
    ∃ R > 0, R < 1 ∧ ∃ Y : ℝ, Triangle.width ≤ Y ∧ ∃ v : ℂ → ℂ,
      AnalyticOnNhd ℂ v (Metric.ball 0 R) ∧
      (∀ t ∈ Metric.ball 0 R, v t ≠ 0) ∧
      ∀ z ∈ Triangle.horodisc Y, Triangle.cuspQ z ∈ Metric.ball 0 R ∧
        r.generator z = (Triangle.cuspQ z)⁻¹ * v (Triangle.cuspQ z) := by
  obtain ⟨v, hv, hv0, hF⟩ := r.exists_cusp_unit hu hu0 hq
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp
    (hv.eventually_analyticAt.and (hv.continuousAt.eventually_ne hv0))
  let R := min ε (1 / 2)
  have hR : 0 < R := lt_min hε (by norm_num)
  have hR1 : R < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hsub : Metric.ball (0 : ℂ) R ⊆ Metric.ball 0 ε :=
    Metric.ball_subset_ball (min_le_left _ _)
  have hsmall : ∀ᶠ z in atImInfty, Triangle.cuspQ z ∈ Metric.ball 0 R :=
    (qParam_tendsto_atImInfty Triangle.width_pos).eventually (Metric.ball_mem_nhds 0 hR)
  obtain ⟨A, hA⟩ := (UpperHalfPlane.atImInfty_mem _).mp (hsmall.and hF)
  refine ⟨R, hR, hR1, max A Triangle.width, le_max_right _ _, v,
    (fun t ht => (hball (hsub ht)).1), (fun t ht => (hball (hsub ht)).2), ?_⟩
  intro z hz
  change max A Triangle.width < z.im at hz
  exact hA z ((le_max_left _ _).trans hz.le)

/-- An actual meromorphic function in the cusp coordinate agrees with the
μ-generator high in the cusp and has precisely a simple pole at zero. -/
theorem exists_cusp_meromorphic_function {u : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) (hu0 : u 0 ≠ 0)
    (hq : ∀ᶠ z in atImInfty,
      Periodic.qParam 1 (τ z) = Triangle.cuspQ z * u (Triangle.cuspQ z)) :
    ∃ F : ℂ → ℂ, MeromorphicAt F 0 ∧ meromorphicOrderAt F 0 = (-1 : ℤ) ∧
      ∀ᶠ z in atImInfty, r.generator z = F (Triangle.cuspQ z) := by
  obtain ⟨v, hv, hv0, hF⟩ := r.exists_cusp_unit hu hu0 hq
  refine ⟨fun t => v t / t, hv.meromorphicAt.div analyticAt_id.meromorphicAt, ?_, ?_⟩
  · change meromorphicOrderAt (v / id) 0 = (-1 : ℤ)
    rw [meromorphicOrderAt_div hv.meromorphicAt analyticAt_id.meromorphicAt,
      hv.meromorphicOrderAt_eq, hv.analyticOrderAt_eq_zero.mpr hv0, meromorphicOrderAt_id]
    norm_num
  · filter_upwards [hF] with z hz
    simpa only [div_eq_mul_inv, mul_comm] using hz

end Root

end Wikipedia.HopfProblem.SpecialPeriods.MuGenerator
