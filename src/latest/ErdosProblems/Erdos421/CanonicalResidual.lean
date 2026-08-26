import Mathlib.Analysis.Complex.CanonicalDecomposition
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Tactic

/-! # Removing the interior zeros without changing boundary norms -/

namespace Erdos421

open Complex Filter Function MeromorphicOn Metric Set Topology

noncomputable def canonicalProduct (f : ℂ → ℂ) (R : ℝ) : ℂ → ℂ :=
  ∏ᶠ w, canonicalFactor R w ^ (-divisor f (ball 0 R) w)

theorem canonicalProduct_eq_prod {f : ℂ → ℂ} {R : ℝ}
    (hf : MeromorphicOn f (closedBall 0 R)) :
    canonicalProduct f R =
      ∏ w ∈ hf.divisor_ball_support_finite.toFinset,
        canonicalFactor R w ^ (-divisor f (ball 0 R) w) := by
  classical
  apply finprod_eq_prod_of_mulSupport_subset_of_finite
  intro w hw
  by_contra hn
  have hzero : divisor f (ball 0 R) w = 0 := by simpa using hn
  simp [hzero] at hw

theorem analyticAt_canonicalProduct {f : ℂ → ℂ} {R : ℝ} {z : ℂ}
    (hz : z ∈ closedBall 0 R) (hdiv : divisor f (ball 0 R) z = 0) :
    AnalyticAt ℂ (canonicalProduct f R) z := by
  apply analyticAt_finprod
  intro w
  by_cases hw : divisor f (ball 0 R) w = 0
  · simp only [hw, neg_zero, zpow_zero]
    exact analyticAt_const
  have hwball : w ∈ ball 0 R :=
    (divisor f (ball 0 R)).supportWithinDomain hw
  have hzw : z ≠ w := by rintro rfl; exact hw hdiv
  exact (analyticOnNhd_canonicalFactor R w z hzw).zpow
    (canonicalFactor_ne_zero hwball hz hzw)

theorem canonicalProduct_ne_zero {f : ℂ → ℂ} {R : ℝ} {z : ℂ}
    (hz : z ∈ closedBall 0 R) (hdiv : divisor f (ball 0 R) z = 0) :
    canonicalProduct f R z ≠ 0 := by
  apply finprod_apply_ne_zero
  intro w
  by_cases hw : divisor f (ball 0 R) w = 0
  · simp [hw]
  have hwball : w ∈ ball 0 R :=
    (divisor f (ball 0 R)).supportWithinDomain hw
  have hzw : z ≠ w := by rintro rfl; exact hw hdiv
  exact zpow_ne_zero _ (canonicalFactor_ne_zero hwball hz hzw)

theorem canonicalResidual_analytic {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (D : CanonicalDecomp f g R) : AnalyticOnNhd ℂ g (closedBall 0 R) := by
  apply D.meromorphicNFOn.divisor_nonneg_iff_analyticOnNhd.mp
  intro z
  change 0 ≤ divisor g (closedBall 0 R) z
  rw [D.divisor_eq_divisor hR]
  exact (hf.mono sphere_subset_closedBall).divisor_nonneg z

theorem canonicalDecomp_eventuallyEq_at {f g : ℂ → ℂ} {R : ℝ} {z : ℂ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (D : CanonicalDecomp f g R) (hz : z ∈ closedBall 0 R)
    (hdiv : divisor f (ball 0 R) z = 0) :
    f =ᶠ[𝓝 z] fun x ↦ canonicalProduct f R x * g x := by
  have hp := analyticAt_canonicalProduct hz hdiv
  have hg := canonicalResidual_analytic hR hf D z hz
  apply ((hf z hz).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
    (hp.mul hg).continuousAt).mp
  apply MeromorphicAt.eventuallyEq_nhdsNE_of_eventuallyEq_codiscreteWithin_preperfect
    (U := closedBall 0 R) (hf z hz).meromorphicAt (hp.mul hg).meromorphicAt hz
  · rw [← closure_ball 0 hR.ne']
    exact isOpen_ball.perfect_closure.2
  · exact D.eventuallyEq

theorem norm_canonicalProduct_sphere {f : ℂ → ℂ} {R : ℝ} {z : ℂ}
    (hf : MeromorphicOn f (closedBall 0 R)) (hz : z ∈ sphere 0 R) :
    ‖canonicalProduct f R z‖ = 1 := by
  classical
  rw [canonicalProduct_eq_prod hf, Finset.prod_apply, norm_prod]
  apply Finset.prod_eq_one
  intro w hw
  have hwball := (divisor f (ball 0 R)).supportWithinDomain
    (hf.divisor_ball_support_finite.mem_toFinset.mp hw)
  simp only [Pi.pow_apply, norm_zpow, norm_canonicalFactor_eval_circle_eq_one hwball hz,
    one_zpow]

theorem norm_canonicalResidual_sphere {f g : ℂ → ℂ} {R : ℝ} {z : ℂ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (D : CanonicalDecomp f g R) (hz : z ∈ sphere 0 R) : ‖g z‖ = ‖f z‖ := by
  have hznot : z ∉ ball (0 : ℂ) R := by
    simp only [mem_sphere, dist_zero_right] at hz
    simp only [mem_ball, dist_zero_right, hz, lt_self_iff_false, not_false_eq_true]
  have he := (canonicalDecomp_eventuallyEq_at hR hf D (sphere_subset_closedBall hz)
    ((divisor f (ball 0 R)).apply_eq_zero_of_notMem hznot)).eq_of_nhds
  rw [he, norm_mul, norm_canonicalProduct_sphere hf.meromorphicOn hz, one_mul]

theorem norm_canonicalResidual_le {f g : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (D : CanonicalDecomp f g R) (hM : ∀ z ∈ sphere 0 R, ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ closedBall 0 R) : ‖g z‖ ≤ M := by
  apply Complex.norm_le_of_forall_mem_frontier_norm_le (U := ball 0 R) isBounded_ball
  · apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 hR.ne']
    exact (canonicalResidual_analytic hR hf D).differentiableOn
  · intro w hw
    rw [frontier_ball 0 hR.ne'] at hw
    rw [norm_canonicalResidual_sphere hR hf D hw]
    exact hM w hw
  · rwa [closure_ball 0 hR.ne']

theorem divisor_zero_of_ne_zero {f : ℂ → ℂ} {R : ℝ} {z : ℂ}
    (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hz : z ∈ closedBall 0 R)
    (hfz : f z ≠ 0) : divisor f (ball 0 R) z = 0 := by
  by_cases hb : z ∈ ball 0 R
  · rw [divisor_apply (hf.mono ball_subset_closedBall).meromorphicOn hb,
      (hf z hz).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfz]
    rfl
  · exact (divisor f (ball 0 R)).apply_eq_zero_of_notMem hb

theorem canonicalFactor_zero {R : ℝ} (hR : R ≠ 0) (w : ℂ) :
    canonicalFactor R w 0 = -(R : ℂ) / w := by
  rw [canonicalFactor_apply]
  simp only [mul_zero, sub_zero, zero_sub, mul_neg, div_neg]
  by_cases hw : w = 0
  · simp [hw]
  · have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR
    field_simp

theorem norm_canonicalProduct_zero_le_one {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0) :
    ‖canonicalProduct f R 0‖ ≤ 1 := by
  classical
  have hdiv0 := divisor_zero_of_ne_zero hf (mem_closedBall_self hR.le) hf0
  rw [canonicalProduct_eq_prod hf.meromorphicOn, Finset.prod_apply, norm_prod]
  apply Finset.prod_le_one (fun _ _ ↦ norm_nonneg _)
  intro w hw
  have hwsupport := hf.meromorphicOn.divisor_ball_support_finite.mem_toFinset.mp hw
  have hwball := (divisor f (ball 0 R)).supportWithinDomain hwsupport
  have hw0 : w ≠ 0 := by rintro rfl; exact hwsupport hdiv0
  have hnorm : ‖canonicalFactor R w 0‖ = R / ‖w‖ := by
    rw [canonicalFactor_zero hR.ne', norm_div, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hR]
  have hge : 1 ≤ ‖canonicalFactor R w 0‖ := by
    rw [hnorm, le_div_iff₀ (norm_pos_iff.mpr hw0), one_mul]
    exact (mem_ball_zero_iff.mp hwball).le
  simp only [Pi.pow_apply, norm_zpow]
  exact zpow_le_one_of_nonpos₀ hge
    (neg_nonpos.mpr ((hf.mono ball_subset_closedBall).divisor_nonneg w))

theorem norm_canonicalResidual_zero_ge {f g : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R))
    (D : CanonicalDecomp f g R) (hf0 : f 0 ≠ 0) : ‖f 0‖ ≤ ‖g 0‖ := by
  have h0 : (0 : ℂ) ∈ closedBall 0 R := mem_closedBall_self hR.le
  have he := (canonicalDecomp_eventuallyEq_at hR hf D h0
    (divisor_zero_of_ne_zero hf h0 hf0)).eq_of_nhds
  calc
    ‖f 0‖ = ‖canonicalProduct f R 0‖ * ‖g 0‖ := by rw [he, norm_mul]
    _ ≤ 1 * ‖g 0‖ := mul_le_mul_of_nonneg_right
      (norm_canonicalProduct_zero_le_one hR hf hf0) (norm_nonneg _)
    _ = ‖g 0‖ := one_mul _

theorem meromorphicOrderAt_ne_top_on_disk {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0) :
    ∀ z : closedBall (0 : ℂ) R, meromorphicOrderAt f z ≠ ⊤ := by
  rw [← hf.meromorphicOn.exists_meromorphicOrderAt_ne_top_iff_forall
    (Metric.isConnected_closedBall hR.le)]
  refine ⟨⟨0, mem_closedBall_self hR.le⟩, ?_⟩
  rw [(hf 0 (mem_closedBall_self hR.le)).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hf0]
  exact WithTop.coe_ne_top

theorem divisor_ne_zero_iff_zero_on_disk {f : ℂ → ℂ} {R : ℝ} {z : ℂ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0)
    (hz : z ∈ ball 0 R) : divisor f (ball 0 R) z ≠ 0 ↔ f z = 0 := by
  have he := (hf.mono ball_subset_closedBall).meromorphicNFOn.zero_set_eq_divisor_support
    (fun w ↦ meromorphicOrderAt_ne_top_on_disk hR hf hf0
      ⟨w, ball_subset_closedBall w.property⟩)
  change z ∈ Function.support (divisor f (ball 0 R)) ↔ _
  rw [← he]
  simp only [mem_inter_iff, mem_preimage, mem_singleton_iff, hz, true_and]

theorem exists_analytic_canonicalResidual {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall 0 R)) (hf0 : f 0 ≠ 0) :
    ∃ g : ℂ → ℂ, CanonicalDecomp f g R ∧ AnalyticOnNhd ℂ g (closedBall 0 R) := by
  obtain ⟨g, D⟩ := hf.meromorphicOn.exists_canonicalDecomp
    (meromorphicOrderAt_ne_top_on_disk hR hf hf0)
  exact ⟨g, D, canonicalResidual_analytic hR hf D⟩

end Erdos421
