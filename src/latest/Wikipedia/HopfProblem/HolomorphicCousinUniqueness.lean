import Wikipedia.HopfProblem.HolomorphicCousinAnnulus
import Mathlib.Analysis.Complex.Liouville

/-!
# Uniqueness for the two-disc additive Cousin problem

Functions on the finite disc and on the inverse-coordinate disc which agree
on their annular overlap give an actual entire function.  Its limit at infinity
is its inverse-coordinate value at zero.  Liouville's theorem therefore proves
that both functions are constant.  Subtraction then proves uniqueness of a
normalized additive splitting.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace Wikipedia.HopfProblem.HolomorphicCousin

/-- The function obtained by gluing the finite and inverse-coordinate charts.
The agreement hypothesis is used to prove its analyticity, not in its definition. -/
def twoChartGlue (b : ℝ) (f G : ℂ → ℂ) (z : ℂ) : ℂ :=
  if ‖z‖ < b then f z else G z⁻¹

theorem twoChartGlue_eq_f {b : ℝ} {f G : ℂ → ℂ} {z : ℂ}
    (hz : z ∈ ball 0 b) : twoChartGlue b f G z = f z := by
  exact if_pos (by simpa only [mem_ball, dist_zero_right] using hz)

theorem twoChartGlue_eq_G {a b : ℝ} {f G : ℂ → ℂ}
    (hfg : ∀ z ∈ annulus a b, f z = G z⁻¹) {z : ℂ}
    (hz : a < ‖z‖) : twoChartGlue b f G z = G z⁻¹ := by
  by_cases hzb : ‖z‖ < b
  · exact (if_pos hzb).trans (hfg z ⟨hz, hzb⟩)
  · exact if_neg hzb

/-- The two open chart domains really cover the complex plane, and their
agreement makes the glued function entire, including points on the seam. -/
theorem twoChartGlue_analyticAt {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {f G : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 b))
    (hG : AnalyticOnNhd ℂ G (ball 0 a⁻¹))
    (hfg : ∀ z ∈ annulus a b, f z = G z⁻¹) (z : ℂ) :
    AnalyticAt ℂ (twoChartGlue b f G) z := by
  by_cases hzb : ‖z‖ < b
  · have hz : z ∈ ball (0 : ℂ) b := by
      simpa only [mem_ball, dist_zero_right] using hzb
    apply (hf z hz).congr
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    exact (twoChartGlue_eq_f hw).symm
  · have haz : a < ‖z‖ := hab.trans_le (le_of_not_gt hzb)
    have hz0 : z ≠ 0 := norm_pos_iff.mp (ha.trans haz)
    have hzi : z⁻¹ ∈ ball (0 : ℂ) a⁻¹ := by
      simp only [mem_ball, dist_zero_right, norm_inv]
      exact (inv_lt_inv₀ (ha.trans haz) ha).mpr haz
    apply ((hG z⁻¹ hzi).comp (analyticAt_inv hz0)).congr
    filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds haz]
      with w hw
    exact (twoChartGlue_eq_G hfg hw).symm

/-- The glued function tends at infinity to the value of its second chart at
the origin.  Thus the boundedness needed for Liouville is a proved consequence
of its two-chart construction. -/
theorem twoChartGlue_tendsto_cocompact {a b : ℝ} (ha : 0 < a)
    {f G : ℂ → ℂ} (hG : AnalyticOnNhd ℂ G (ball 0 a⁻¹)) :
    Tendsto (twoChartGlue b f G) (cocompact ℂ) (𝓝 (G 0)) := by
  have hG0 : ContinuousAt G 0 :=
    (hG 0 (by simpa only [mem_ball, dist_self] using inv_pos.mpr ha)).continuousAt
  have hlim : Tendsto (fun z : ℂ => G z⁻¹) (Bornology.cobounded ℂ) (𝓝 (G 0)) :=
    hG0.tendsto.comp tendsto_inv₀_cobounded
  rw [← Metric.cobounded_eq_cocompact]
  apply hlim.congr'
  filter_upwards [eventually_cobounded_le_norm b] with z hz
  exact (if_neg (not_lt.mpr hz)).symm

/-- A holomorphic function on the two standard overlapping charts of the
Riemann sphere is constant.  The global entire function is constructed above. -/
theorem eq_const_of_two_chart_agreement {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {f G : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f (ball 0 b))
    (hG : AnalyticOnNhd ℂ G (ball 0 a⁻¹))
    (hfg : ∀ z ∈ annulus a b, f z = G z⁻¹) :
    EqOn f (fun _ => G 0) (ball 0 b) ∧
      EqOn G (fun _ => G 0) (ball 0 a⁻¹) := by
  have hd : Differentiable ℂ (twoChartGlue b f G) :=
    fun z => (twoChartGlue_analyticAt ha hab hf hG hfg z).differentiableAt
  have hc : ∀ z, twoChartGlue b f G z = G 0 := fun z =>
    hd.apply_eq_of_tendsto_cocompact z (twoChartGlue_tendsto_cocompact ha hG)
  constructor
  · intro z hz
    exact (twoChartGlue_eq_f hz).symm.trans (hc z)
  · intro u hu
    by_cases hu0 : u = 0
    · subst u
      rfl
    · have hu' : ‖u‖ < a⁻¹ := by
        simpa only [mem_ball, dist_zero_right] using hu
      have hai : a < ‖u⁻¹‖ := by
        rw [norm_inv]
        exact (lt_inv_comm₀ ha (norm_pos_iff.mpr hu0)).mpr hu'
      simpa only [inv_inv] using (twoChartGlue_eq_G hfg hai).symm.trans (hc u⁻¹)

/-- The additive Cousin splitting is unique when the inverse-coordinate
summand has value zero at infinity. -/
theorem normalized_splitting_unique {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {h f₁ f₂ G₁ G₂ : ℂ → ℂ}
    (hf₁ : AnalyticOnNhd ℂ f₁ (ball 0 b))
    (hf₂ : AnalyticOnNhd ℂ f₂ (ball 0 b))
    (hG₁ : AnalyticOnNhd ℂ G₁ (ball 0 a⁻¹))
    (hG₂ : AnalyticOnNhd ℂ G₂ (ball 0 a⁻¹))
    (hs₁ : ∀ z ∈ annulus a b, f₁ z + G₁ z⁻¹ = h z)
    (hs₂ : ∀ z ∈ annulus a b, f₂ z + G₂ z⁻¹ = h z)
    (hG₁0 : G₁ 0 = 0) (hG₂0 : G₂ 0 = 0) :
    EqOn f₁ f₂ (ball 0 b) ∧ EqOn G₁ G₂ (ball 0 a⁻¹) := by
  have hag : ∀ z ∈ annulus a b, f₁ z - f₂ z = G₂ z⁻¹ - G₁ z⁻¹ := by
    intro z hz
    have he := (hs₁ z hz).trans (hs₂ z hz).symm
    exact sub_eq_sub_iff_add_eq_add.mpr (he.trans (add_comm _ _))
  obtain ⟨hfinite, hinfty⟩ := eq_const_of_two_chart_agreement ha hab
    (hf₁.sub hf₂) (hG₂.sub hG₁) hag
  constructor
  · intro z hz
    have hz' := hfinite hz
    simpa only [Pi.sub_apply, hG₁0, hG₂0, sub_zero, sub_eq_zero] using hz'
  · intro u hu
    have hu' := hinfty hu
    have he : G₂ u = G₁ u := by
      simpa only [Pi.sub_apply, hG₁0, hG₂0, sub_zero, sub_eq_zero] using hu'
    exact he.symm

/-- Negative-degree transition functions have no nonzero holomorphic section
on this two-chart cover.  This includes the `O(-1)` vanishing used in the
additive Cousin argument. -/
theorem negative_twist_eq_zero {a b : ℝ} (ha : 0 < a) (hab : a < b)
    {m : ℕ} (hm : 0 < m) {f G : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f (ball 0 b))
    (hG : AnalyticOnNhd ℂ G (ball 0 a⁻¹))
    (hfg : ∀ z ∈ annulus a b, f z = z⁻¹ ^ m * G z⁻¹) :
    EqOn f (fun _ => 0) (ball 0 b) ∧
      EqOn G (fun _ => 0) (ball 0 a⁻¹) := by
  have hH : AnalyticOnNhd ℂ (fun u => u ^ m * G u) (ball 0 a⁻¹) :=
    fun u hu => (analyticAt_id.pow m).mul (hG u hu)
  obtain ⟨hfconst, hHconst⟩ := eq_const_of_two_chart_agreement ha hab hf hH hfg
  have hfinite : EqOn f (fun _ => 0) (ball 0 b) := by
    simpa only [zero_pow hm.ne', zero_mul] using hfconst
  have hGoff (u : ℂ) (hu : u ∈ ball (0 : ℂ) a⁻¹) (hu0 : u ≠ 0) : G u = 0 := by
    have he : u ^ m * G u = 0 := by
      simpa only [zero_pow hm.ne', zero_mul] using hHconst hu
    exact (mul_eq_zero.mp he).resolve_left (pow_ne_zero m hu0)
  have h0 : (0 : ℂ) ∈ ball (0 : ℂ) a⁻¹ := by
    simpa only [mem_ball, dist_self] using inv_pos.mpr ha
  have hlim : Tendsto G (𝓝[≠] (0 : ℂ)) (𝓝 (G 0)) :=
    (hG 0 h0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hzero : G =ᶠ[𝓝[≠] (0 : ℂ)] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds h0)] with u hu0 hu
    exact hGoff u hu hu0
  have hG0 : G 0 = 0 := tendsto_nhds_unique hlim (tendsto_const_nhds.congr' hzero.symm)
  refine ⟨hfinite, fun u hu => ?_⟩
  by_cases hu0 : u = 0
  · simpa only [hu0] using hG0
  · exact hGoff u hu hu0

end Wikipedia.HopfProblem.HolomorphicCousin
