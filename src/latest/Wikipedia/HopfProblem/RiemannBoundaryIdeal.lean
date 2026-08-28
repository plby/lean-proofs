import Wikipedia.HopfProblem.RiemannBoundaryConformal
import Wikipedia.HopfProblem.RiemannBoundaryInfinity

/-!
# The ideal vertex of a half-strip

The logarithmic coordinate unfolds the ideal vertex. Its finite real
boundary values lie on the two sides of the strip, while its parameter
zero escapes to infinity. Properness proves the unit-modulus limit in both
cases; the reflected extension is analytic and noncritical at zero.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology ComplexConjugate

namespace Wikipedia.HopfProblem.RiemannBoundary

/-- The principal logarithm is continuous from the closed upper
half-plane at every nonzero point, including its negative real boundary. -/
theorem continuousWithinAt_log_closedUpper {q : ℂ} (hq : q ≠ 0) :
    ContinuousWithinAt log {z : ℂ | 0 ≤ z.im} q := by
  by_cases hi : q.im = 0
  · by_cases hr : 0 < q.re
    · exact (continuousAt_clog (Or.inl hr)).continuousWithinAt
    · have hre : q.re < 0 := by
        have hne : q.re ≠ 0 := by
          intro heq
          apply hq
          exact Complex.ext heq hi
        exact lt_of_le_of_ne (le_of_not_gt hr) hne
      exact continuousWithinAt_log_of_re_neg_of_im_zero hre hi
  · exact (continuousAt_clog (Or.inr hi)).continuousWithinAt

theorem continuousWithinAt_logHalfStrip_closedUpper (a c : ℝ) {q : ℂ} (hq : q ≠ 0) :
    ContinuousWithinAt (logHalfStrip a c) {z : ℂ | 0 ≤ z.im} q := by
  exact continuousWithinAt_const.sub
    (continuousWithinAt_const.mul (continuousWithinAt_log_closedUpper hq))

theorem analyticOnNhd_logHalfStrip_upper (a c : ℝ) :
    AnalyticOnNhd ℂ (logHalfStrip a c) {z : ℂ | 0 < z.im} := by
  intro q hq
  exact analyticAt_const.sub
    (analyticAt_const.mul (analyticAt_clog (Or.inr (ne_of_gt hq))))

theorem logHalfStrip_re_mem_Ioo (a : ℝ) {c : ℝ} (hc : 0 < c) {q : ℂ}
    (hq : 0 < q.im) : (logHalfStrip a c q).re ∈ Ioo a (a + c * Real.pi) := by
  have harg0 : q.arg ≠ 0 := fun h => (ne_of_gt hq) (arg_eq_zero_iff.mp h).2
  have harg : 0 < q.arg := lt_of_le_of_ne (arg_nonneg_iff.mpr hq.le) harg0.symm
  have hargπ : q.arg < Real.pi := arg_lt_pi_iff.mpr (Or.inr (ne_of_gt hq))
  rw [logHalfStrip_re]
  constructor <;> nlinarith

theorem logHalfStrip_real_re (a c : ℝ) (t : ℝ) :
    (logHalfStrip a c (t : ℂ)).re = a ∨
      (logHalfStrip a c (t : ℂ)).re = a + c * Real.pi := by
  by_cases ht : 0 ≤ t
  · left
    simp [logHalfStrip_re, arg_ofReal_of_nonneg ht]
  · right
    simp [logHalfStrip_re, arg_ofReal_of_neg (lt_of_not_ge ht)]

/-- A sufficiently small punctured parameter disk maps above every
specified horizontal level under the logarithmic half-strip chart. -/
theorem exists_logHalfStrip_height_radius (a B : ℝ) {c : ℝ} (hc : 0 < c) :
    ∃ R > 0, ∀ q ∈ ball (0 : ℂ) R, q ≠ 0 → B < (logHalfStrip a c q).im := by
  have ht : ∀ᶠ q in 𝓝[≠] (0 : ℂ), B < (logHalfStrip a c q).im :=
    (tendsto_logHalfStrip_im_atTop a hc).eventually_gt_atTop B
  obtain ⟨R, hR, hs⟩ := Metric.mem_nhdsWithin_iff.mp ht
  exact ⟨R, hR, fun q hq hne => hs ⟨hq, hne⟩⟩

/-- **Conformal extension at the ideal vertex.** The source domain is
only required to contain an actual high half-strip and exclude its two
vertical sides. All boundary norm limits and the nonzero derivative at
the filled ideal vertex are proved, rather than assumed. -/
theorem exists_conformal_extension_discHomeomorph_at_ideal_vertex
    {D : Set ℂ} (e : D ≃ₜ ball (0 : ℂ) 1) {f : ℂ → ℂ}
    (he : ∀ z : D, f z = (e z : ℂ)) (hf : DifferentiableOn ℂ f D)
    (a B : ℝ) {c : ℝ} (hc : 0 < c)
    (hstrip : ∀ z : ℂ, a < z.re → z.re < a + c * Real.pi → B < z.im → z ∈ D)
    (hedge : ∀ z : ℂ, B < z.im → (z.re = a ∨ z.re = a + c * Real.pi) → z ∉ D) :
    ∃ r > 0, ∃ H : ℂ → ℂ,
      AnalyticOnNhd ℂ H (ball (0 : ℂ) r) ∧
      EqOn H (f ∘ logHalfStrip a c) (ball (0 : ℂ) r ∩ {z : ℂ | 0 < z.im}) ∧
      EqOn H (fun z => (conj (f (logHalfStrip a c (conj z))))⁻¹)
        (ball (0 : ℂ) r ∩ {z : ℂ | z.im < 0}) ∧
      (∀ t : ℝ, (t : ℂ) ∈ ball (0 : ℂ) r → ‖H (t : ℂ)‖ = 1) ∧
      HasStrictDerivAt H (deriv H 0) 0 ∧ deriv H 0 ≠ 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℂ), ‖H z‖ < 1 ↔ 0 < z.im := by
  obtain ⟨R, hR, hheight⟩ := exists_logHalfStrip_height_radius a B hc
  let U : Set ℂ := ball (0 : ℂ) R
  have hU : IsOpen U := isOpen_ball
  have h0U : (0 : ℂ) ∈ U := mem_ball_self hR
  have hside : MapsTo (logHalfStrip a c) (U ∩ {z : ℂ | 0 < z.im}) D := by
    intro q hq
    have hq0 : q ≠ 0 := by
      intro heq
      have hi := hq.2
      rw [heq] at hi
      exact (lt_irrefl (0 : ℝ)) hi
    have hRe := logHalfStrip_re_mem_Ioo a hc hq.2
    exact hstrip _ hRe.1 hRe.2 (hheight q hq.1 hq0)
  have hφ : DifferentiableOn ℂ (logHalfStrip a c) (U ∩ {z : ℂ | 0 < z.im}) :=
    (analyticOnNhd_logHalfStrip_upper a c).differentiableOn.mono inter_subset_right
  have hdiff : DifferentiableOn ℂ (f ∘ logHalfStrip a c)
      (U ∩ {z : ℂ | 0 < z.im}) := hf.comp hφ hside
  have hmod : ∀ t : ℝ, (t : ℂ) ∈ U →
      Tendsto (fun q => ‖f (logHalfStrip a c q)‖)
        (𝓝[{z : ℂ | 0 < z.im}] (t : ℂ)) (𝓝 1) := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      apply tendsto_norm_discHomeomorph_logHalfStrip e he a hc
      have hnear : U ∈ 𝓝[{z : ℂ | 0 < z.im}] (0 : ℂ) :=
        mem_nhdsWithin_of_mem_nhds (hU.mem_nhds h0U)
      filter_upwards [hnear, self_mem_nhdsWithin] with q hq hi
      exact hside ⟨hq, hi⟩
    · let V : Set ℂ := U \ {0}
      have hV : IsOpen V := hU.sdiff isClosed_singleton
      have htC : (t : ℂ) ≠ 0 := ofReal_ne_zero.mpr ht0
      have htV : (t : ℂ) ∈ V := ⟨ht, htC⟩
      have hcont : ContinuousOn (logHalfStrip a c) (V ∩ {z : ℂ | 0 ≤ z.im}) := by
        intro q hq
        exact (continuousWithinAt_logHalfStrip_closedUpper a c hq.1.2).mono
          inter_subset_right
      have hsideV : MapsTo (logHalfStrip a c) (V ∩ {z : ℂ | 0 < z.im}) D := by
        intro q hq
        exact hside ⟨hq.1.1, hq.2⟩
      exact tendsto_norm_discHomeomorph_in_boundary_chart e he hV hcont hsideV htV
        (hedge _ (hheight _ ht htC) (logHalfStrip_real_re a c t))
  apply exists_conformal_extension_of_modulus_one hU h0U hdiff hmod
  intro q hq
  have hp := hside hq
  have hv := he ⟨logHalfStrip a c q, hp⟩
  simpa only [Function.comp_def, mem_ball, dist_zero_right, ← hv] using
    (e ⟨logHalfStrip a c q, hp⟩).property

end Wikipedia.HopfProblem.RiemannBoundary
