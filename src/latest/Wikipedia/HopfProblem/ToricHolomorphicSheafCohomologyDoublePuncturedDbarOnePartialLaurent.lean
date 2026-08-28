import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDoublePuncturedDbarOneContours
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLaurent

/-!
# Actual partial Laurent splitting on `(ℂ*)²`

The second-coordinate Laurent parts extend holomorphically over the
second axis while the first coordinate remains punctured. The parts are
the same actual Cauchy integrals used in the global one-puncture theorem;
only the open parameter domain is changed.
-/

noncomputable section

open Set Metric Filter Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarOne

open HolomorphicCousin Laurent

theorem positiveContour_openParameter_analytic {f : ℂ × ℂ → ℂ} {R : ℝ} {V : Set ℂ}
    (hR : 0 < R) (hV : IsOpen V)
    (hf : AnalyticOnNhd ℂ f (V ×ˢ sphere (0 : ℂ) R)) :
    AnalyticOnNhd ℂ (positiveContour f R) (V ×ˢ ball (0 : ℂ) R) := by
  have hs : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => f (p.2, p.1))
      (sphere (0 : ℂ) R ×ˢ V) := by
    intro q hq
    exact AnalyticAt.comp (f := fun p : ℂ × ℂ => (p.2, p.1))
      (hf (q.2, q.1) ⟨hq.2, hq.1⟩) (analyticAt_snd.prod analyticAt_fst)
  intro q hq
  exact AnalyticAt.comp (f := fun p : ℂ × ℂ => (p.2, p.1))
    (firstPositiveContour_analytic hR hV hs (q.2, q.1) ⟨hq.2, hq.1⟩)
    (analyticAt_snd.prod analyticAt_fst)

theorem reciprocalContour_openParameter_analytic {f : ℂ × ℂ → ℂ} {R : ℝ} {V : Set ℂ}
    (hR : 0 < R) (hV : IsOpen V)
    (hf : AnalyticOnNhd ℂ f (V ×ˢ sphere (0 : ℂ) R)) :
    AnalyticOnNhd ℂ (reciprocalContour f R) (V ×ˢ ball (0 : ℂ) R⁻¹) := by
  have hs : AnalyticOnNhd ℂ (fun p : ℂ × ℂ => f (p.2, p.1))
      (sphere (0 : ℂ) R ×ˢ V) := by
    intro q hq
    exact AnalyticAt.comp (f := fun p : ℂ × ℂ => (p.2, p.1))
      (hf (q.2, q.1) ⟨hq.2, hq.1⟩) (analyticAt_snd.prod analyticAt_fst)
  intro q hq
  exact AnalyticAt.comp (f := fun p : ℂ × ℂ => (p.2, p.1))
    (firstReciprocalContour_analytic hR hV hs (q.2, q.1) ⟨hq.2, hq.1⟩)
    (analyticAt_snd.prod analyticAt_fst)

theorem secondCircle_subset_domain {R : ℝ} (hR : 0 < R) :
    {z : ℂ | z ≠ 0} ×ˢ sphere (0 : ℂ) R ⊆ domain := by
  intro q hq
  have hn : ‖q.2‖ = R := by simpa only [mem_sphere, dist_zero_right] using hq.2
  exact ⟨hq.1, norm_pos_iff.mp (hn.symm ▸ hR)⟩

theorem secondSlice_analytic_of_first_ne {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f domain) {z : ℂ} (hz : z ≠ 0) :
    AnalyticOnNhd ℂ (fun w => f (z, w)) {w | w ≠ 0} := by
  intro w hw
  exact (hf (z, w) ⟨hz, hw⟩).curry_right

theorem partialPositivePart_analytic {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f domain) :
    AnalyticOnNhd ℂ (parametricPositivePart f) {q : ℂ × ℂ | q.1 ≠ 0} := by
  intro q hq
  let R : ℝ := ‖q.2‖ + 1
  have hR : 0 < R := by dsimp only [R]; positivity
  have hqR : q.2 ∈ ball (0 : ℂ) R := by
    simpa only [mem_ball, dist_zero_right] using lt_add_one ‖q.2‖
  have hV : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  apply (positiveContour_openParameter_analytic hR hV
    (hf.mono (secondCircle_subset_domain hR)) q ⟨hq, hqR⟩).congr
  have hnear₁ : {p : ℂ × ℂ | p.1 ≠ 0} ∈ 𝓝 q :=
    (isOpen_ne_fun continuous_fst continuous_const).mem_nhds hq
  have hnear₂ : {p : ℂ × ℂ | p.2 ∈ ball (0 : ℂ) R} ∈ 𝓝 q :=
    (isOpen_ball.preimage continuous_snd).mem_nhds hqR
  filter_upwards [hnear₁, hnear₂] with p hp₁ hp₂
  exact (positivePart_eq_contour (secondSlice_analytic_of_first_ne hf hp₁) hR
    (by simpa only [mem_ball, dist_zero_right] using hp₂ : ‖p.2‖ < R)).symm

theorem partialNegativePart_analytic {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f domain) :
    AnalyticOnNhd ℂ (parametricNegativePart f) {q : ℂ × ℂ | q.1 ≠ 0} := by
  intro q hq
  let R : ℝ := (‖q.2‖ + 1)⁻¹
  have hR : 0 < R := by dsimp only [R]; positivity
  have hqR : q.2 ∈ ball (0 : ℂ) R⁻¹ := by
    simpa only [mem_ball, dist_zero_right, R, inv_inv] using lt_add_one ‖q.2‖
  have hV : IsOpen {z : ℂ | z ≠ 0} := isOpen_ne_fun continuous_id continuous_const
  apply ((reciprocalContour_openParameter_analytic hR hV
    (hf.mono (secondCircle_subset_domain hR)) q ⟨hq, hqR⟩).neg).congr
  have hnear₁ : {p : ℂ × ℂ | p.1 ≠ 0} ∈ 𝓝 q :=
    (isOpen_ne_fun continuous_fst continuous_const).mem_nhds hq
  have hnear₂ : {p : ℂ × ℂ | p.2 ∈ ball (0 : ℂ) R⁻¹} ∈ 𝓝 q :=
    (isOpen_ball.preimage continuous_snd).mem_nhds hqR
  filter_upwards [hnear₁, hnear₂] with p hp₁ hp₂
  exact (negativePart_eq_contour (secondSlice_analytic_of_first_ne hf hp₁) hR
    (by simpa only [mem_ball, dist_zero_right] using hp₂ : ‖p.2‖ < R⁻¹)).symm

/-- Actual second-coordinate Laurent splitting while the first coordinate
remains punctured. The reciprocal part vanishes on the new zero section. -/
theorem exists_partial_second_splitting {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f domain) :
    ∃ p m : ℂ × ℂ → ℂ,
      AnalyticOnNhd ℂ p {q : ℂ × ℂ | q.1 ≠ 0} ∧
      AnalyticOnNhd ℂ m {q : ℂ × ℂ | q.1 ≠ 0} ∧
      (∀ x : ℂ, x ≠ 0 → m (x, 0) = 0) ∧
      ∀ x y : ℂ, x ≠ 0 → y ≠ 0 → f (x, y) = p (x, y) + m (x, y⁻¹) := by
  exact ⟨parametricPositivePart f, parametricNegativePart f,
    partialPositivePart_analytic hf, partialNegativePart_analytic hf,
    fun x _ => parametricNegativePart_zero f x,
    fun x y hx hy => (positivePart_add_negativePart_inv
      (secondSlice_analytic_of_first_ne hf hx) hy).symm⟩

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarOne
