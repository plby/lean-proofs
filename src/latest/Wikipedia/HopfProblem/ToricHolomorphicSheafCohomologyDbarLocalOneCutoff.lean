import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationDbar
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Compact smooth representatives of actual two-variable germs

The cutoff extension preserves the germ of each coefficient separately.
No closedness condition is imposed on the extensions away from that germ.
-/

noncomputable section

open Complex Set Metric Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DbarLocalOne

open HolomorphicCousin PeriodTorusLineBundleClassification

theorem exists_compact_smooth_representative {U : Set (ℂ × ℂ)} (hU : IsOpen U)
    {g : ℂ × ℂ → ℂ} (hg : ContDiffOn ℝ ∞ g U) {x : ℂ × ℂ} (hx : x ∈ U) :
    ∃ v : ℂ × ℂ → ℂ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧ v =ᶠ[𝓝 x] g := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hx
  let b : ContDiffBump x :=
    { rIn := r / 4
      rOut := r / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let v : ℂ × ℂ → ℂ := fun z => (b z : ℂ) * g z
  have hbU : tsupport b ⊆ U := by
    intro z hz
    rw [b.tsupport_eq] at hz
    apply hrU
    exact lt_of_le_of_lt hz (by change r / 2 < r; linarith)
  have hb : ContDiff ℝ ∞ (fun z => (b z : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp b.contDiff
  have hv : ContDiff ℝ ∞ v := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport b
    · exact hb.contDiffAt.mul ((hg z (hbU hz)).contDiffAt (hU.mem_nhds (hbU hz)))
    · have he : v =ᶠ[𝓝 z] (fun _ => 0) := by
        filter_upwards [(isClosed_tsupport b).isOpen_compl.mem_nhds hz] with w hw
        simp only [v, image_eq_zero_of_notMem_tsupport hw, Complex.ofReal_zero, zero_mul]
      exact contDiffAt_const.congr_of_eventuallyEq he
  have hc : HasCompactSupport v :=
    (b.hasCompactSupport.comp_left Complex.ofReal_zero).mul_right
  refine ⟨v, hv, hc, ?_⟩
  filter_upwards [Metric.ball_mem_nhds x b.rIn_pos] with z hz
  simp only [v, b.one_of_mem_closedBall (Metric.ball_subset_closedBall hz),
    Complex.ofReal_one, one_mul]

theorem dbarFirst_eq_of_eventuallyEq {f g : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (he : f =ᶠ[𝓝 q] g) : dbarFirst f q = dbarFirst g q := by
  have ht : Tendsto (fun z : ℂ => (z, q.2)) (𝓝 q.1) (𝓝 q) :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hs := he.comp_tendsto ht
  have hd : fderiv ℝ (fun z => f (z, q.2)) q.1 =
      fderiv ℝ (fun z => g (z, q.2)) q.1 := hs.fderiv_eq
  unfold dbarFirst dbar
  rw [hd]

theorem dbarSecond_eq_of_eventuallyEq {f g : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (he : f =ᶠ[𝓝 q] g) : dbarSecond f q = dbarSecond g q := by
  have ht : Tendsto (fun w : ℂ => (q.1, w)) (𝓝 q.2) (𝓝 q) :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hs := he.comp_tendsto ht
  have hd : fderiv ℝ (fun w => f (q.1, w)) q.2 =
      fderiv ℝ (fun w => g (q.1, w)) q.2 := hs.fderiv_eq
  unfold dbarSecond dbar
  rw [hd]

theorem dbarFirst_eventuallyEq {f g : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (he : f =ᶠ[𝓝 q] g) : dbarFirst f =ᶠ[𝓝 q] dbarFirst g :=
  he.eventuallyEq_nhds.mono (fun _ h => dbarFirst_eq_of_eventuallyEq h)

theorem dbarSecond_eventuallyEq {f g : ℂ × ℂ → ℂ} {q : ℂ × ℂ}
    (he : f =ᶠ[𝓝 q] g) : dbarSecond f =ᶠ[𝓝 q] dbarSecond g :=
  he.eventuallyEq_nhds.mono (fun _ h => dbarSecond_eq_of_eventuallyEq h)

/-- A centered cutoff with both its inner radius and outer support radius
specified. -/
theorem exists_complex_cutoff_between (x : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ χ : ℂ → ℂ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ z ∈ closedBall x r, χ z = 1) ∧
      ∀ z, χ z ≠ 0 → z ∈ closedBall x R := by
  let b : ContDiffBump x :=
    { rIn := r
      rOut := R
      rIn_pos := hr
      rIn_lt_rOut := hrR }
  refine ⟨fun z => (b z : ℂ), Complex.ofRealCLM.contDiff.comp b.contDiff,
    b.hasCompactSupport.comp_left Complex.ofReal_zero, ?_, ?_⟩
  · intro z hz
    dsimp only
    rw [b.one_of_mem_closedBall hz, Complex.ofReal_one]
  · intro z hz
    have hn : b z ≠ 0 := by
      intro he
      apply hz
      change (b z : ℂ) = 0
      rw [he, Complex.ofReal_zero]
    have hs := subset_tsupport b hn
    rwa [b.tsupport_eq] at hs

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DbarLocalOne
