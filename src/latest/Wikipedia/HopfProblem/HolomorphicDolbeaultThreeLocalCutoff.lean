import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeBasic
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

/-!
# Smooth cutoff representatives for the local three-dimensional lemma

Each coefficient is extended separately.  The resulting functions are
smooth globally, but closedness is preserved only as a germ, never
asserted away from the original open set.
-/

noncomputable section

open Complex Set Metric Filter
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local

/-- A smooth cutoff whose nonzero locus stays strictly within the larger
disc and which equals one throughout the smaller disc. -/
theorem exists_coordinate_cutoff (x : ℂ) {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ χ : ℂ → ℂ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ z ∈ ball x r, χ z = 1) ∧ ∀ z, χ z ≠ 0 → z ∈ ball x R := by
  let b : ContDiffBump x :=
    { rIn := r
      rOut := R
      rIn_pos := hr
      rIn_lt_rOut := hrR }
  refine ⟨fun z => (b z : ℂ), Complex.ofRealCLM.contDiff.comp b.contDiff,
    b.hasCompactSupport.comp_left Complex.ofReal_zero, ?_, ?_⟩
  · intro z hz
    dsimp only
    rw [b.one_of_mem_closedBall (ball_subset_closedBall hz), Complex.ofReal_one]
  · intro z hz
    have hb : z ∈ Function.support b := by
      intro he
      apply hz
      change (b z : ℂ) = 0
      rw [he, Complex.ofReal_zero]
    simpa only [b.support_eq] using hb

/-- A genuine compactly supported smooth representative of a function germ
on a finite-dimensional real normed space. -/
theorem exists_compact_smooth_representative
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {U : Set E} (hU : IsOpen U) {g : E → ℂ} (hg : ContDiffOn ℝ ∞ g U)
    {x : E} (hx : x ∈ U) :
    ∃ v : E → ℂ, ContDiff ℝ ∞ v ∧ HasCompactSupport v ∧ v =ᶠ[𝓝 x] g := by
  obtain ⟨r, hr, hrU⟩ := Metric.isOpen_iff.mp hU x hx
  let b : ContDiffBump x :=
    { rIn := r / 4
      rOut := r / 2
      rIn_pos := by positivity
      rIn_lt_rOut := by linarith }
  let v : E → ℂ := fun z => (b z : ℂ) * g z
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

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Local
