import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLaurentScalar
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyLaurentParametric

/-!
# Actual holomorphic Laurent splitting on `ℂ × ℂ*`

The two summands are constructed by actual Cauchy integrals. Radius
independence and the joint analytic fixed-contour formulas prove that both
are holomorphic on all of `ℂ²`. The reciprocal-coordinate summand vanishes
on the zero section. This is an analytic splitting theorem, not a definition
or an assumed vanishing statement for sheaf cohomology.
-/

noncomputable section

open Complex Set Metric Filter
open scoped Topology

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.Laurent

open HolomorphicCousin

def parametricPositivePart (f : ℂ × ℂ → ℂ) (q : ℂ × ℂ) : ℂ :=
  positivePart (fun w => f (q.1, w)) q.2

def parametricNegativePart (f : ℂ × ℂ → ℂ) (q : ℂ × ℂ) : ℂ :=
  negativePart (fun w => f (q.1, w)) q.2

theorem parametricPositivePart_analytic {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {q | q.2 ≠ 0}) :
    AnalyticOnNhd ℂ (parametricPositivePart f) univ := by
  intro q _
  let r : ℝ := ‖q.1‖ + 1
  let R : ℝ := ‖q.2‖ + 1
  have hr : 0 < r := by dsimp only [r]; positivity
  have hR : 0 < R := by dsimp only [R]; positivity
  have hqr : q.1 ∈ ball (0 : ℂ) r := by
    simpa only [mem_ball, dist_zero_right] using lt_add_one ‖q.1‖
  have hqR : q.2 ∈ ball (0 : ℂ) R := by
    simpa only [mem_ball, dist_zero_right] using lt_add_one ‖q.2‖
  apply (positiveContour_analyticOnNhd hf hr hR q ⟨hqr, hqR⟩).congr
  have hnear : {p : ℂ × ℂ | p.2 ∈ ball (0 : ℂ) R} ∈ 𝓝 q :=
    (isOpen_ball.preimage continuous_snd).mem_nhds hqR
  filter_upwards [hnear] with p hp
  exact (positivePart_eq_contour (secondSlice_analytic hf p.1) hR
    (by simpa only [mem_ball, dist_zero_right] using hp : ‖p.2‖ < R)).symm

theorem parametricNegativePart_analytic {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {q | q.2 ≠ 0}) :
    AnalyticOnNhd ℂ (parametricNegativePart f) univ := by
  intro q _
  let r : ℝ := ‖q.1‖ + 1
  let R : ℝ := (‖q.2‖ + 1)⁻¹
  have hr : 0 < r := by dsimp only [r]; positivity
  have hR : 0 < R := by dsimp only [R]; positivity
  have hqr : q.1 ∈ ball (0 : ℂ) r := by
    simpa only [mem_ball, dist_zero_right] using lt_add_one ‖q.1‖
  have hqR : q.2 ∈ ball (0 : ℂ) R⁻¹ := by
    simpa only [mem_ball, dist_zero_right, R, inv_inv] using lt_add_one ‖q.2‖
  apply ((reciprocalContour_analyticOnNhd hf hr hR q ⟨hqr, hqR⟩).neg).congr
  have hnear : {p : ℂ × ℂ | p.2 ∈ ball (0 : ℂ) R⁻¹} ∈ 𝓝 q :=
    (isOpen_ball.preimage continuous_snd).mem_nhds hqR
  filter_upwards [hnear] with p hp
  exact (negativePart_eq_contour (secondSlice_analytic hf p.1) hR
    (by simpa only [mem_ball, dist_zero_right] using hp : ‖p.2‖ < R⁻¹)).symm

@[simp] theorem parametricNegativePart_zero (f : ℂ × ℂ → ℂ) (z : ℂ) :
    parametricNegativePart f (z, 0) = 0 := negativePart_zero _

theorem parametricPositivePart_add_negativePart_inv {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {q | q.2 ≠ 0}) (z : ℂ) {w : ℂ} (hw : w ≠ 0) :
    parametricPositivePart f (z, w) + parametricNegativePart f (z, w⁻¹) = f (z, w) :=
  positivePart_add_negativePart_inv (secondSlice_analytic hf z) hw

/-- **Holomorphic Laurent splitting on `ℂ × ℂ*`.** Both summands extend
holomorphically to the whole two-dimensional complex vector space. -/
theorem exists_entire_parametric_splitting {f : ℂ × ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f {q | q.2 ≠ 0}) :
    ∃ fPlus fMinus : ℂ × ℂ → ℂ,
      AnalyticOnNhd ℂ fPlus univ ∧ AnalyticOnNhd ℂ fMinus univ ∧
      (∀ z, fMinus (z, 0) = 0) ∧
      ∀ z w, w ≠ 0 → f (z, w) = fPlus (z, w) + fMinus (z, w⁻¹) := by
  exact ⟨parametricPositivePart f, parametricNegativePart f,
    parametricPositivePart_analytic hf, parametricNegativePart_analytic hf,
    parametricNegativePart_zero f,
    fun z _ hw => (parametricPositivePart_add_negativePart_inv hf z hw).symm⟩

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.Laurent
