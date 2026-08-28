import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisDerivativeBounds
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisSeriesBasic

/-!
# Differentiating the original parameterized Fourier sum

A closed base disc inside the given open set supplies the compact-uniform
derivative majorant. The genuine series theorem then differentiates the
literal Fourier sum on its product with the real covering space. Thus its
actual Fréchet derivative is the convergent sum of the original mode
derivatives, with no assumed regularity of the infinite sum.
-/

noncomputable section

open TopologicalSpace UnitAddTorus

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

/-- The actual joint Fourier sum is differentiable, with the original
termwise Fréchet derivative. -/
theorem hasFDerivAt_jointSynthesis {U : Opens ℂ} {c : Coefficients}
    (hc : SmoothRapidCoefficients U c) (x : ℂ × (Fin 4 → ℝ)) (hx : x.1 ∈ U) :
    HasFDerivAt (jointSynthesis c) (∑' k, jointFourierModeDerivative c k x) x := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp U.isOpen x.1 hx
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hrε : r < ε := half_lt_self hε
  have hclosed : Metric.closedBall x.1 r ⊆ U :=
    (Metric.closedBall_subset_ball hrε).trans hball
  let K : Set U := (Subtype.val : U → ℂ) ⁻¹' Metric.closedBall x.1 r
  have hK : IsCompact K :=
    Topology.IsInducing.subtypeVal.isCompact_preimage' (isCompact_closedBall x.1 r)
      (by simpa only [Subtype.range_coe] using hclosed)
  obtain ⟨u, _, hsum, hbound⟩ := jointFourierModeDerivative_majorant hc K hK
  let S : Set (ℂ × (Fin 4 → ℝ)) := Metric.ball x.1 r ×ˢ Set.univ
  have hSU (y : ℂ × (Fin 4 → ℝ)) (hy : y ∈ S) : y.1 ∈ U :=
    hclosed (Metric.ball_subset_closedBall hy.1)
  have hxS : x ∈ S := ⟨Metric.mem_ball_self hr, Set.mem_univ x.2⟩
  exact hasFDerivAt_tsum_of_isPreconnected hsum
    (Metric.isOpen_ball.prod isOpen_univ)
    ((convex_ball x.1 r).isPreconnected.prod isPreconnected_univ)
    (fun k y hy => hasFDerivAt_jointFourierMode_of_smoothRapid hc k y (hSU y hy))
    (fun k y hy => hbound ⟨y.1, hSU y hy⟩
      (Metric.ball_subset_closedBall hy.1) y.2 k)
    hxS (summable_jointFourierMode hc x hx) hxS

/-- Evaluating the genuine derivative in a fixed real direction gives
the literal Fourier synthesis of the differentiated coefficients. -/
theorem jointSynthesis_fderiv_apply {U : Opens ℂ} {c : Coefficients}
    (hc : SmoothRapidCoefficients U c) (x v : ℂ × (Fin 4 → ℝ)) (hx : x.1 ∈ U) :
    fderiv ℝ (jointSynthesis c) x v = jointSynthesis (jointDerivativeCoefficients v c) x := by
  rw [(hasFDerivAt_jointSynthesis hc x hx).fderiv]
  calc
    (∑' k, jointFourierModeDerivative c k x) v =
        ∑' k, jointFourierModeDerivative c k x v :=
      (ContinuousLinearMap.apply ℝ ℂ v).map_tsum
        (summable_jointFourierModeDerivative hc x hx)
    _ = jointSynthesis (jointDerivativeCoefficients v c) x := by
      apply tsum_congr
      intro k
      exact jointFourierModeDerivative_apply_coefficients c k x v

/-- No regularity premise on the infinite sum is needed for its actual
differentiability throughout the original base product. -/
theorem jointSynthesis_differentiableOn {U : Opens ℂ} {c : Coefficients}
    (hc : SmoothRapidCoefficients U c) :
    DifferentiableOn ℝ (jointSynthesis c) (Smooth.baseProductDomain U (Fin 4 → ℝ)) :=
  fun x hx => (hasFDerivAt_jointSynthesis hc x hx).differentiableAt.differentiableWithinAt

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis
