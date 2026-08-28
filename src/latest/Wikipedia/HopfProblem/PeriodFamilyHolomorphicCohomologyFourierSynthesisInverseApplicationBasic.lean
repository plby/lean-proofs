import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisInverse
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisCoefficientsProductBasic

/-!
# The genuine selected inverse satisfies the multiplier condition

The original inverse-mode estimates give polynomial growth of degree zero
for every real derivative word on one common base disc. The multiplier is
the unchanged ambient inverse of the original period family and original
centre selector. No multiplier regularity or growth hypothesis is added.
-/

noncomputable section

open TopologicalSpace Metric

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisInverse

open FourierSynthesis

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- The genuine selected inverse is a smooth polynomial multiplier on one original
base disc. Each growth witness has degree zero, by the proved uniform real-word bound. -/
theorem exists_disc_inverse_multiplier (b₀ : U) :
    ∃ r : ℝ, 0 < r ∧ closedBall (b₀ : ℂ) (3 * r) ⊆ U ∧
      SmoothPolynomiallyBoundedCoefficients ⟨ball (b₀ : ℂ) r, isOpen_ball⟩
        (RelativeFourier.ambientInverse P (P.point b₀)) := by
  obtain ⟨r, hr, hbase, hsmooth, hbound⟩ := exists_disc_smooth_uniform_inverse P b₀
  refine ⟨r, hr, hbase, ⟨hsmooth, ?_⟩⟩
  intro s K _
  obtain ⟨C, hC, hword⟩ := hbound s
  refine ⟨C, 0, hC, ?_⟩
  intro b _ k
  simpa only [pow_zero, mul_one] using hword (b : ℂ) b.property k

/-- Open-subtype form for synthesis on the original base, using the literal original
ambient inverse and a neighborhood that does not depend on any input coefficients. -/
theorem exists_open_inverse_multiplier (b₀ : U) :
    ∃ V : Opens ℂ, (b₀ : ℂ) ∈ V ∧ V ≤ U ∧
      SmoothPolynomiallyBoundedCoefficients V
        (RelativeFourier.ambientInverse P (P.point b₀)) := by
  obtain ⟨r, hr, hbase, hmult⟩ := exists_disc_inverse_multiplier P b₀
  refine ⟨⟨ball (b₀ : ℂ) r, isOpen_ball⟩, mem_ball_self hr, ?_, hmult⟩
  intro z hz
  exact hbase (closedBall_subset_closedBall (by linarith) (ball_subset_closedBall hz))

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisInverse
