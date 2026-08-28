import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisInverseApplicationIdentity
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeBasePrimitive

/-!
# One original neighborhood for the inverse modes and the base mean primitive

Intersect the genuinely proved inverse neighborhood with the genuine
Cauchy--Green neighborhood for the original base coefficient. All data
remain literal restrictions of the original functions. The resulting
single neighborhood supports both parts of the local primitive.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy

open FourierSynthesis FourierParameter RelativeFourier PeriodTorusLineBundleClassification

/-- Restrict the actual polynomial multiplier estimates without changing
any original coefficient or derivative word. -/
theorem multiplier_mono {U V : Opens ℂ} {m : Coefficients}
    (hm : SmoothPolynomiallyBoundedCoefficients U m) (hVU : V ≤ U) :
    SmoothPolynomiallyBoundedCoefficients V m where
  smooth k := (hm.smooth k).mono hVU
  growth := by
    intro s K hK
    let i : V → U := Set.inclusion hVU
    obtain ⟨C, n, hC, hbound⟩ := hm.growth s (i '' K)
      (hK.image (continuous_inclusion hVU))
    exact ⟨C, n, hC, fun b hb k => hbound (i b) (Set.mem_image_of_mem i hb) k⟩

/-- The original inverse equations, holomorphic inverse, rapid-multiplier
estimates, and actual scalar mean primitive hold on one genuine neighborhood. -/
theorem exists_open_inverse_and_mean_primitive {U : Opens ℂ}
    (P : HolomorphicPeriodMap ℂ U) (a₀ : SmoothFamily U (Fin 4)) (b₀ : U) :
    ∃ V : Opens ℂ, ∃ hVU : V ≤ U, (b₀ : ℂ) ∈ V ∧
      SmoothPolynomiallyBoundedCoefficients V (ambientInverse P (P.point b₀)) ∧
      (∀ k : Frequency, DifferentiableOn ℂ (ambientInverse P (P.point b₀) k) V) ∧
      (∀ (b : V) (k : Frequency), k ≠ 0 →
        centreCoefficient (P.point b₀) (P.point (Set.inclusion hVU b)) (integerFrequency k) *
          ambientInverse P (P.point b₀) k (b : ℂ) = 1) ∧
      ∃ u : ℂ → ℂ, ContDiff ℝ ∞ u ∧
        ∀ b : V, (fderiv ℝ u (b : ℂ) 1 + Complex.I * fderiv ℝ u (b : ℂ) Complex.I) / 2 =
          a₀.coefficientValue 0 (b : ℂ) := by
  obtain ⟨V₁, hV₁U, hb₁, hm, hhol, hinverse, _⟩ :=
    FourierSynthesisInverse.exists_open_inverse_identity_data P b₀
  obtain ⟨V₂, _, hb₂, u, hu, hprimitive⟩ :=
    RelativeBasePrimitive.exists_local_mean_primitive a₀ b₀
  let V : Opens ℂ := V₁ ⊓ V₂
  have hV₁ : V ≤ V₁ := inf_le_left
  have hV₂ : V ≤ V₂ := inf_le_right
  have hVU : V ≤ U := hV₁.trans hV₁U
  refine ⟨V, hVU, ⟨hb₁, hb₂⟩, multiplier_mono hm hV₁,
    fun k => (hhol k).mono hV₁, ?_, u, hu, ?_⟩
  · intro b k hk
    exact hinverse (Set.inclusion hV₁ b) k hk
  · intro b
    exact hprimitive (Set.inclusion hV₂ b)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeHomotopy
