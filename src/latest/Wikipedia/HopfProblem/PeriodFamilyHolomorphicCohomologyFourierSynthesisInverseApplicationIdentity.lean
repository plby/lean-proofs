import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisInverseApplicationBasic

/-!
# One original neighborhood with smooth inverse growth and actual inverse identities

Intersect the previously proved multiplier neighborhood with the original
native neighborhood carrying the selected-denominator lower bound. The
unchanged ambient inverse is then smooth with polynomial derivative
growth and holomorphic on this one open set. Its genuine selected
denominator cancels it at every nonzero integer mode, while its zero mode
vanishes. No input family or coefficient estimate enters the neighborhood
choice.
-/

noncomputable section

open TopologicalSpace

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisInverse

open FourierSynthesis PeriodTorusLineBundleClassification

/-- Restriction preserves the original ambient multiplier and all its derivative words. -/
private theorem polynomial_multiplier_restrict {A V : Opens ℂ} {m : Coefficients}
    (hm : SmoothPolynomiallyBoundedCoefficients A m) (hVA : V ≤ A) :
    SmoothPolynomiallyBoundedCoefficients V m where
  smooth k := (hm.smooth k).mono hVA
  growth := by
    intro s K hK
    let i : V → A := Set.inclusion hVA
    have hi : Continuous i := continuous_inclusion hVA
    obtain ⟨C, n, hC, hbound⟩ := hm.growth s (i '' K) (hK.image hi)
    exact ⟨C, n, hC, fun b hb k => hbound (i b) (Set.mem_image_of_mem i hb) k⟩

variable {U : Opens ℂ} (P : HolomorphicPeriodMap ℂ U)

/-- One original neighborhood carries smooth growth, holomorphicity, and the inverse equations. -/
theorem exists_open_inverse_identity_data (b₀ : U) :
    ∃ V : Opens ℂ, ∃ hVU : V ≤ U, (b₀ : ℂ) ∈ V ∧
      SmoothPolynomiallyBoundedCoefficients V
        (RelativeFourier.ambientInverse P (P.point b₀)) ∧
      (∀ k : Fin 4 → ℤ,
        DifferentiableOn ℂ (RelativeFourier.ambientInverse P (P.point b₀) k) V) ∧
      (∀ (b : V) (k : Fin 4 → ℤ), k ≠ 0 →
        RelativeFourier.centreCoefficient (P.point b₀)
            (P.point (Set.inclusion hVU b)) (integerFrequency k) *
          RelativeFourier.ambientInverse P (P.point b₀) k (b : ℂ) = 1) ∧
      (∀ b : V, RelativeFourier.ambientInverse P (P.point b₀) 0 (b : ℂ) = 0) := by
  obtain ⟨V₀, hb₀, hV₀U, hm⟩ := exists_open_inverse_multiplier P b₀
  obtain ⟨W, c, hW, hbW, hc, hbound, hhol, _⟩ :=
    RelativeFourier.exists_open_uniform_holomorphic_inverse P b₀
  let W' : Opens ℂ :=
    ⟨(Subtype.val : U → ℂ) '' W, U.isOpen.isOpenMap_subtype_val _ hW⟩
  let V : Opens ℂ := V₀ ⊓ W'
  have hVV₀ : V ≤ V₀ := inf_le_left
  have hVW' : V ≤ W' := inf_le_right
  have hVU : V ≤ U := hVV₀.trans hV₀U
  refine ⟨V, hVU, ?_, polynomial_multiplier_restrict hm hVV₀, ?_, ?_, ?_⟩
  · exact ⟨hb₀, ⟨b₀, hbW, rfl⟩⟩
  · intro k
    exact (RelativeFourier.ambientInverse_differentiableOn_image P (P.point b₀) k
      W hW (hhol (integerFrequency k))).mono hVW'
  · intro b k hk
    let bU : U := Set.inclusion hVU b
    have hbUW : bU ∈ W := by
      obtain ⟨a, ha, haeq⟩ := hVW' b.property
      have heq : a = bU := Subtype.ext haeq
      exact heq ▸ ha
    change RelativeFourier.centreCoefficient (P.point b₀) (P.point bU)
        (integerFrequency k) * RelativeFourier.ambientInverse P (P.point b₀) k (bU : ℂ) = 1
    rw [RelativeFourier.ambientInverse_apply]
    exact RelativeFourier.centreCoefficient_mul_denominatorInverse (P.point b₀) (P.point bU)
      (integerFrequency k)
      (RelativeFourier.centreCoefficient_ne_zero_of_lowerBound (P.point b₀) (P.point bU)
        c hc (integerFrequency_ne_zero hk) (hbound bU hbUW (integerFrequency k)))
  · intro b
    rw [RelativeFourier.ambientInverse_apply P (P.point b₀) 0 (Set.inclusion hVU b),
      integerFrequency_zero,
      RelativeFourier.denominatorInverse_zero]

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesisInverse
