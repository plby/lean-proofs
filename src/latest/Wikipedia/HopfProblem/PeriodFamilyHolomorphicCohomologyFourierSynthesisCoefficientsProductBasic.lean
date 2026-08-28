import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierSynthesisCoefficients

/-!
# Polynomially bounded coefficient multipliers on the original base

Every literal base-derivative word of a multiplier is required to have
compact-uniform polynomial frequency growth. Further base differentiation
preserves this condition by appending its direction to the original word.
Rapidly decreasing coefficients also restrict to a smaller base open by
mapping its compact subsets into the original open, without changing their
ambient functions or directional derivatives.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis

open FourierParameter PeriodTorusLineBundleClassification

local notation "word" => iteratedDirectionalDerivativeList

/-- Original smooth multiplier coefficients whose every real derivative word
has compact-uniform polynomial growth on the marked integer Fourier lattice. -/
structure SmoothPolynomiallyBoundedCoefficients (U : Opens ℂ) (m : Coefficients) : Prop where
  smooth : ∀ k, ContDiffOn ℝ ∞ (m k) U
  growth : ∀ (s : List ℂ) (K : Set U), IsCompact K →
    ∃ (C : ℝ) (n : ℕ), 0 ≤ C ∧ ∀ b ∈ K, ∀ k,
      ‖word s (m k) (b : ℂ)‖ ≤ C * (1 + ‖integerFrequency k‖) ^ n

variable {U : Opens ℂ} {m c : Coefficients}

/-- A further real base derivative preserves polynomial growth by the
unchanged tail-first word with its new direction appended on the right. -/
theorem SmoothPolynomiallyBoundedCoefficients.baseDiff
    (hm : SmoothPolynomiallyBoundedCoefficients U m) (v : ℂ) :
    SmoothPolynomiallyBoundedCoefficients U (baseDiff v m) where
  smooth k :=
    ((contDiffOn_infty_iff_fderiv_of_isOpen U.isOpen).mp (hm.smooth k)).2.clm_apply
      contDiffOn_const
  growth := by
    intro s K hK
    obtain ⟨C, n, hC, hbound⟩ := hm.growth (s ++ [v]) K hK
    refine ⟨C, n, hC, ?_⟩
    intro b hb k
    have hword : word (s ++ [v]) (m k) = word s (FourierSynthesis.baseDiff v m k) :=
      word_append s [v] (m k)
    rw [← hword]
    exact hbound b hb k

/-- Restrict the genuine rapid coefficient condition to a smaller base open.
The coefficient functions and every ambient derivative word remain unchanged. -/
theorem SmoothRapidCoefficients.mono (hc : SmoothRapidCoefficients U c)
    {V : Opens ℂ} (hVU : V ≤ U) : SmoothRapidCoefficients V c where
  smooth k := (hc.smooth k).mono hVU
  majorant := by
    intro s K hK r
    let i : V → U := Set.inclusion hVU
    have hi : Continuous i := continuous_inclusion hVU
    obtain ⟨u, hu, hsum, hbound⟩ := hc.majorant s (i '' K) (hK.image hi) r
    refine ⟨u, hu, hsum, ?_⟩
    intro b hb k
    exact hbound (i b) (Set.mem_image_of_mem i hb) k

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierSynthesis
