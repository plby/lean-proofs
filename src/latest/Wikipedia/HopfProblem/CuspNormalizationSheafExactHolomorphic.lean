import Wikipedia.HopfProblem.CuspNormalizationSheafExactBoundary

/-!
# The exact holomorphic normalization resolution of the actual cusp fibre

This is the genuine sheaf sequence of source Lemma 9.12(i): the reduced
holomorphic-function sheaf on the actual singular fibre, the actual
normalization direct image, the direct sum of the three actual double-curve
direct images, and the two actual scalar skyscraper sheaves. Its arrows
are the actual pullback, source-oriented differences, and alternating
evaluations. Exactness is proved on the actual analytic stalks.

No higher-cohomology acyclicity or cohomology comparison is claimed here.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The actual normalization resolution
`0 → O_W → ν_*O_E₀ → ⨁ₖ (iₖ)_*O_Dₖ → ℂ_P ⊕ ℂ_Q → 0`
is exact, with the source's literal maps and the same signs at `P,Q`. -/
theorem resolution_exact : (resolution C ε hε hε1 hC hR).Exact where
  toIsComplex := resolution_isComplex C ε hε hε1 hC hR
  exact i hi := by
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · exact initialComplex_exact C ε hε hε1 hC hR
    · exact normalizationComplex_exact C ε hε hε1 hC hR
    · exact boundaryComplex_exact C ε hε hε1 hC hR
    · exact terminalComplex_exact C ε hε hε1 hC hR

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
