import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyFinitePushforward
import Wikipedia.HopfProblem.SheafHigherDirectImageBasic

/-!
# Genuine higher direct images under finite closed maps

The already proved exactness of the actual finite closed pushforward
makes the pushed-forward injective resolution exact in positive degree.
Consequently its genuine right-derived sheaves vanish. The concrete
corollaries apply this to the actual cusp normalization and its three
actual double-curve inclusions, for arbitrary abelian sheaves.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyFinitePushforward

variable {X Y : TopCat.{0}} (f : X ⟶ Y) [T2Space X]
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)

include hf hfinite

/-- Actual finite closed pushforward has no positive right-derived
sheaves, for every genuine abelian sheaf on the source. -/
theorem higherDirectImage_isZero (F : AbelianSheaf X) (n : ℕ) :
    IsZero (SheafHigherDirectImage.sheaf f F (n + 1)) := by
  let I := injectiveResolution F
  refine IsZero.of_iso ?_ (SheafHigherDirectImage.resolutionIso f F I (n + 1))
  apply (HomologicalComplex.exactAt_iff_isZero_homology _ (n + 1)).mp
  change ((I.cocomplex.sc (n + 1)).map (pushforward f)).Exact
  exact pushforward_exact f hf hfinite _ (I.cocomplex_exactAt_succ n)

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyFinitePushforward

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace NormalizationCurves
open SheafCohomologyFinitePushforward

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

include hε1 hC hR

/-- The actual normalization has vanishing positive derived sheaf
pushforwards, not merely vanishing cohomology of a proposed model. -/
theorem normalization_higherDirectImage_isZero
    (F : AbelianSheaf (TopCat.of (rayDivisor 0))) (n : ℕ) :
    IsZero (SheafHigherDirectImage.sheaf (normalizationMap C ε hε) F (n + 1)) :=
  higherDirectImage_isZero (normalizationMap C ε hε) (normalization_isClosedMap C ε hε)
    (normalization_fibre_finite C ε hε hε1 hC hR) F n

/-- Each of the actual source-ordered double-curve inclusions has
vanishing positive derived pushforwards of every abelian sheaf. -/
theorem curve_higherDirectImage_isZero (k : Fin 3)
    (F : AbelianSheaf (TopCat.of (sourceDoubleCurve C ε hε k))) (n : ℕ) :
    IsZero (SheafHigherDirectImage.sheaf (sourceCurveMap C ε hε k) F (n + 1)) := by
  let := quotient_t2Space C ε hε hε1 hC hR
  exact higherDirectImage_isZero (sourceCurveMap C ε hε k)
    (SheafCurveStalk.sourceCurveMap_isClosedMap C ε hε k)
    (sourceCurveMap_fibre_finite C ε hε k) F n

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
