import Wikipedia.HopfProblem.CuspNormalizationSheafCuspEndpoints
import Mathlib.Algebra.Homology.ExactSequence

/-!
# The actual normalization sheaf complex with both zero endpoints

The last differential is the source's actual signed evaluation
`g₁ - g₂ + g₃` at each of the two triple points. The complex identity is
proved using the actual endpoint table of the six boundary curves and
naturality of holomorphic evaluation. No exactness is assumed here.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits
open scoped ContDiff ZeroObject

namespace Wikipedia.HopfProblem.CuspNormalization.SheafResolution

open CuspQuotient ToricCharts ToricSpace
open CuspQuotient.NormalizationCurves

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- Evaluation depends on the actual point, not on the proof that it
lies in the specified fibre. -/
theorem normalizationPointEvaluation_congr (y z : rayDivisor 0) (t : Fin 2)
    (hy : normalizationMap C ε hε y = triplePoint C ε hε t)
    (hyz : y = z) (hz : normalizationMap C ε hε z = triplePoint C ε hε t) :
    normalizationPointEvaluation C ε hε y t hy = normalizationPointEvaluation C ε hε z t hz := by
  subst z
  rfl

/-- Evaluation at the actual positive endpoint of a double-curve lift. -/
def plusEndpointEvaluation (k : Fin 3) (t : Fin 2) :
    normalizationSheaf C ε hε ⟶ triplePointSheaf C ε hε t :=
  normalizationPointEvaluation C ε hε
    (sourcePlusLift C ε hε k (curveTriplePoint C ε hε k t)) t
    ((normalization_sourcePlusLift C ε hε k _).trans
      (sourceCurveMap_curveTriplePoint C ε hε k t))

/-- Evaluation at the actual negative endpoint of a double-curve lift. -/
def minusEndpointEvaluation (k : Fin 3) (t : Fin 2) :
    normalizationSheaf C ε hε ⟶ triplePointSheaf C ε hε t :=
  normalizationPointEvaluation C ε hε
    (sourceMinusLift C ε hε k (curveTriplePoint C ε hε k t)) t
    ((normalization_sourceMinusLift C ε hε k _).trans
      (sourceCurveMap_curveTriplePoint C ε hε k t))

/-- The actual restrictions telescope at both actual triple points. -/
theorem boundaryDifference_evaluation_sum (t : Fin 2) :
    boundaryDifference C ε hε hε1 hC hR 0 ≫ curveEvaluation C ε hε hε1 hC hR 0 t -
      boundaryDifference C ε hε hε1 hC hR 1 ≫ curveEvaluation C ε hε hε1 hC hR 1 t +
      boundaryDifference C ε hε hε1 hC hR 2 ≫ curveEvaluation C ε hε hε1 hC hR 2 t = 0 := by
  simp only [boundaryDifference, Preadditive.sub_comp, plusPullback_curveEvaluation,
    minusPullback_curveEvaluation]
  change (plusEndpointEvaluation C ε hε 0 t - minusEndpointEvaluation C ε hε 0 t) -
    (plusEndpointEvaluation C ε hε 1 t - minusEndpointEvaluation C ε hε 1 t) +
    (plusEndpointEvaluation C ε hε 2 t - minusEndpointEvaluation C ε hε 2 t) = 0
  fin_cases t
  · change (plusEndpointEvaluation C ε hε 0 0 - minusEndpointEvaluation C ε hε 0 0) -
      (plusEndpointEvaluation C ε hε 1 0 - minusEndpointEvaluation C ε hε 1 0) +
      (plusEndpointEvaluation C ε hε 2 0 - minusEndpointEvaluation C ε hε 2 0) = 0
    have h₁ : plusEndpointEvaluation C ε hε 1 0 = plusEndpointEvaluation C ε hε 0 0 := by
      unfold plusEndpointEvaluation
      apply normalizationPointEvaluation_congr
      simp only [curveTriplePoint_zero, sourcePlusLift_P]
      rfl
    have h₂ : plusEndpointEvaluation C ε hε 2 0 = minusEndpointEvaluation C ε hε 0 0 := by
      unfold plusEndpointEvaluation minusEndpointEvaluation
      apply normalizationPointEvaluation_congr
      simp only [curveTriplePoint_zero, sourcePlusLift_P, sourceMinusLift_P]
      rfl
    have h₃ : minusEndpointEvaluation C ε hε 2 0 = minusEndpointEvaluation C ε hε 1 0 := by
      unfold minusEndpointEvaluation
      apply normalizationPointEvaluation_congr
      simp only [curveTriplePoint_zero, sourceMinusLift_P]
      rfl
    rw [h₁, h₂, h₃]
    abel
  · change (plusEndpointEvaluation C ε hε 0 1 - minusEndpointEvaluation C ε hε 0 1) -
      (plusEndpointEvaluation C ε hε 1 1 - minusEndpointEvaluation C ε hε 1 1) +
      (plusEndpointEvaluation C ε hε 2 1 - minusEndpointEvaluation C ε hε 2 1) = 0
    have h₁ : minusEndpointEvaluation C ε hε 1 1 = minusEndpointEvaluation C ε hε 0 1 := by
      unfold minusEndpointEvaluation
      apply normalizationPointEvaluation_congr
      simp only [curveTriplePoint_one, sourceMinusLift_Q]
      rfl
    have h₂ : plusEndpointEvaluation C ε hε 2 1 = plusEndpointEvaluation C ε hε 1 1 := by
      unfold plusEndpointEvaluation
      apply normalizationPointEvaluation_congr
      simp only [curveTriplePoint_one, sourcePlusLift_Q]
      rfl
    have h₃ : minusEndpointEvaluation C ε hε 2 1 = plusEndpointEvaluation C ε hε 0 1 := by
      unfold minusEndpointEvaluation plusEndpointEvaluation
      apply normalizationPointEvaluation_congr
      simp only [curveTriplePoint_one, sourceMinusLift_Q, sourcePlusLift_Q]
      rfl
    rw [h₁, h₂, h₃]
    abel

/-- The actual alternating evaluation at one of the two triple points. -/
def deltaOneAt (t : Fin 2) :
    boundarySheaf C ε hε hε1 hC hR ⟶ triplePointSheaf C ε hε t :=
  biproduct.π (curveSheaf C ε hε hε1 hC hR) 0 ≫ curveEvaluation C ε hε hε1 hC hR 0 t -
    biproduct.π (curveSheaf C ε hε hε1 hC hR) 1 ≫ curveEvaluation C ε hε hε1 hC hR 1 t +
    biproduct.π (curveSheaf C ε hε hε1 hC hR) 2 ≫ curveEvaluation C ε hε hε1 hC hR 2 t

/-- The genuine last nonzero differential, evaluated at actual `P,Q`. -/
def deltaOne : boundarySheaf C ε hε hε1 hC hR ⟶ tripleSheaf C ε hε :=
  biproduct.lift (deltaOneAt C ε hε hε1 hC hR)

@[reassoc (attr := simp)] theorem deltaOne_component (t : Fin 2) :
    deltaOne C ε hε hε1 hC hR ≫ biproduct.π (triplePointSheaf C ε hε) t =
      deltaOneAt C ε hε hε1 hC hR t :=
  biproduct.lift_π _ _

theorem deltaZero_deltaOne :
    deltaZero C ε hε hε1 hC hR ≫ deltaOne C ε hε hε1 hC hR = 0 := by
  apply biproduct.hom_ext
  intro t
  rw [Category.assoc, deltaOne_component, zero_comp]
  simp only [deltaOneAt, Preadditive.comp_add, Preadditive.comp_sub,
    ← Category.assoc, deltaZero_component]
  exact boundaryDifference_evaluation_sum C ε hε hε1 hC hR t

/-- The middle and last nonzero arrows as an actual short complex. -/
def boundaryComplex :
    ShortComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε))) where
  X₁ := normalizationSheaf C ε hε
  X₂ := boundarySheaf C ε hε hε1 hC hR
  X₃ := tripleSheaf C ε hε
  f := deltaZero C ε hε hε1 hC hR
  g := deltaOne C ε hε hε1 hC hR
  zero := deltaZero_deltaOne C ε hε hε1 hC hR

/-- The terminal zero arrow of the actual resolution. -/
def terminalComplex :
    ShortComplex (TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε))) where
  X₁ := boundarySheaf C ε hε hε1 hC hR
  X₂ := tripleSheaf C ε hε
  X₃ := 0
  f := deltaOne C ε hε hε1 hC hR
  g := 0
  zero := comp_zero

/-- The entire actual normalization sequence, with its two zero endpoints. -/
def resolution : ComposableArrows
    (TopCat.Sheaf AddCommGrpCat (TopCat.of (CentralSpace C ε))) 5 :=
  ComposableArrows.mk₅ (initialComplex C ε hε hε1 hC hR).f
    (normalizationPullback C ε hε hε1 hC hR) (deltaZero C ε hε hε1 hC hR)
    (deltaOne C ε hε hε1 hC hR) (terminalComplex C ε hε hε1 hC hR).g

/-- The actual global sheaf sequence is a complex, with the source's
literal restriction maps and the same signs at both actual triple points. -/
theorem resolution_isComplex : (resolution C ε hε hε1 hC hR).IsComplex where
  zero i hi := by
    have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    rcases h with rfl | rfl | rfl | rfl
    · exact (initialComplex C ε hε hε1 hC hR).zero
    · exact (normalizationComplex C ε hε hε1 hC hR).zero
    · exact (boundaryComplex C ε hε hε1 hC hR).zero
    · exact (terminalComplex C ε hε hε1 hC hR).zero

end Wikipedia.HopfProblem.CuspNormalization.SheafResolution
