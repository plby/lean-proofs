import Wikipedia.HopfProblem.SheafCupProductCusp
import Wikipedia.HopfProblem.SheafCupProductFunctionsLinear
import Wikipedia.HopfProblem.SheafCupProductExteriorBasic

/-!
# Actual complex-bilinear and exterior-square cup maps on the cusp

These are maps on the original reduced holomorphic sheaf's native
cohomology, with precisely the pointwise scalar structures used in its
proved dimension calculation.  The source exterior power is Mathlib's
actual exterior square.  Nonvanishing and invertibility are not assumed
or asserted.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SheafCupProduct.Cusp

open CuspNormalization SheafResolution CuspQuotient ToricCharts ToricSpace

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
  (hε1 : ε < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 ε))
  (hR : SmallDrift C ε)

/-- The original constant functions in the actual fixed-atlas cusp ring sheaf. -/
def reducedCuspCoefficients : Scalars.Coefficients (reducedRingSheaf C ε hε hε1 hC hR) := by
  letI := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact reducedCoefficients 𝓘(ℂ, CoordinateSpace 3) (centralSet C ε)

theorem scalarEnd_reducedCuspCoefficients :
    Scalars.scalarEnd (reducedCuspCoefficients C ε hε hε1 hC hR) =
      SheafCohomologyScalarResolution.reducedSheafScalarEnd C ε hε hε1 hC hR := by
  let := CuspQuotient.chartedSpace C ε hε hε1 hC hR
  exact scalarEnd_reducedCoefficients 𝓘(ℂ, CoordinateSpace 3) (centralSet C ε)

/-- The actual holomorphic cusp cup, bilinear for the original pointwise scalars. -/
def holomorphicCuspLinearCup :
    CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 1 →ₗ[ℂ]
      CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 1 →ₗ[ℂ]
        CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 2 :=
  linearCupOfScalarEnd (reducedCuspCoefficients C ε hε hε1 hC hR)
    (SheafCohomologyScalarResolution.reducedSheafScalarEnd C ε hε hε1 hC hR)
    (scalarEnd_reducedCuspCoefficients C ε hε hε1 hC hR)

@[simp] theorem holomorphicCuspLinearCup_apply
    (a b : CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 1) :
    holomorphicCuspLinearCup C ε hε hε1 hC hR a b =
      holomorphicCuspCup C ε hε hε1 hC hR a b :=
  linearCupOfScalarEnd_apply (reducedCuspCoefficients C ε hε hε1 hC hR)
    (SheafCohomologyScalarResolution.reducedSheafScalarEnd C ε hε hε1 hC hR)
    (scalarEnd_reducedCuspCoefficients C ε hε hε1 hC hR) a b

theorem holomorphicCuspLinearCup_self
    (a : CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 1) :
    holomorphicCuspLinearCup C ε hε hε1 hC hR a a = 0 := by
  exact (holomorphicCuspLinearCup_apply C ε hε hε1 hC hR a a).trans
    (cup_self_eq_zero (reducedRingSheaf C ε hε hε1 hC hR)
      (SheafCohomologyScalarResolution.reducedSheafScalarEnd C ε hε hε1 hC hR) a)

/-- The genuine exterior-square cup map for the original singular cusp structure sheaf. -/
def holomorphicCuspExteriorCup :
    ⋀[ℂ]^2 (CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 1) →ₗ[ℂ]
      CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 2 :=
  exteriorPairing (holomorphicCuspLinearCup C ε hε hε1 hC hR)
    (holomorphicCuspLinearCup_self C ε hε hε1 hC hR)

@[simp] theorem holomorphicCuspExteriorCup_ιMulti
    (v : Fin 2 → CategoryTheory.Sheaf.H.{0} (reducedSheaf C ε hε hε1 hC hR) 1) :
    holomorphicCuspExteriorCup C ε hε hε1 hC hR (exteriorPower.ιMulti ℂ 2 v) =
      holomorphicCuspCup C ε hε hε1 hC hR (v 0) (v 1) := by
  exact (exteriorPairing_ιMulti (holomorphicCuspLinearCup C ε hε hε1 hC hR)
    (holomorphicCuspLinearCup_self C ε hε hε1 hC hR) v).trans
      (holomorphicCuspLinearCup_apply C ε hε hε1 hC hR (v 0) (v 1))

end Wikipedia.HopfProblem.SheafCupProduct.Cusp
