import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupBasic
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyOne
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Dimension of the genuine exterior-square source

The source is Mathlib's exterior square of the original Ext-defined
holomorphic H¹ with its actual pointwise complex scalar action.
The dimension follows from the proved Haar-mean computation, without
any assertion about the value or nonvanishing of cup.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup

open PeriodTorusHolomorphicCohomology

theorem exterior_finrank (p : PeriodDomain) :
    Module.finrank ℂ (⋀[ℂ]^2 (H p 1)) = 1 := by
  let : Module.Finite ℂ (H p 1) :=
    Module.finite_of_finrank_pos (by rw [h1_finrank]; decide)
  rw [exteriorPower.finrank_eq, h1_finrank]
  rfl

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup
