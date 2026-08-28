import Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishingNative
import Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishingExteriorDimension
import Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishingDetection
import Wikipedia.HopfProblem.SheafCupProductCuspLinear

/-!
# The genuine exterior-square cup is an isomorphism on the cusp

The nonzero value is the cup of the original named classes. The source
and target dimensions come from the proved Ext-defined holomorphic
cohomology calculation. Thus the original exterior-square cup map,
with its original pointwise complex scalars, is itself bijective.
-/

noncomputable section

open CategoryTheory
open scoped ContDiff

namespace Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishing

open CuspNormalization SheafResolution CuspQuotient ToricSpace SheafCupProduct.Cusp

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
  (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
  (hR : SmallDrift C r)

/-- The original exterior-square cup map is nonzero. -/
theorem holomorphicCuspExteriorCup_ne_zero :
    holomorphicCuspExteriorCup C r hr hr1 hC hR ≠ 0 :=
  linearMap_ne_zero_of_nonzero_value (holomorphicCuspExteriorCup C r hr hr1 hC hR)
    (exteriorPower.ιMulti ℂ 2
      ![holomorphicGamma C r hr hr1 hC hR, holomorphicU C r hr hr1 hC hR])
    (holomorphicCuspCup C r hr hr1 hC hR
      (holomorphicGamma C r hr hr1 hC hR) (holomorphicU C r hr hr1 hC hR))
    (holomorphicCuspExteriorCup_ιMulti C r hr hr1 hC hR
      ![holomorphicGamma C r hr hr1 hC hR, holomorphicU C r hr hr1 hC hR])
    (holomorphicGamma_cup_holomorphicU_ne_zero C r hr hr1 hC hR)

/-- Source Lemma 9.12(iv): the genuine exterior-square holomorphic cup is bijective. -/
theorem holomorphicCuspExteriorCup_bijective :
    Function.Bijective (holomorphicCuspExteriorCup C r hr hr1 hC hR) :=
  bijective_of_finrank_one (holomorphicCuspExteriorCup C r hr hr1 hC hR)
    (holomorphicExterior_finrank C r hr hr1 hC hR)
    (SheafCohomology.reducedH2_finrank C r hr hr1 hC hR)
    (holomorphicCuspExteriorCup_ne_zero C r hr hr1 hC hR)

/-- The actual cup map, bundled using its proved bijectivity. -/
def holomorphicCuspExteriorCupEquiv :
    ⋀[ℂ]^2 (CategoryTheory.Sheaf.H.{0} (reducedSheaf C r hr hr1 hC hR) 1) ≃ₗ[ℂ]
      CategoryTheory.Sheaf.H.{0} (reducedSheaf C r hr hr1 hC hR) 2 :=
  LinearEquiv.ofBijective (holomorphicCuspExteriorCup C r hr hr1 hC hR)
    (holomorphicCuspExteriorCup_bijective C r hr hr1 hC hR)

/-- The equivalence's forward linear map is exactly the original cup map. -/
@[simp] theorem holomorphicCuspExteriorCupEquiv_toLinearMap :
    (holomorphicCuspExteriorCupEquiv C r hr hr1 hC hR).toLinearMap =
      holomorphicCuspExteriorCup C r hr hr1 hC hR := rfl

@[simp] theorem holomorphicCuspExteriorCupEquiv_apply
    (v : ⋀[ℂ]^2 (CategoryTheory.Sheaf.H.{0} (reducedSheaf C r hr hr1 hC hR) 1)) :
    holomorphicCuspExteriorCupEquiv C r hr hr1 hC hR v =
      holomorphicCuspExteriorCup C r hr hr1 hC hR v := rfl

end Wikipedia.HopfProblem.CuspHolomorphicCupNonvanishing
