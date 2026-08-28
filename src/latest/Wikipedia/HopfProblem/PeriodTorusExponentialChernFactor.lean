import Wikipedia.HopfProblem.PeriodTorusExponentialChernLocalWinding
import Wikipedia.HopfProblem.PeriodTorusExponentialChernNaturality
import Wikipedia.HopfProblem.ExponentialChernComparisonLogarithmBridge

/-!
# The original factor-bundle winding class is its exponential Chern class

The original native unit cocycle and its original holomorphic logarithms
feed the actual connecting-map comparison.  The local singular cochains
have the literal winding cochain as their differential.  Canonical
coefficient naturality therefore identifies the two actual classes after
the original period coefficient map, which is genuinely injective on the
original torus's integral degree-two singular cohomology.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusExponentialChern

open ConstantSheafSingularComparison PeriodTorusAppellHumbert
open ExponentialChernComparison HolomorphicExponentialSheaf

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂

variable {p : PeriodDomain} (F : FactorOfAutomorphy p)

/-- The actual original coefficient map identifies the original
exponential Chern class and the original boundary-winding Chern class. -/
theorem factor_coefficient_firstChernClass :
    Coefficients.exponentialH2Hom p
        (nativeFirstChernClass p (Core.data F).core.Fiber) =
      Coefficients.exponentialH2Hom p (PeriodTorusLineBundle.Chern.firstChernClass F) := by
  have h := LogarithmBridge.constantSheafH2Iso_exponentialConnecting
    IC p.Torus (torusLocallyContractible p)
    (factorNativeCocycle F) (chartCover_covers p)
    (coordinateLogSection F) (coordinateLogSection_exponential F)
    (windingComplexCochain F) (windingComplexCochain_closed F)
    (localPrimitive F) (localPrimitive_winding F) (localPrimitive_difference F)
  calc
    _ = (constantSheafH2Iso (TopCat.of p.Torus) (AddCommGrpCat.of ℂ)
        (torusLocallyContractible p)).hom
          (CategoryTheory.Sheaf.H.map (CochainZero.integerCoefficientMap (TopCat.of p.Torus)) 2
            (HolomorphicPicard.Chern.exponentialConnecting IC p.Torus 1
              (HolomorphicPicard.CechExtension.classOf
                (factorNativeCocycle F) (chartCover_covers p)))) :=
      exponentialH2Hom_integralH2Comparison p
        (HolomorphicPicard.Chern.nativeFirstChernClass IC p.Torus (Core.data F).core.Fiber)
    _ = SheafHigherDirectImage.ExtBridge.cycleClass
        (singularCochainComplex p.Torus (AddCommGrpCat.of ℂ)) 2
          (windingComplexCochain F) (windingComplexCochain_closed_sc F) := h
    _ = _ := (exponentialH2Hom_firstChernClass F).symm

/-- For the original native factor bundle, the actual integral
exponential class equals its independently defined integer winding class. -/
theorem nativeFirstChernClass_factor :
    nativeFirstChernClass p (Core.data F).core.Fiber =
      PeriodTorusLineBundle.Chern.firstChernClass F :=
  Coefficients.exponentialH2Hom_injective p (factor_coefficient_firstChernClass F)

end Wikipedia.HopfProblem.PeriodTorusExponentialChern
