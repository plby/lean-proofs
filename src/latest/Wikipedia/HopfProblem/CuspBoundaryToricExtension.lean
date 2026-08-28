import Wikipedia.HopfProblem.CuspBoundaryToricExtensionCap

/-!
# The two actual toric swept boundary classes and their disc caps

The source's dual period basis in `Λ` is the hatted `(γ,u,w,δ)` basis,
distinct from the cohomology basis in `V`.  Its last two
columns are fixed by the original `M₀`, and their genuine positive
circle sweeps extend over the actual reference-chart disc product in
the original full cusp cap.  The positive Wang formulas concern these
same explicitly constructed classes, not selected Wang preimages.

The package also exposes the literal boundary map on real cylinder
representatives and its actual regular-family comparison, independently
of all homology calculations.
-/

noncomputable section

namespace Wikipedia.HopfProblem.CuspBoundaryToricExtension

open FirstHurewicz SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology
open TrianglePeriodFamily

/-- The actual sweep of the positive original hatted `w` period in `Λ`. -/
def sweptWClass : SingularHomology (ThreefoldOverlapMappingTorus.Boundary none) 2 :=
  sweptToricClass (loopHomologyClass (coordinatePeriodLoop 2 (Pi.single 0 1)))

/-- The actual sweep of the positive original hatted `δ` period in `Λ`. -/
def sweptDeltaClass : SingularHomology (ThreefoldOverlapMappingTorus.Boundary none) 2 :=
  sweptToricClass (loopHomologyClass (coordinatePeriodLoop 2 (Pi.single 1 1)))

/-- A single actual swept class simultaneously has zero cap image and
the exact positive original Wang marking. -/
theorem sweptToricClass_cap_zero_and_wang (a : SingularHomology (ProductTorus 2) 1) :
    ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap none 2 (sweptToricClass a) = 0 ∧
      wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 1 (sweptToricClass a) =
        singularHomologyMap fibreMap 1 a :=
  ⟨boundaryFillingHomologyMap_sweptToricClass_eq_zero a, sweptToricClass_wang a⟩

theorem sweptWClass_cap_eq_zero :
    ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap none 2 sweptWClass = 0 :=
  boundaryFillingHomologyMap_sweptToricClass_eq_zero _

theorem sweptDeltaClass_cap_eq_zero :
    ThreefoldOverlapMappingTorus.boundaryFillingHomologyMap none 2 sweptDeltaClass = 0 :=
  boundaryFillingHomologyMap_sweptToricClass_eq_zero _

/-- The positive `w` sweep has the original third period as its exact Wang boundary. -/
theorem sweptWClass_wang :
    wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 1 sweptWClass =
      FlatTorus.singularH1Equiv.symm (Pi.single (2 : Fin 4) 1) :=
  sweptToricClass_wang_basis_zero

/-- The positive `δ` sweep has the original fourth period as its exact Wang boundary. -/
theorem sweptDeltaClass_wang :
    wangBoundary ThreefoldOverlapMappingTorus.Cusp.monodromy 1 sweptDeltaClass =
      FlatTorus.singularH1Equiv.symm (Pi.single (3 : Fin 4) 1) :=
  sweptToricClass_wang_basis_one

end Wikipedia.HopfProblem.CuspBoundaryToricExtension
