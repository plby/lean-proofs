import Wikipedia.HopfProblem.PeriodTorusCohomologyCupFormalPairs
import Wikipedia.HopfProblem.PeriodTorusCohomologyCupCycles
import Wikipedia.HopfProblem.PeriodTorusCohomologyCupDecomposition
import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingCoordinates
import Wikipedia.HopfProblem.CuspCentralCohomologyCoordinatesGenerators

/-!
# Actual coordinate cup pairs and the original alternating classes

The native Alexander--Whitney product of two coordinate one-cocycles is
evaluated on the actual positive period-pair cycle by its exact affine-prism
representative.  This gives the alternating coordinate formula and identifies
the actual cup products with the original six-coefficient classes.  The same
calculation identifies the existing coordinate-dual classes on the four-torus.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomologyCup

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open PeriodTorusHigherHomology PeriodTorusHigherHomologyPontryagin SingularCohomologyCup
open PeriodTorusCohomology PeriodTorusTypeOneOne PeriodTorusHigherHomologyExterior
open CuspCentralCohomology CuspCentralHomology.SpecializationModel LocalSystemMatrices

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The actual cup cochain evaluates every realized integral-vertex chain
by the corresponding literal front/back functional. -/
theorem coordinateOneCup_affineChain (i j : Fin 4) (c : FormalChains Lattice 3) :
    cup (coordinateOneCochain 4 i) (coordinateOneCochain 4 j)
      (affineTorusChain 4 2 c) = formalPairEvaluation i j c := by
  have h : (cup (coordinateOneCochain 4 i) (coordinateOneCochain 4 j)).comp
      (affineTorusChain 4 2) = formalPairEvaluation i j := by
    apply formalChains_ext
    intro v
    change cup (coordinateOneCochain 4 i) (coordinateOneCochain 4 j)
      (affineTorusChain 4 2 (formalSimplex v)) = _
    rw [affineTorusChain_simplex, coordinateOneCup_affineSimplex,
      formalPairEvaluation_simplex]
    rfl
  exact LinearMap.congr_fun h c

/-- Evaluation on actual ordered products of positive vector loops fixes
the sign of the genuine coordinate cup product. -/
theorem coordinateOneCup_evaluate_periodLoops (i j : Fin 4) (x y : Lattice) :
    singularEvaluation (ProductTorus 4) 2
        (cupProduct (ProductTorus 4) 1 1 (coordinateOneClass 4 i) (coordinateOneClass 4 j))
        (product11 (ProductTorus 4) (loopHomologyClass (coordinatePeriodLoop 4 x))
          (loopHomologyClass (coordinatePeriodLoop 4 y))) =
      x i * y j - x j * y i := by
  rw [← coordinatePairCycle_class]
  refine (cupProduct_evaluate_cocycles (ProductTorus 4) 1 1
    (coordinateOneCocycle 4 i) (coordinateOneCocycle 4 j) (coordinatePairCycle x y)).trans ?_
  rw [coordinateOneCocycle_val, coordinateOneCocycle_val, coordinatePairCycle_val,
    coordinateOneCup_affineChain, formalPairEvaluation_periodProduct]

/-- The actual pullback to each original period torus has the same ordered periods. -/
theorem periodOneCup_evaluate_periodLoops (p : PeriodDomain) (i j : Fin 4) (x y : Lattice) :
    singularEvaluation p.Torus 2
        (cupProduct p.Torus 1 1 (periodOneClass p i) (periodOneClass p j))
        (product11 p.Torus (loopHomologyClass (p.periodLoop x))
          (loopHomologyClass (p.periodLoop y))) =
      x i * y j - x j * y i := by
  rw [← coordinateOneCup_pullback, singularEvaluation_naturality,
    periodProduct_coordinate_image, positivePeriodLoop_coordinate_image,
    positivePeriodLoop_coordinate_image, coordinateOneCup_evaluate_periodLoops]

/-- The six coefficients of the alternating form of one ordered coordinate cup. -/
def pairCoefficients (i j : Fin 4) (k : Fin 6) : ℤ :=
  let x : Lattice := Pi.single (coefficientPair k).1 1
  let y : Lattice := Pi.single (coefficientPair k).2 1
  x i * y j - x j * y i

/-- The equality is proved in native singular cohomology by its six actual period-pair values. -/
theorem periodOneCup_eq_coefficientClass (p : PeriodDomain) (i j : Fin 4) :
    cupProduct p.Torus 1 1 (periodOneClass p i) (periodOneClass p j) =
      coefficientClass p (pairCoefficients i j) := by
  apply coefficientClass_unique_of_basis_pairs p (pairCoefficients i j)
  intro k
  exact periodOneCup_evaluate_periodLoops p i j
    (Pi.single (coefficientPair k).1 1) (Pi.single (coefficientPair k).2 1)

/-- Each of the six declared ordered pairs gives the corresponding unit coefficient. -/
@[simp] theorem pairCoefficients_coefficientPair (k : Fin 6) :
    pairCoefficients (coefficientPair k).1 (coefficientPair k).2 = Pi.single k 1 := by
  fin_cases k <;> decide

/-- All six coordinate-dual degree-two classes are actual ordered degree-one cups. -/
theorem periodOneCup_coefficientPair (p : PeriodDomain) (k : Fin 6) :
    cupProduct p.Torus 1 1
        (periodOneClass p (coefficientPair k).1) (periodOneClass p (coefficientPair k).2) =
      coefficientClass p (Pi.single k 1) := by
  rw [periodOneCup_eq_coefficientClass, pairCoefficients_coefficientPair]

/-- In particular, the first source coefficient is the actual cup of γ and u. -/
theorem periodOneCup_gamma_u (p : PeriodDomain) :
    cupProduct p.Torus 1 1 (periodOneClass p 0) (periodOneClass p 1) =
      coefficientClass p (Pi.single 0 1) :=
  periodOneCup_coefficientPair p 0

/-- The two previously defined enumerations use exactly the same six ordered pairs. -/
theorem pairIndices_eq_coefficientPair (k : Fin 6) :
    pairIndices k = ![(coefficientPair k).1, (coefficientPair k).2] := by
  fin_cases k <;> rfl

/-- The actual ordered basis-pair cycle has its original unit minor coordinate. -/
theorem coordinateTorusH2Coordinates_basis_pair (k : Fin 6) :
    coordinateTorusH2Coordinates
        (product11 (ProductTorus 4)
          (loopHomologyClass (coordinatePeriodLoop 4 (Pi.single (coefficientPair k).1 1)))
          (loopHomologyClass (coordinatePeriodLoop 4 (Pi.single (coefficientPair k).2 1)))) =
      Pi.single k 1 := by
  have hp : coordinateTorusWedgeTwo (squareBasis k) =
      product11 (ProductTorus 4)
        (loopHomologyClass (coordinatePeriodLoop 4 (Pi.single (coefficientPair k).1 1)))
        (loopHomologyClass (coordinatePeriodLoop 4 (Pi.single (coefficientPair k).2 1))) := by
    rw [squareBasis_apply, coordinateTorusWedgeTwo_apply_ιMulti_periodLoops
      (Elliptic.examplePeriod .four), pairIndices_eq_coefficientPair]
    simp only [Function.comp_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      latticeBasis, Pi.basisFun_apply]
  rw [← hp]
  change squareCoordinates
    (coordinateTorusH2ExteriorEquiv (coordinateTorusWedgeTwo (squareBasis k))) = _
  rw [coordinateTorusH2ExteriorEquiv_wedge]
  ext l
  simp [squareCoordinates_apply, Finsupp.single_apply, Pi.single_apply, eq_comm]

/-- The inverse of the original minor marking selects that same actual period-pair cycle. -/
theorem coordinateTorusH2Coordinates_symm_basis_pair (k : Fin 6) :
    coordinateTorusH2Coordinates.symm (Pi.single k 1) =
      product11 (ProductTorus 4)
        (loopHomologyClass (coordinatePeriodLoop 4 (Pi.single (coefficientPair k).1 1)))
        (loopHomologyClass (coordinatePeriodLoop 4 (Pi.single (coefficientPair k).2 1))) := by
  apply coordinateTorusH2Coordinates.injective
  rw [LinearEquiv.apply_symm_apply, coordinateTorusH2Coordinates_basis_pair]

/-- The constructed cocycle classes agree with the existing genuine positive-loop dual classes. -/
theorem coordinateOneClass_eq_dualClass (i : Fin 4) :
    coordinateOneClass 4 i = coordinateTorusH1DualClass i := by
  apply coordinateTorusH1CohomologyCoordinates.injective
  rw [coordinateTorusH1DualClass_coordinates]
  funext k
  change coordinateTorusCohomologyCoordinates 1 coordinateTorusH1Coordinates
    (coordinateOneClass 4 i) k = _
  rw [coordinateTorusCohomologyCoordinates_apply_coordinate,
    coordinateTorusH1Coordinates_symm_apply,
    coordinateH1_four_apply (Elliptic.examplePeriod .four), coordinateOneClass_periodLoop]
  simp [Pi.single_apply, eq_comm]

/-- Native cup evaluation gives the original six dual-minor coordinates. -/
theorem coordinateOneCup_coordinates (i j : Fin 4) :
    coordinateTorusH2CohomologyCoordinates
        (cupProduct (ProductTorus 4) 1 1 (coordinateOneClass 4 i) (coordinateOneClass 4 j)) =
      pairCoefficients i j := by
  funext k
  change coordinateTorusCohomologyCoordinates 2 coordinateTorusH2Coordinates
    (cupProduct (ProductTorus 4) 1 1 (coordinateOneClass 4 i) (coordinateOneClass 4 j)) k = _
  rw [coordinateTorusCohomologyCoordinates_apply_coordinate,
    coordinateTorusH2Coordinates_symm_basis_pair, coordinateOneCup_evaluate_periodLoops]
  rfl

/-- Every original ordered dual-minor generator is the genuine cup of its two degree-one classes. -/
theorem coordinateDualCup_coefficientPair (k : Fin 6) :
    cupProduct (ProductTorus 4) 1 1
        (coordinateTorusH1DualClass (coefficientPair k).1)
        (coordinateTorusH1DualClass (coefficientPair k).2) =
      coordinateTorusH2DualClass k := by
  rw [← coordinateOneClass_eq_dualClass, ← coordinateOneClass_eq_dualClass]
  apply coordinateTorusH2CohomologyCoordinates.injective
  rw [coordinateOneCup_coordinates, pairCoefficients_coefficientPair,
    coordinateTorusH2DualClass_coordinates]

/-- The requested γ∪u identification holds for the original coordinate-dual classes. -/
theorem coordinateDualCup_gamma_u :
    cupProduct (ProductTorus 4) 1 1
        (coordinateTorusH1DualClass 0) (coordinateTorusH1DualClass 1) =
      coordinateTorusH2DualClass 0 :=
  coordinateDualCup_coefficientPair 0

end Wikipedia.HopfProblem.PeriodTorusCohomologyCup
