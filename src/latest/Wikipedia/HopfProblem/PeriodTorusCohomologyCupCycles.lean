import Wikipedia.HopfProblem.PeriodTorusCohomologyCupOneRealization
import Wikipedia.HopfProblem.PeriodTorusCohomologyCupTopClass

/-!
# Genuine cycle representatives for the period cup calculation

The pair and top cycles below are built using the actual singular
Pontryagin product.  Their underlying chains are exactly the realized
integer-vertex prism chains, and their classes are the original positive
period products.  The formal chains need not be cycles before reduction
modulo the period lattice.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomologyCup

open FirstHurewicz SingularMayerVietoris ModuleHomology
open PeriodTorusHigherHomology PeriodTorusHigherHomologyPontryagin

attribute [local instance] integerLinearMapModule integerTensorModule

/-- A positive period loop, regarded in the native all-degree cycle kernel. -/
def coordinateProductLoopCycle (x : Lattice) :
    Cycle (singularComplex (ProductTorus 4)) 1 := loopCycle (coordinatePeriodLoop 4 x)

@[simp] theorem coordinateProductLoopCycle_val (x : Lattice) :
    (coordinateProductLoopCycle x).val = pathChain (coordinatePeriodLoop 4 x) := rfl

@[simp] theorem coordinateProductLoopCycle_class (x : Lattice) :
    ModuleHomology.cycleClass (singularComplex (ProductTorus 4)) 1
      (coordinateProductLoopCycle x) = loopHomologyClass (coordinatePeriodLoop 4 x) := rfl

/-- The actual pair of positive vector loops, multiplied in the native singular complex. -/
def coordinatePairCycle (x y : Lattice) : Cycle (singularComplex (ProductTorus 4)) 2 :=
  productCycles (ProductTorus 4) 1
    (coordinateProductLoopCycle x) (coordinateProductLoopCycle y)

/-- Its underlying native chain is the literal formal prism after integer-affine realization. -/
theorem coordinatePairCycle_val (x y : Lattice) :
    (coordinatePairCycle x y).val =
      affineTorusChain 4 2 (formalPeriodProduct 1 (formalPeriodEdge x) (formalPeriodEdge y)) := by
  rw [affineTorusChain_formalPeriodProduct, affineTorusChain_formalPeriodEdge,
    affineTorusChain_formalPeriodEdge]
  exact productCycles_val (ProductTorus 4) 1 _ _

/-- The actual homology class is the original ordered product of the two positive loops. -/
theorem coordinatePairCycle_class (x y : Lattice) :
    ModuleHomology.cycleClass (singularComplex (ProductTorus 4)) 2 (coordinatePairCycle x y) =
      product11 (ProductTorus 4) (loopHomologyClass (coordinatePeriodLoop 4 x))
        (loopHomologyClass (coordinatePeriodLoop 4 y)) :=
  (product_cycleClass (ProductTorus 4) 1
    (coordinateProductLoopCycle x) (coordinateProductLoopCycle y)).symm

/-- The positive fourfold native cycle, with the same right association as the prism. -/
def coordinateTopCycle : Cycle (singularComplex (ProductTorus 4)) 4 :=
  productCycles (ProductTorus 4) 3
    (coordinateProductLoopCycle (Pi.single 0 1))
    (productCycles (ProductTorus 4) 2
      (coordinateProductLoopCycle (Pi.single 1 1))
      (productCycles (ProductTorus 4) 1
        (coordinateProductLoopCycle (Pi.single 2 1))
        (coordinateProductLoopCycle (Pi.single 3 1))))

/-- The exact native top-cycle chain is the formal positive prism used in the finite calculation. -/
theorem coordinateTopCycle_val :
    coordinateTopCycle.val = affineTorusChain 4 4 formalPositiveTop := by
  simp only [coordinateTopCycle, productCycles_val, coordinateProductLoopCycle_val,
    formalPositiveTop, affineTorusChain_formalPeriodProduct,
    affineTorusChain_formalPeriodEdge]

/-- The genuine top-cycle class has the original positive Mayer--Vietoris normalization. -/
theorem coordinateTopCycle_class :
    ModuleHomology.cycleClass (singularComplex (ProductTorus 4)) 4 coordinateTopCycle =
      productTorusTopClass 4 := by
  rw [coordinateTopCycle, ← product_cycleClass, ← product_cycleClass, ← product_cycleClass]
  simp only [coordinateProductLoopCycle_class]
  exact productTorusTopClass_four.symm

end Wikipedia.HopfProblem.PeriodTorusCohomologyCup
