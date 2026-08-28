import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCrossProductDefinition
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCrossArcChains
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleTwoChainConnecting
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleProduct

/-!
# The connecting map of the actual positive circle cross product

The actual two arc cross-chains have opposite boundaries coming from
the upper-minus-lower intersection cycle. Gluing them in the genuine
small-chain complex and applying the actual connecting formula gives
the raw coordinates `(-b,b)`. The signed circle coordinate is therefore
exactly `b`.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris CircleTopology CirclePaths

variable (X : Type) [TopologicalSpace X]

/-- The actual small cycle made from the two arc cross-chains. -/
def positiveCircleSmallCycle (n : ℕ) (b : ModuleHomology.Cycle (singularComplex X) n) :
    ModuleHomology.Cycle (smallComplex (productU X) (productV X)) (n + 1) :=
  twoChainSmallCycle (productU X) (productV X) n
    (uCrossChain X n b) (vCrossChain X n b) (intersectionDifferenceCycle X n b)
    (uCrossChain_boundary X n b) (vCrossChain_boundary X n b)

/-- Its actual ambient chain is the cross product of the sum of the two arc chains. -/
theorem positiveCircleSmallCycle_ambient_val (n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    (ModuleHomology.mapCycles (smallInclusion (productU X) (productV X)) (n + 1)
        (positiveCircleSmallCycle X n b)).1 =
      crossProductEdge Circle X n (pathChain uCirclePath + pathChain vCirclePath) b.1 :=
  (twoChainSmallCycle_ambient_val (productU X) (productV X) n
    (uCrossChain X n b) (vCrossChain X n b) (intersectionDifferenceCycle X n b)
    (uCrossChain_boundary X n b) (vCrossChain_boundary X n b)).trans
    (arcCrossChains_inclusion_sum X n b)

/-- The ambient cycle is literally the constructed cross-product cycle of the arc sum. -/
theorem positiveCircleSmallCycle_ambient_eq (n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    ModuleHomology.mapCycles (smallInclusion (productU X) (productV X)) (n + 1)
        (positiveCircleSmallCycle X n b) = crossProductCycles Circle X n arcSumCycle b := by
  apply Subtype.ext
  exact positiveCircleSmallCycle_ambient_val X n b

/-- The glued actual small cycle represents the genuine positive-loop cross product. -/
theorem positiveCircleSmallCycle_ambient_class (n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    ModuleHomology.cycleClass (singularComplex (Circle × X)) (n + 1)
        (ModuleHomology.mapCycles (smallInclusion (productU X) (productV X)) (n + 1)
          (positiveCircleSmallCycle X n b)) =
      positiveCircleCross X n (ModuleHomology.cycleClass (singularComplex X) n b) := by
  rw [positiveCircleSmallCycle_ambient_eq]
  exact (positiveCircleCross_arcSum_cycleClass X n b).symm

/-- The actual Mayer–Vietoris connecting class is the actual upper-minus-lower cycle class. -/
theorem circleConnecting_positiveCircleCross_cycleClass (n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    circleMayerVietorisConnecting X n
        (positiveCircleCross X n (ModuleHomology.cycleClass (singularComplex X) n b)) =
      ModuleHomology.cycleClass
        (singularComplex (productU X ∩ productV X : Set (Circle × X))) n
        (intersectionDifferenceCycle X n b) := by
  rw [← positiveCircleSmallCycle_ambient_class]
  exact connectingHomomorphism_twoChain (productU X) (productV X)
    (productU_open X) (productV_open X) (product_cover X) n
    (uCrossChain X n b) (vCrossChain X n b) (intersectionDifferenceCycle X n b)
    (uCrossChain_boundary X n b) (vCrossChain_boundary X n b)

/-- The component order fixes the raw sign of the positive circle cross product. -/
theorem circleBoundaryCoordinates_positiveCircleCross_cycleClass (n : ℕ)
    (b : ModuleHomology.Cycle (singularComplex X) n) :
    circleBoundaryCoordinates X n
        (positiveCircleCross X n (ModuleHomology.cycleClass (singularComplex X) n b)) =
      (-ModuleHomology.cycleClass (singularComplex X) n b,
        ModuleHomology.cycleClass (singularComplex X) n b) := by
  change productIntersectionHomologyEquiv X n
    (circleMayerVietorisConnecting X n
      (positiveCircleCross X n (ModuleHomology.cycleClass (singularComplex X) n b))) = _
  rw [circleConnecting_positiveCircleCross_cycleClass]
  exact intersectionDifferenceCycle_class_coordinates X n b

/-- In every degree, the actual positive circle cross product has raw connecting value `(-b,b)`. -/
theorem circleBoundaryCoordinates_positiveCircleCross (n : ℕ) (b : SingularHomology X n) :
    circleBoundaryCoordinates X n (positiveCircleCross X n b) = (-b, b) := by
  obtain ⟨c, rfl⟩ := ModuleHomology.cycleClass_surjective (singularComplex X) n b
  exact circleBoundaryCoordinates_positiveCircleCross_cycleClass X n c

/-- The marked signed circle boundary is a left inverse to the actual cross product. -/
@[simp] theorem circleBoundary_positiveCircleCross (n : ℕ) (b : SingularHomology X n) :
    circleBoundary X n (positiveCircleCross X n b) = b := by
  rw [circleBoundary_apply, circleBoundaryCoordinates_positiveCircleCross]
  exact neg_neg b

theorem positiveCircleCross_injective (n : ℕ) : Function.Injective (positiveCircleCross X n) :=
  (show Function.LeftInverse (circleBoundary X n) (positiveCircleCross X n)
    from circleBoundary_positiveCircleCross X n).injective

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
