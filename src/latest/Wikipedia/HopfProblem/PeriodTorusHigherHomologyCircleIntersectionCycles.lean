import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePaths
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleProductMaps
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleConnectingCycles

/-!
# Concrete intersection cycles for the positive circle product

The quarter and three-quarter sections lie in the first and second actual
intersection components. Their induced homology maps have coordinates
`(a,0)` and `(0,a)` under the proved intersection equivalence. The difference
of the two actual image cycles therefore has coordinates `(-a,a)`, with
the sign determined by the positive arc orientation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris ModuleHomology CircleTopology CirclePaths

variable (X : Type) [TopologicalSpace X]

/-- The actual quarter section gives the first intersection homology summand. -/
theorem quarterIntersectionHomology_coordinates (n : ℕ) (a : SingularHomology X n) :
    productIntersectionHomologyEquiv X n
        (singularHomologyMap (quarterIntersectionSection X) n a) = (a, 0) := by
  rw [productIntersectionHomologyEquiv_apply, ← LinearMap.comp_apply,
    ← singularHomologyMap_comp, quarterIntersectionSection_comp]
  exact sumHomologyEquiv_inl X X n a

/-- The actual three-quarter section gives the second intersection homology summand. -/
theorem threeQuarterIntersectionHomology_coordinates (n : ℕ) (a : SingularHomology X n) :
    productIntersectionHomologyEquiv X n
        (singularHomologyMap (threeQuarterIntersectionSection X) n a) = (0, a) := by
  rw [productIntersectionHomologyEquiv_apply, ← LinearMap.comp_apply,
    ← singularHomologyMap_comp, threeQuarterIntersectionSection_comp]
  exact sumHomologyEquiv_inr X X n a

/-- The actual upper-minus-lower intersection cycle associated with a cycle
in the unchanged factor. -/
def intersectionDifferenceCycle (n : ℕ) (b : Cycle (singularComplex X) n) :
    Cycle (singularComplex (productU X ∩ productV X : Set (Circle × X))) n :=
  mapCycles (singularChainMap (threeQuarterIntersectionSection X)) n b -
    mapCycles (singularChainMap (quarterIntersectionSection X)) n b

/-- The underlying actual chain is the difference of the two induced section chains. -/
@[simp] theorem intersectionDifferenceCycle_val (n : ℕ) (b : Cycle (singularComplex X) n) :
    (intersectionDifferenceCycle X n b).1 =
      inducedChain (threeQuarterIntersectionSection X) n b.1 -
        inducedChain (quarterIntersectionSection X) n b.1 := by
  change (mapCycles (singularChainMap (threeQuarterIntersectionSection X)) n b).1 -
    (mapCycles (singularChainMap (quarterIntersectionSection X)) n b).1 = _
  rw [mapCycles_val, mapCycles_val]

/-- The actual difference cycle represents exactly `(-[b],[b])` in the
fixed lower-first intersection homology coordinates. -/
theorem intersectionDifferenceCycle_class_coordinates (n : ℕ)
    (b : Cycle (singularComplex X) n) :
    productIntersectionHomologyEquiv X n
        (cycleClass (singularComplex (productU X ∩ productV X : Set (Circle × X))) n
          (intersectionDifferenceCycle X n b)) =
      (-cycleClass (singularComplex X) n b, cycleClass (singularComplex X) n b) := by
  rw [intersectionDifferenceCycle, map_sub, map_sub,
    ← homologyMap_cycleClass, ← homologyMap_cycleClass]
  change productIntersectionHomologyEquiv X n
      (singularHomologyMap (threeQuarterIntersectionSection X) n
        (cycleClass (singularComplex X) n b)) -
    productIntersectionHomologyEquiv X n
      (singularHomologyMap (quarterIntersectionSection X) n
        (cycleClass (singularComplex X) n b)) = _
  rw [threeQuarterIntersectionHomology_coordinates, quarterIntersectionHomology_coordinates]
  simp only [Prod.mk_sub_mk, zero_sub, sub_zero]

/-- Through the first product chart, the lower intersection section is
literally insertion of the lower endpoint in the first arc. -/
theorem quarterIntersectionSection_toU :
    (productIntersectionToU X).comp (quarterIntersectionSection X) =
      ((productUHomeomorph X).symm : C(arcU × X, productU X)).comp
        ((ContinuousMap.const X quarterU).prodMk (ContinuousMap.id X)) := rfl

/-- The same lower endpoint insertion in the second arc. -/
theorem quarterIntersectionSection_toV :
    (productIntersectionToV X).comp (quarterIntersectionSection X) =
      ((productVHomeomorph X).symm : C(arcV × X, productV X)).comp
        ((ContinuousMap.const X quarterV).prodMk (ContinuousMap.id X)) := rfl

/-- The upper intersection section is literal upper endpoint insertion in the first arc. -/
theorem threeQuarterIntersectionSection_toU :
    (productIntersectionToU X).comp (threeQuarterIntersectionSection X) =
      ((productUHomeomorph X).symm : C(arcU × X, productU X)).comp
        ((ContinuousMap.const X threeQuarterU).prodMk (ContinuousMap.id X)) := rfl

/-- The upper intersection section is literal upper endpoint insertion in the second arc. -/
theorem threeQuarterIntersectionSection_toV :
    (productIntersectionToV X).comp (threeQuarterIntersectionSection X) =
      ((productVHomeomorph X).symm : C(arcV × X, productV X)).comp
        ((ContinuousMap.const X threeQuarterV).prodMk (ContinuousMap.id X)) := rfl

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
