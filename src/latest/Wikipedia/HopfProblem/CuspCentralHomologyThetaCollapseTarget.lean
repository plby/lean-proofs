import Wikipedia.HopfProblem.CuspCentralHomologyThetaCollapseTopology
import Wikipedia.HopfProblem.CuspCentralHomologyThetaCollapseCover
import Wikipedia.HopfProblem.CuspCentralHomologySuspensionCircles

/-!
# Coordinates on the target belt of the actual theta collapse

The three literal circle inclusions give the three separate integral
homology coordinates.  The midpoint section into the suspension's open
middle band preserves these coordinates under the constructed homotopy
equivalence with the three circles.
-/

namespace Wikipedia.HopfProblem.CuspCentralHomology

open SingularMayerVietoris PeriodTorusHigherHomology

/-- The continuous inclusion of the circle carrying the indicated edge label. -/
def thetaCircleMap (j : Fin 3) : C(_root_.Circle, ThreeCircles) :=
  ⟨thetaCircleInclusion j, thetaCircleInclusion_continuous j⟩

theorem thetaCircleMap_apply (j : Fin 3) (z : _root_.Circle) :
    thetaCircleMap j z = thetaCircleInclusion j z := rfl

theorem thetaCircleMap_zero :
    thetaCircleMap 0 = sumInlMap _root_.Circle (_root_.Circle ⊕ _root_.Circle) := rfl

theorem thetaCircleMap_one :
    thetaCircleMap 1 =
      (sumInrMap _root_.Circle (_root_.Circle ⊕ _root_.Circle)).comp
        (sumInlMap _root_.Circle _root_.Circle) := rfl

theorem thetaCircleMap_two :
    thetaCircleMap 2 =
      (sumInrMap _root_.Circle (_root_.Circle ⊕ _root_.Circle)).comp
        (sumInrMap _root_.Circle _root_.Circle) := rfl

private theorem threeCirclesHomologySplit_apply (n : ℕ)
    (a : SingularHomology ThreeCircles n) :
    threeCirclesHomologySplit n a =
      ((sumHomologyEquiv _root_.Circle (_root_.Circle ⊕ _root_.Circle) n a).1,
        sumHomologyEquiv _root_.Circle _root_.Circle n
          (sumHomologyEquiv _root_.Circle (_root_.Circle ⊕ _root_.Circle) n a).2) := rfl

/-- The actual disjoint-union splitting sends each circle to its own summand. -/
theorem thetaCircleMap_homologySplit (j : Fin 3) (n : ℕ)
    (a : SingularHomology _root_.Circle n) :
    threeCirclesHomologySplit n (singularHomologyMap (thetaCircleMap j) n a) =
      ![(a, (0, 0)), (0, (a, 0)), (0, (0, a))] j := by
  fin_cases j <;>
    simp [thetaCircleMap_zero, thetaCircleMap_one, thetaCircleMap_two,
      singularHomologyMap_comp, threeCirclesHomologySplit_apply]
  rfl

private theorem threeCirclesHomologyOneEquiv_apply
    (a : SingularHomology ThreeCircles 1) :
    threeCirclesHomologyOneEquiv a =
      ![unitCircleHomologyOneEquiv (threeCirclesHomologySplit 1 a).1,
        unitCircleHomologyOneEquiv (threeCirclesHomologySplit 1 a).2.1,
        unitCircleHomologyOneEquiv (threeCirclesHomologySplit 1 a).2.2] := rfl

/-- The actual first homology map of the `j`th circle inclusion is the
`j`th coordinate inclusion, with the existing unit-circle orientation. -/
theorem thetaCircleMap_homologyOne (j : Fin 3)
    (a : SingularHomology _root_.Circle 1) :
    threeCirclesHomologyOneEquiv (singularHomologyMap (thetaCircleMap j) 1 a) =
      Pi.single j (unitCircleHomologyOneEquiv a) := by
  rw [threeCirclesHomologyOneEquiv_apply, thetaCircleMap_homologySplit]
  fin_cases j <;> funext k <;> fin_cases k <;> simp

/-- The target belt coordinates are induced by its actual homotopy equivalence. -/
noncomputable def thetaTargetBeltHomologyEquiv :
    SingularHomology (Suspension.middleBand ThreeCircles) 1 ≃ₗ[ℤ] (Fin 3 → ℤ) :=
  (homotopyEquivHomologyEquiv
    (Suspension.middleBandHomotopyEquiv (X := ThreeCircles)) 1).trans
      threeCirclesHomologyOneEquiv

theorem thetaTargetBeltHomologyEquiv_apply
    (a : SingularHomology (Suspension.middleBand ThreeCircles) 1) :
    thetaTargetBeltHomologyEquiv a =
      threeCirclesHomologyOneEquiv (singularHomologyMap
        (Suspension.middleBandHomotopyEquiv (X := ThreeCircles)).toFun 1 a) := rfl

/-- The midpoint section has exactly the original three-circle coordinates. -/
theorem thetaTargetBeltHomologyEquiv_middleSection
    (a : SingularHomology ThreeCircles 1) :
    thetaTargetBeltHomologyEquiv
      (singularHomologyMap (suspensionMiddleSection ThreeCircles) 1 a) =
        threeCirclesHomologyOneEquiv a := by
  have hsection :
      (Suspension.middleBandHomotopyEquiv (X := ThreeCircles)).toFun.comp
        (suspensionMiddleSection ThreeCircles) = ContinuousMap.id ThreeCircles := by
    apply ContinuousMap.ext
    exact suspensionMiddleSection_label ThreeCircles
  change threeCirclesHomologyOneEquiv
    (((singularHomologyMap
      (Suspension.middleBandHomotopyEquiv (X := ThreeCircles)).toFun 1).comp
        (singularHomologyMap (suspensionMiddleSection ThreeCircles) 1)) a) = _
  rw [← singularHomologyMap_comp, hsection, singularHomologyMap_id]
  rfl

/-- A labeled circle at the literal midpoint gives its single target coordinate. -/
theorem thetaTargetBeltHomologyEquiv_middleSection_circle (j : Fin 3)
    (a : SingularHomology _root_.Circle 1) :
    thetaTargetBeltHomologyEquiv
      (singularHomologyMap
        ((suspensionMiddleSection ThreeCircles).comp (thetaCircleMap j)) 1 a) =
          Pi.single j (unitCircleHomologyOneEquiv a) := by
  rw [singularHomologyMap_comp, LinearMap.comp_apply,
    thetaTargetBeltHomologyEquiv_middleSection, thetaCircleMap_homologyOne]

end Wikipedia.HopfProblem.CuspCentralHomology
