import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryWangComponents

/-!
# Geometric evaluation of regular-intersection component maps

When a genuine map lands in a specified actual overlap component, its
three-component homology coordinates are concentrated in that component.
The remaining coefficient is the singular-homology map of its actual
upper-chart fibre coordinate. Thus component labels and fibre formulas
can be checked geometrically, without an assumed homology matrix.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SingularMayerVietoris PeriodTorusHigherHomology Homology

variable {X : Type} [TopologicalSpace X]
  (D : Data ℂ TriangleRegularPoint) (b : SlitBaseLift)

/-- Insert one class into the middle, left, or right coordinate, in that order. -/
def componentCoordinates {H : Type*} [Zero H] (i : Fin 3) (a : H) : H × (H × H) :=
  ![(a, (0, 0)), (0, (a, 0)), (0, (0, a))] i

@[simp] theorem componentCoordinates_zero {H : Type*} [Zero H] (a : H) :
    componentCoordinates 0 a = (a, (0, 0)) := rfl

@[simp] theorem componentCoordinates_one {H : Type*} [Zero H] (a : H) :
    componentCoordinates 1 a = (0, (a, 0)) := rfl

@[simp] theorem componentCoordinates_two {H : Type*} [Zero H] (a : H) :
    componentCoordinates 2 a = (0, (0, a)) := rfl

/-- The actual upper-chart fibre projection on an internal overlap component. -/
def pieceFibreProjection (i : Fin 3) : C(intersectionPiece D i, RealTorus₄) :=
  (overlapHomotopyEquiv D b (intersectionIndex i)).toFun.comp
    (intersectionPieceHomeomorph D i : C(_, _))

/-- The internal component homology marking is induced by this actual fibre projection. -/
theorem pieceFibreProjection_homology (i : Fin 3) (n : ℕ) :
    singularHomologyMap (pieceFibreProjection D b i) n =
      (intersectionPieceHomologyEquiv D b i n).toLinearMap := by
  rw [pieceFibreProjection, singularHomologyMap_comp]
  rfl

variable (C : C(X, familyIntersection D)) (i : Fin 3)
  (hC : ∀ x, C x ∈ intersectionPiece D i)

/-- Restrict the actual map to the component in which its image has been proved to lie. -/
def componentLift : C(X, intersectionPiece D i) :=
  ⟨fun x => ⟨C x, hC x⟩, C.continuous.subtype_mk _⟩

/-- The actual map is precisely its component lift followed by the literal inclusion. -/
theorem componentLift_factor :
    (openPartitionInclusion (intersectionPiece D) i).comp (componentLift D C i hC) = C := by
  apply ContinuousMap.ext
  intro x
  rfl

/-- Retain the complete actual fibre-coordinate map, including any affine translation. -/
def componentFibreMap : C(X, RealTorus₄) :=
  (pieceFibreProjection D b i).comp (componentLift D C i hC)

/-- The coefficient is the literal upper-chart fibre coordinate of the original map. -/
@[simp] theorem componentFibreMap_apply (x : X) :
    componentFibreMap D b C i hC x =
      (overlapChart D b (intersectionIndex i) ⟨(C x).val, hC x⟩).2 := rfl

/-- Its actual homology map is exactly the component homology coefficient. -/
theorem componentFibreMap_homology (n : ℕ) (a : SingularHomology X n) :
    singularHomologyMap (componentFibreMap D b C i hC) n a =
      intersectionPieceHomologyEquiv D b i n
        (singularHomologyMap (componentLift D C i hC) n a) := by
  rw [componentFibreMap, singularHomologyMap_comp, LinearMap.comp_apply,
    pieceFibreProjection_homology]
  rfl

/-- A geometrically verified component map occupies exactly the corresponding homology summand. -/
theorem intersectionHomology_componentMap (n : ℕ) (a : SingularHomology X n) :
    Homology.intersectionHomologyEquiv D b n (singularHomologyMap C n a) =
      componentCoordinates i (singularHomologyMap (componentFibreMap D b C i hC) n a) := by
  have hfactor : singularHomologyMap C n a =
      singularHomologyMap (openPartitionInclusion (intersectionPiece D) i) n
        (singularHomologyMap (componentLift D C i hC) n a) := by
    rw [← LinearMap.comp_apply, ← singularHomologyMap_comp, componentLift_factor]
  rw [hfactor, componentFibreMap_homology]
  fin_cases i
  · exact intersectionHomologyEquiv_inclusion_middle D b n _
  · exact intersectionHomologyEquiv_inclusion_left D b n _
  · exact intersectionHomologyEquiv_inclusion_right D b n _

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
