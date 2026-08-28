import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductBoundary
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductTriangle
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductDescent

/-!
# The actual integral homology cross product with a degree-one factor

The signed edge boundary formula gives descent in the second factor. The
proved triangle boundary formula gives descent in the first factor. Hence
this bilinear operation is defined on actual categorical singular homology
classes in both factors, without assuming a product or comparison theorem.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris ModuleHomology

attribute [local instance] integerLinearMapModule integerTensorModule

/-- Cross products of genuine singular cycles, as a bilinear cycle map. -/
def crossProductCycles (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) :
    Cycle (singularComplex X) 1 →ₗ[ℤ] Cycle (singularComplex Y) n →ₗ[ℤ]
      Cycle (singularComplex (X × Y)) (n + 1) where
  toFun a :=
    { toFun b := mkCycle (singularComplex (X × Y)) (n + 1)
        (crossProductEdge X Y n a.1 b.1) (by
          rw [Nat.add_sub_cancel]
          exact crossProductEdge_cycle n a.1 b.1
            (cycle_condition (singularComplex X) 1 a)
            (cycle_condition (singularComplex Y) n b))
      map_add' b c := by
        apply Subtype.ext
        exact (crossProductEdge X Y n a.1).map_add b.1 c.1
      map_smul' r b := by
        apply Subtype.ext
        exact (crossProductEdge X Y n a.1).map_smul r b.1 }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun f : Chains Y n →ₗ[ℤ] Chains (X × Y) (n + 1) => f c.1)
      ((crossProductEdge X Y n).map_add a.1 b.1)
  map_smul' r a := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun f : Chains Y n →ₗ[ℤ] Chains (X × Y) (n + 1) => f c.1)
      ((crossProductEdge X Y n).map_smul r a.1)

@[simp] theorem crossProductCycles_val (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (a : Cycle (singularComplex X) 1) (b : Cycle (singularComplex Y) n) :
    (crossProductCycles X Y n a b).1 = crossProductEdge X Y n a.1 b.1 := rfl

/-- The homology class of a cycle cross product, before quotienting its inputs. -/
def crossProductCycleClasses (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) : Cycle (singularComplex X) 1 →ₗ[ℤ] Cycle (singularComplex Y) n →ₗ[ℤ]
      (singularComplex (X × Y)).homology (n + 1) :=
  integerBilinearPostcompose (crossProductCycles X Y n)
    (cycleClass (singularComplex (X × Y)) (n + 1))

@[simp] theorem crossProductCycleClasses_apply (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (a : Cycle (singularComplex X) 1) (b : Cycle (singularComplex Y) n) :
    crossProductCycleClasses X Y n a b =
      cycleClass (singularComplex (X × Y)) (n + 1) (crossProductCycles X Y n a b) := rfl

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- A boundary in the right factor produces a boundary, with the required minus sign. -/
theorem crossProductCycleClasses_boundary_right (n : ℕ)
    (a : Cycle (singularComplex X) 1) (b : Chains Y (n + 1)) :
    crossProductCycleClasses X Y n a (boundaryCycle (singularComplex Y) n b) = 0 := by
  apply (cycleClass_eq_zero_iff (singularComplex (X × Y)) (n + 1) _).mpr
  refine ⟨-crossProductEdge X Y (n + 1) a.1 b, ?_⟩
  change ((singularComplex (X × Y)).d (n + 2) (n + 1)).hom
      (-crossProductEdge X Y (n + 1) a.1 b) =
    crossProductEdge X Y n a.1 (((singularComplex Y).d (n + 1) n).hom b)
  rw [map_neg, crossProductEdge_boundary_of_left_cycle n a.1
    (cycle_condition (singularComplex X) 1 a), neg_neg]

/-- For a fixed left cycle, the product descends to actual homology in the right factor. -/
def crossProductHomologyFixed (n : ℕ) (a : Cycle (singularComplex X) 1) :
    (singularComplex Y).homology n →ₗ[ℤ] (singularComplex (X × Y)).homology (n + 1) :=
  homologyDesc (singularComplex Y) n (crossProductCycleClasses X Y n a)
    (crossProductCycleClasses_boundary_right n a)

@[simp] theorem crossProductHomologyFixed_cycleClass (n : ℕ)
    (a : Cycle (singularComplex X) 1) (b : Cycle (singularComplex Y) n) :
    crossProductHomologyFixed n a (cycleClass (singularComplex Y) n b) =
      cycleClass (singularComplex (X × Y)) (n + 1) (crossProductCycles X Y n a b) :=
  homologyDesc_cycleClass _ _ _ _ b

/-- The right-factor descent is still linear in the actual left cycle. -/
def crossProductHomologyCycles (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y]
    (n : ℕ) : Cycle (singularComplex X) 1 →ₗ[ℤ]
      ((singularComplex Y).homology n →ₗ[ℤ] (singularComplex (X × Y)).homology (n + 1)) where
  toFun a := crossProductHomologyFixed n a
  map_add' a b := by
    apply homologyLinearMap_ext (singularComplex Y) n
    intro c
    change crossProductHomologyFixed n (a + b) (cycleClass (singularComplex Y) n c) =
      crossProductHomologyFixed n a (cycleClass (singularComplex Y) n c) +
        crossProductHomologyFixed n b (cycleClass (singularComplex Y) n c)
    simp only [crossProductHomologyFixed_cycleClass]
    exact congrArg (fun f : Cycle (singularComplex Y) n →ₗ[ℤ]
      (singularComplex (X × Y)).homology (n + 1) => f c)
      ((crossProductCycleClasses X Y n).map_add a b)
  map_smul' r a := by
    apply homologyLinearMap_ext (singularComplex Y) n
    intro c
    simp only [LinearMap.smul_apply, RingHom.id_apply, crossProductHomologyFixed_cycleClass]
    exact congrArg (fun f : Cycle (singularComplex Y) n →ₗ[ℤ]
      (singularComplex (X × Y)).homology (n + 1) => f c)
      ((crossProductCycleClasses X Y n).map_smul r a)

/-- The triangle product proves invariance under boundaries in the left factor. -/
theorem crossProductCycleClasses_boundary_left (n : ℕ) (a : Chains X 2)
    (b : Cycle (singularComplex Y) n) :
    crossProductCycleClasses X Y n (boundaryCycle (singularComplex X) 1 a) b = 0 := by
  apply (cycleClass_eq_zero_iff (singularComplex (X × Y)) (n + 1) _).mpr
  refine ⟨crossProductTriangle X Y n a b.1, ?_⟩
  exact crossProductTriangle_boundary_of_right_cycle n a b.1
    (cycle_condition (singularComplex Y) n b)

theorem crossProductHomologyCycles_boundary_left (n : ℕ) (a : Chains X 2) :
    crossProductHomologyCycles X Y n (boundaryCycle (singularComplex X) 1 a) = 0 := by
  apply homologyLinearMap_ext (singularComplex Y) n
  intro b
  change crossProductHomologyFixed n (boundaryCycle (singularComplex X) 1 a)
    (cycleClass (singularComplex Y) n b) = 0
  rw [crossProductHomologyFixed_cycleClass]
  exact crossProductCycleClasses_boundary_left n a b

/-- The bilinear cross product on actual integral singular homology, in both factors. -/
def crossProductHomology (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ) :
    (singularComplex X).homology 1 →ₗ[ℤ]
      (singularComplex Y).homology n →ₗ[ℤ] (singularComplex (X × Y)).homology (n + 1) :=
  homologyDesc (singularComplex X) 1 (crossProductHomologyCycles X Y n)
    (crossProductHomologyCycles_boundary_left n)

/-- Both input homology classes are represented by the actual chain cross product. -/
@[simp] theorem crossProductHomology_cycleClass (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y] (n : ℕ)
    (a : Cycle (singularComplex X) 1) (b : Cycle (singularComplex Y) n) :
    crossProductHomology X Y n (cycleClass (singularComplex X) 1 a)
        (cycleClass (singularComplex Y) n b) =
      cycleClass (singularComplex (X × Y)) (n + 1) (crossProductCycles X Y n a b) := by
  rw [crossProductHomology, homologyDesc_cycleClass]
  exact crossProductHomologyFixed_cycleClass n a b

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
