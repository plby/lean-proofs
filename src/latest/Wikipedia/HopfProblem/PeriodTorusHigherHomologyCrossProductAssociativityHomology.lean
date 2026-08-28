import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductAssociativityBoundary
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductSymmetryHomologyMixed

/-!
# Associativity and cyclic symmetry of three actual one-dimensional classes

The actual associator cone and mixed swap cone identify the two iterated
products in singular degree three. Their consequence is invariance under a
cyclic permutation of three degree-one classes, with the literal permutation
of the three spaces. All identities take place in actual integral singular
homology.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris ModuleHomology

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The actual cone equates the two classes of iterated singular cycle products. -/
theorem crossProductCycleClasses_associative
    (a : Cycle (singularComplex X) 1) (b : Cycle (singularComplex Y) 1)
    (c : Cycle (singularComplex Z) 1) :
    (HomologicalComplex.homologyMap
      (singularChainMap (Homeomorph.prodAssoc X Y Z : C(_, _))) 3).hom
      (cycleClass (singularComplex ((X × Y) × Z)) 3
        (crossProductTwoOneCycles (X × Y) Z (crossProductCycles X Y 1 a b) c)) =
    cycleClass (singularComplex (X × (Y × Z))) 3
      (crossProductCycles X (Y × Z) 2 a (crossProductCycles Y Z 1 b c)) := by
  rw [homologyMap_cycleClass]
  apply (cycleClass_eq_iff (singularComplex (X × (Y × Z))) 3 _ _).mpr
  refine ⟨crossProductAssociatorHomotopy X Y Z 1 a.1 b.1 c.1, ?_⟩
  simp only [mapCycles_val, crossProductTwoOneCycles_val, crossProductCycles_val]
  exact crossProductAssociatorHomotopy_boundary_of_cycle 1 a.1 b.1 c.1
    (cycle_condition (singularComplex Z) 1 c)

/-- Reassociation identifies the actual products of three degree-one classes. -/
theorem crossProductHomology_associative
    (a : SingularHomology X 1) (b : SingularHomology Y 1) (c : SingularHomology Z 1) :
    singularHomologyMap (Homeomorph.prodAssoc X Y Z : C(_, _)) 3
        (crossProductHomologyTwoOne (X × Y) Z (crossProductHomology X Y 1 a b) c) =
      crossProductHomology X (Y × Z) 2 a (crossProductHomology Y Z 1 b c) := by
  obtain ⟨a, rfl⟩ := cycleClass_surjective (singularComplex X) 1 a
  obtain ⟨b, rfl⟩ := cycleClass_surjective (singularComplex Y) 1 b
  obtain ⟨c, rfl⟩ := cycleClass_surjective (singularComplex Z) 1 c
  rw [crossProductHomology_cycleClass, crossProductHomologyTwoOne_cycleClass,
    crossProductHomology_cycleClass, crossProductHomology_cycleClass]
  exact crossProductCycleClasses_associative a b c

/-- The literal cyclic permutation sending `(y,(z,x))` to `(x,(y,z))`. -/
def crossProductCyclicMap (X Y Z : Type)
    [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z] :
    C(Y × (Z × X), X × (Y × Z)) :=
  ContinuousMap.prodSwap.comp ((Homeomorph.prodAssoc Y Z X).symm : C(_, _))

@[simp] theorem crossProductCyclicMap_apply (p : Y × (Z × X)) :
    crossProductCyclicMap X Y Z p = (p.2.2, (p.1, p.2.1)) := rfl

/-- The cyclic map undoes the corresponding swapped reassociation. -/
theorem crossProductCyclicMap_assoc_swap :
    (crossProductCyclicMap X Y Z).comp
        ((Homeomorph.prodAssoc Y Z X : C(_, _)).comp ContinuousMap.prodSwap) =
      ContinuousMap.id (X × (Y × Z)) := rfl

/-- Cyclic permutation has positive sign on three actual degree-one classes. -/
theorem crossProductHomology_cyclic
    (a : SingularHomology X 1) (b : SingularHomology Y 1) (c : SingularHomology Z 1) :
    crossProductHomology X (Y × Z) 2 a (crossProductHomology Y Z 1 b c) =
      singularHomologyMap (crossProductCyclicMap X Y Z) 3
        (crossProductHomology Y (Z × X) 2 b (crossProductHomology Z X 1 c a)) := by
  have h := crossProductHomology_associative b c a
  rw [crossProductHomologyTwoOne_apply] at h
  have h' := congrArg (singularHomologyMap (crossProductCyclicMap X Y Z) 3) h
  have hmap : (singularHomologyMap (crossProductCyclicMap X Y Z) 3).comp
        ((singularHomologyMap (Homeomorph.prodAssoc Y Z X : C(_, _)) 3).comp
          (singularHomologyMap (ContinuousMap.prodSwap : C(X × (Y × Z), (Y × Z) × X)) 3)) =
      LinearMap.id := by
    rw [← singularHomologyMap_comp, ← singularHomologyMap_comp,
      crossProductCyclicMap_assoc_swap, singularHomologyMap_id]
  exact (LinearMap.congr_fun hmap
    (crossProductHomology X (Y × Z) 2 a (crossProductHomology Y Z 1 b c))).symm.trans h'

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
