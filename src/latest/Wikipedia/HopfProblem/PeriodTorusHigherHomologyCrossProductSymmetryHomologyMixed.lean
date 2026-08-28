import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductHomology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductSymmetryMixed
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# The actual degree-two by degree-one homology cross product

The product is defined by swapping the already descended degree-one by
degree-two product. The mixed swap homotopy proves that its value on cycle
classes is the class of the actual triangle cross product. Thus the positive
mixed swap sign is proved on actual singular homology, not imposed on chain
representatives.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris ModuleHomology

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The actual triangle cross product of a two-cycle and a one-cycle. -/
def crossProductTwoOneCycles (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    Cycle (singularComplex X) 2 →ₗ[ℤ] Cycle (singularComplex Y) 1 →ₗ[ℤ]
      Cycle (singularComplex (X × Y)) 3 where
  toFun a :=
    { toFun b := mkCycle (singularComplex (X × Y)) 3
        (crossProductTriangle X Y 1 a.1 b.1) (by
          change ((singularComplex (X × Y)).d 3 2).hom
            (crossProductTriangle X Y 1 a.1 b.1) = 0
          simp only [crossProductTriangle_boundary,
            cycle_condition (singularComplex X) 2 a,
            cycle_condition (singularComplex Y) 1 b,
            map_zero, LinearMap.zero_apply, zero_add])
      map_add' b c := by
        apply Subtype.ext
        exact (crossProductTriangle X Y 1 a.1).map_add b.1 c.1
      map_smul' r b := by
        apply Subtype.ext
        exact (crossProductTriangle X Y 1 a.1).map_smul r b.1 }
  map_add' a b := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun f : Chains Y 1 →ₗ[ℤ] Chains (X × Y) 3 => f c.1)
      ((crossProductTriangle X Y 1).map_add a.1 b.1)
  map_smul' r a := by
    apply LinearMap.ext
    intro c
    apply Subtype.ext
    exact congrArg (fun f : Chains Y 1 →ₗ[ℤ] Chains (X × Y) 3 => f c.1)
      ((crossProductTriangle X Y 1).map_smul r a.1)

@[simp] theorem crossProductTwoOneCycles_val (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (a : Cycle (singularComplex X) 2) (b : Cycle (singularComplex Y) 1) :
    (crossProductTwoOneCycles X Y a b).1 = crossProductTriangle X Y 1 a.1 b.1 := rfl

/-- The degree-two by degree-one product on actual integral singular homology. -/
def crossProductHomologyTwoOne (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    SingularHomology X 2 →ₗ[ℤ] SingularHomology Y 1 →ₗ[ℤ] SingularHomology (X × Y) 3 :=
  integerBilinearPostcompose (integerBilinearFlip (crossProductHomology Y X 2))
    (singularHomologyMap ContinuousMap.prodSwap 3)

/-- The mixed product is the positive swap of the degree-one by degree-two product. -/
@[simp] theorem crossProductHomologyTwoOne_apply (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (a : SingularHomology X 2) (b : SingularHomology Y 1) :
    crossProductHomologyTwoOne X Y a b =
      singularHomologyMap ContinuousMap.prodSwap 3 (crossProductHomology Y X 2 b a) := rfl

/-- The mixed product on homology classes is represented by the actual triangle product. -/
@[simp] theorem crossProductHomologyTwoOne_cycleClass (X Y : Type)
    [TopologicalSpace X] [TopologicalSpace Y]
    (a : Cycle (singularComplex X) 2) (b : Cycle (singularComplex Y) 1) :
    crossProductHomologyTwoOne X Y (cycleClass (singularComplex X) 2 a)
        (cycleClass (singularComplex Y) 1 b) =
      cycleClass (singularComplex (X × Y)) 3 (crossProductTwoOneCycles X Y a b) := by
  rw [crossProductHomologyTwoOne_apply, crossProductHomology_cycleClass]
  change (HomologicalComplex.homologyMap (singularChainMap ContinuousMap.prodSwap) 3).hom
      (cycleClass (singularComplex (Y × X)) 3 (crossProductCycles Y X 2 b a)) = _
  rw [homologyMap_cycleClass]
  apply Eq.symm
  apply (cycleClass_eq_iff (singularComplex (X × Y)) 3 _ _).mpr
  refine ⟨crossProductMixedSwapHomotopy X Y a.1 b.1, ?_⟩
  simp only [crossProductTwoOneCycles_val, mapCycles_val, crossProductCycles_val]
  exact crossProductMixedSwapHomotopy_boundary_of_cycle a.1
    (cycle_condition (singularComplex X) 2 a) b.1

variable {X Y X' Y' : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

/-- Naturality of the actual mixed cycle cross product. -/
theorem crossProductTwoOneCycles_natural (f : C(X, X')) (g : C(Y, Y'))
    (a : Cycle (singularComplex X) 2) (b : Cycle (singularComplex Y) 1) :
    mapCycles (singularChainMap (f.prodMap g)) 3 (crossProductTwoOneCycles X Y a b) =
      crossProductTwoOneCycles X' Y' (mapCycles (singularChainMap f) 2 a)
        (mapCycles (singularChainMap g) 1 b) := by
  apply Subtype.ext
  simp only [mapCycles_val, crossProductTwoOneCycles_val]
  exact crossProductTriangle_natural f g 1 a.1 b.1

/-- Naturality of the actual degree-two by degree-one homology product. -/
theorem crossProductHomologyTwoOne_natural (f : C(X, X')) (g : C(Y, Y'))
    (a : SingularHomology X 2) (b : SingularHomology Y 1) :
    singularHomologyMap (f.prodMap g) 3 (crossProductHomologyTwoOne X Y a b) =
      crossProductHomologyTwoOne X' Y' (singularHomologyMap f 2 a)
        (singularHomologyMap g 1 b) := by
  obtain ⟨a, rfl⟩ := cycleClass_surjective (singularComplex X) 2 a
  obtain ⟨b, rfl⟩ := cycleClass_surjective (singularComplex Y) 1 b
  change (HomologicalComplex.homologyMap (singularChainMap (f.prodMap g)) 3).hom
      (crossProductHomologyTwoOne X Y (cycleClass (singularComplex X) 2 a)
        (cycleClass (singularComplex Y) 1 b)) =
    crossProductHomologyTwoOne X' Y'
      ((HomologicalComplex.homologyMap (singularChainMap f) 2).hom
        (cycleClass (singularComplex X) 2 a))
      ((HomologicalComplex.homologyMap (singularChainMap g) 1).hom
        (cycleClass (singularComplex Y) 1 b))
  rw [crossProductHomologyTwoOne_cycleClass, homologyMap_cycleClass,
    homologyMap_cycleClass, homologyMap_cycleClass, crossProductHomologyTwoOne_cycleClass,
    crossProductTwoOneCycles_natural]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
