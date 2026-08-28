import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductSymmetry
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductHomology
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Signed symmetry of the actual degree-one homology cross product

The actual swap cone gives the negative sign on integral degree-two homology.
In particular the sign is proved from a singular boundary, not assumed as a
property of a replacement product or an exterior-algebra model.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris ModuleHomology

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The signed swap cone annihilates the sum of the two actual cycle classes. -/
theorem crossProductCycleClasses_add_swap_eq_zero
    (a : Cycle (singularComplex X) 1) (b : Cycle (singularComplex Y) 1) :
    crossProductCycleClasses X Y 1 a b +
        singularHomologyMap ContinuousMap.prodSwap 2 (crossProductCycleClasses Y X 1 b a) =
      0 := by
  change cycleClass (singularComplex (X × Y)) 2 (crossProductCycles X Y 1 a b) +
      (HomologicalComplex.homologyMap (singularChainMap ContinuousMap.prodSwap) 2).hom
        (cycleClass (singularComplex (Y × X)) 2 (crossProductCycles Y X 1 b a)) = 0
  rw [homologyMap_cycleClass, ← map_add]
  apply (cycleClass_eq_zero_iff (singularComplex (X × Y)) 2 _).mpr
  refine ⟨crossProductSwapHomotopy X Y a.1 b.1, ?_⟩
  rw [Submodule.coe_add, mapCycles_val]
  exact crossProductSwapHomotopy_boundary a.1 b.1

/-- The degree-one cross product is graded-commutative on actual singular homology. -/
theorem crossProductHomology_add_swap_eq_zero
    (a : SingularHomology X 1) (b : SingularHomology Y 1) :
    crossProductHomology X Y 1 a b +
        singularHomologyMap ContinuousMap.prodSwap 2 (crossProductHomology Y X 1 b a) =
      0 := by
  obtain ⟨a, rfl⟩ := cycleClass_surjective (singularComplex X) 1 a
  obtain ⟨b, rfl⟩ := cycleClass_surjective (singularComplex Y) 1 b
  rw [crossProductHomology_cycleClass, crossProductHomology_cycleClass]
  exact crossProductCycleClasses_add_swap_eq_zero a b

/-- Swapping the factors acts by the expected minus sign in bidegree `(1,1)`. -/
theorem crossProductHomology_swap
    (a : SingularHomology X 1) (b : SingularHomology Y 1) :
    singularHomologyMap ContinuousMap.prodSwap 2 (crossProductHomology X Y 1 a b) =
      -crossProductHomology Y X 1 b a := by
  have h := crossProductHomology_add_swap_eq_zero b a
  exact eq_neg_of_add_eq_zero_right h

/-- A symmetric continuous map turns the actual cross product into an
anticommutative operation on degree-one homology classes. -/
theorem crossProductHomology_pushforward_anticommute (f : C(X × X, Z))
    (hf : f.comp ContinuousMap.prodSwap = f)
    (a b : SingularHomology X 1) :
    singularHomologyMap f 2 (crossProductHomology X X 1 a b) =
      -singularHomologyMap f 2 (crossProductHomology X X 1 b a) := by
  have h := congrArg (singularHomologyMap f 2) (crossProductHomology_swap a b)
  rw [map_neg] at h
  have hc := LinearMap.congr_fun
    (singularHomologyMap_comp (ContinuousMap.prodSwap : C(X × X, X × X)) f 2)
    (crossProductHomology X X 1 a b)
  rw [hf] at hc
  exact hc.trans h

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
