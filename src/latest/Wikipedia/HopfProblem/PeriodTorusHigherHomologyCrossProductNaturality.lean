import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductHomology

/-!
# Naturality of the actual homology cross product

All maps here are Mathlib's induced singular homology maps. Naturality follows
on actual cycle representatives from the naturality of the chain construction.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris ModuleHomology

attribute [local instance] integerLinearMapModule integerTensorModule

variable {X Y X' Y' : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace X'] [TopologicalSpace Y']

/-- The concrete actual cycle cross product commutes with induced maps. -/
theorem crossProductCycles_natural (f : C(X, X')) (g : C(Y, Y')) (n : ℕ)
    (a : Cycle (singularComplex X) 1) (b : Cycle (singularComplex Y) n) :
    mapCycles (singularChainMap (f.prodMap g)) (n + 1) (crossProductCycles X Y n a b) =
      crossProductCycles X' Y' n (mapCycles (singularChainMap f) 1 a)
        (mapCycles (singularChainMap g) n b) := by
  apply Subtype.ext
  simp only [mapCycles_val, crossProductCycles_val]
  exact crossProductEdge_natural f g n a.1 b.1

/-- Naturality of the bilinear cross product on actual singular homology. -/
theorem crossProductHomology_natural (f : C(X, X')) (g : C(Y, Y')) (n : ℕ)
    (a : (singularComplex X).homology 1) (b : (singularComplex Y).homology n) :
    (HomologicalComplex.homologyMap (singularChainMap (f.prodMap g)) (n + 1)).hom
        (crossProductHomology X Y n a b) =
      crossProductHomology X' Y' n
        ((HomologicalComplex.homologyMap (singularChainMap f) 1).hom a)
        ((HomologicalComplex.homologyMap (singularChainMap g) n).hom b) := by
  obtain ⟨a, rfl⟩ := cycleClass_surjective (singularComplex X) 1 a
  obtain ⟨b, rfl⟩ := cycleClass_surjective (singularComplex Y) n b
  rw [crossProductHomology_cycleClass, homologyMap_cycleClass,
    homologyMap_cycleClass, homologyMap_cycleClass, crossProductHomology_cycleClass,
    crossProductCycles_natural]

/-- Fixing an actual left cycle agrees with evaluating the descended left homology factor. -/
theorem crossProductHomologyFixed_eq (n : ℕ) (a : Cycle (singularComplex X) 1) :
    crossProductHomologyFixed (Y := Y) n a =
      crossProductHomology X Y n (cycleClass (singularComplex X) 1 a) := by
  apply homologyLinearMap_ext (singularComplex Y) n
  intro b
  rw [crossProductHomologyFixed_cycleClass, crossProductHomology_cycleClass]

/-- Equality of left homology classes gives equality of the entire fixed-cycle operation. -/
theorem crossProductHomologyFixed_eq_of_class_eq (n : ℕ)
    (a a' : Cycle (singularComplex X) 1)
    (h : cycleClass (singularComplex X) 1 a = cycleClass (singularComplex X) 1 a') :
    crossProductHomologyFixed (Y := Y) n a = crossProductHomologyFixed n a' := by
  rw [crossProductHomologyFixed_eq, crossProductHomologyFixed_eq, h]

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
