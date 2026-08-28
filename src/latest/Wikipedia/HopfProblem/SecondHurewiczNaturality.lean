import Wikipedia.HopfProblem.SecondHurewiczMap

/-!
# Naturality of the actual second Hurewicz homomorphism

Postcomposition of the original cube map sends its singular square chain
to the new square chain. Passing through the actual cycle-class map gives
naturality with Mathlib's singular homology functor and the native induced
map on the second homotopy group.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SecondHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Naturality is a literal equality of actual singular square chains. -/
theorem squareChain_natural (f : C(X, Y)) (x : X) (p : GenLoop (Fin 2) X x) :
    inducedChain f 2 (squareChain p) = squareChain (mapGenLoop f x p) := by
  rw [squareChain_eq_induced, squareChain_eq_induced, mapGenLoop_val,
    inducedChain_comp, LinearMap.comp_apply]

theorem squareCycle_natural (f : C(X, Y)) (x : X) (p : GenLoop (Fin 2) X x) :
    ModuleHomology.mapCycles (singularChainMap f) 2 (squareCycle p) =
      squareCycle (mapGenLoop f x p) := by
  apply Subtype.ext
  rw [ModuleHomology.mapCycles_val, squareCycle_val, squareCycle_val]
  exact squareChain_natural f x p

theorem squareHomologyClass_natural (f : C(X, Y)) (x : X) (p : GenLoop (Fin 2) X x) :
    singularHomologyMap f 2 (squareHomologyClass p) =
      squareHomologyClass (mapGenLoop f x p) := by
  change (HomologicalComplex.homologyMap (singularChainMap f) 2).hom
    (ModuleHomology.cycleClass (singularComplex X) 2 (squareCycle p)) = _
  rw [ModuleHomology.homologyMap_cycleClass, squareCycle_natural]
  rfl

/-- Naturality on Mathlib's actual second homotopy group. -/
theorem hurewiczFunction_natural (f : C(X, Y)) (x : X) (a : π_ 2 X x) :
    singularHomologyMap f 2 (hurewiczFunction x a) =
      hurewiczFunction (f x) (homotopyMap f x a) := by
  refine Quotient.inductionOn a fun p => ?_
  exact squareHomologyClass_natural f x p

/-- Additive, integral-linear notation for the same naturality identity. -/
theorem hurewiczMap_natural (f : C(X, Y)) (x : X) (a : Additive (π_ 2 X x)) :
    singularHomologyMap f 2 (hurewiczMap x a) =
      hurewiczMap (f x) ((homotopyMap f x).toAdditive a) :=
  hurewiczFunction_natural f x a.toMul

end Wikipedia.HopfProblem.SecondHurewicz
