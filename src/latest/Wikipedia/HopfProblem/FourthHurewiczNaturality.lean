import Wikipedia.HopfProblem.FourthHurewiczMap

/-!
# Naturality of the actual fourth Hurewicz homomorphism

Postcomposition of the original cube map sends its actual singular
four-chain to the new cube chain. The native homotopy quotient and the
actual cycle-class map then give naturality with Mathlib's integral
singular homology functor and the induced map on its native `π₄`.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Naturality is a literal equality of actual singular four-cube chains. -/
theorem cubeChain_natural (f : C(X, Y)) (x : X) (p : GenLoop (Fin 4) X x) :
    inducedChain f 4 (cubeChain p) = cubeChain (SecondHurewicz.mapGenLoop f x p) := by
  rw [cubeChain_eq_induced, cubeChain_eq_induced, SecondHurewicz.mapGenLoop_val,
    inducedChain_comp, LinearMap.comp_apply]

theorem cubeCycle_natural (f : C(X, Y)) (x : X) (p : GenLoop (Fin 4) X x) :
    ModuleHomology.mapCycles (singularChainMap f) 4 (cubeCycle p) =
      cubeCycle (SecondHurewicz.mapGenLoop f x p) := by
  apply Subtype.ext
  rw [ModuleHomology.mapCycles_val, cubeCycle_val, cubeCycle_val]
  exact cubeChain_natural f x p

theorem cubeHomologyClass_natural (f : C(X, Y)) (x : X) (p : GenLoop (Fin 4) X x) :
    singularHomologyMap f 4 (cubeHomologyClass p) =
      cubeHomologyClass (SecondHurewicz.mapGenLoop f x p) := by
  change (HomologicalComplex.homologyMap (singularChainMap f) 4).hom
    (ModuleHomology.cycleClass (singularComplex X) 4 (cubeCycle p)) = _
  rw [ModuleHomology.homologyMap_cycleClass, cubeCycle_natural]
  rfl

/-- Naturality on Mathlib's actual fourth homotopy group. -/
theorem hurewiczFunction_natural (f : C(X, Y)) (x : X) (a : π_ 4 X x) :
    singularHomologyMap f 4 (hurewiczFunction x a) =
      hurewiczFunction (f x) (homotopyMap f x a) := by
  refine Quotient.inductionOn a fun p => ?_
  exact cubeHomologyClass_natural f x p

/-- Additive, integral-linear notation for the same naturality identity. -/
theorem hurewiczMap_natural (f : C(X, Y)) (x : X) (a : Additive (π_ 4 X x)) :
    singularHomologyMap f 4 (hurewiczMap x a) =
      hurewiczMap (f x) ((homotopyMap f x).toAdditive a) :=
  hurewiczFunction_natural f x a.toMul

end Wikipedia.HopfProblem.FourthHurewicz
