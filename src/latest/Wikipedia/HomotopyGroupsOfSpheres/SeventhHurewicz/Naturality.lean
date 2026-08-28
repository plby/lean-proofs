import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.Map
import Wikipedia.HomotopyGroupsOfSpheres.PointedMaps

/-! # Naturality of the seventh Hurewicz map on actual cubes and pointed maps -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem
open FirstHurewicz SingularMayerVietoris

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem hurewiczMap_ofMul (x : X) (a : π_ 7 X x) :
    hurewiczMap x (Additive.ofMul a) = hurewiczFunction x a := rfl

theorem hurewiczPi7_toAdd (x : X) (a : π_ 7 X x) :
    (hurewiczPi7 x a).toAdd = hurewiczFunction x a := rfl

theorem cubeChain_natural (f : C(X, Y)) (x : X) (p : GenLoop (Fin 7) X x) :
    inducedChain f 7 (cubeChain p) = cubeChain (SecondHurewicz.mapGenLoop f x p) := by
  rw [cubeChain_eq_induced, cubeChain_eq_induced, SecondHurewicz.mapGenLoop_val,
    inducedChain_comp, LinearMap.comp_apply]

theorem cubeCycle_natural (f : C(X, Y)) (x : X) (p : GenLoop (Fin 7) X x) :
    ModuleHomology.mapCycles (singularChainMap f) 7 (cubeCycle p) =
      cubeCycle (SecondHurewicz.mapGenLoop f x p) := by
  apply Subtype.ext
  rw [ModuleHomology.mapCycles_val, cubeCycle_val, cubeCycle_val]
  exact cubeChain_natural f x p

theorem cubeHomologyClass_natural (f : C(X, Y)) (x : X) (p : GenLoop (Fin 7) X x) :
    singularHomologyMap f 7 (cubeHomologyClass p) =
      cubeHomologyClass (SecondHurewicz.mapGenLoop f x p) := by
  change (HomologicalComplex.homologyMap (singularChainMap f) 7).hom
    (ModuleHomology.cycleClass (singularComplex X) 7 (cubeCycle p)) = _
  rw [ModuleHomology.homologyMap_cycleClass, cubeCycle_natural]
  rfl

theorem hurewiczFunction_natural (f : C(X, Y)) (x : X) (a : π_ 7 X x) :
    singularHomologyMap f 7 (hurewiczFunction x a) =
      hurewiczFunction (f x) (homotopyMap f x a) := by
  refine Quotient.inductionOn a fun p ↦ ?_
  exact cubeHomologyClass_natural f x p

theorem hurewiczFunction_map_natural (f : C(X, Y)) (x : X) (a : π_ 7 X x) :
    singularHomologyMap f 7 (hurewiczFunction x a) =
      hurewiczFunction (f x) (Wikipedia.HomotopyGroupsOfSpheres.map f x a) := by
  refine Quotient.inductionOn a fun p ↦ ?_
  exact cubeHomologyClass_natural f x p

theorem hurewiczFunction_homeomorph_natural (e : X ≃ₜ Y) (x : X) (a : π_ 7 X x) :
    singularHomologyMap (e : C(X, Y)) 7 (hurewiczFunction x a) =
      hurewiczFunction (e x) (homeomorphMulEquiv (N := Fin 7) e x a) := by
  refine Quotient.inductionOn a fun p ↦ ?_
  exact cubeHomologyClass_natural (e : C(X, Y)) x p

theorem hurewiczFunction_pointed_natural (f : C(X, Y)) (x : X) (y : Y) (h : f x = y)
    (a : π_ 7 X x) :
    singularHomologyMap f 7 (hurewiczFunction x a) =
      hurewiczFunction y (pointedMap f x y h a) := by
  cases h
  exact hurewiczFunction_natural f x a

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
