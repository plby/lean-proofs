import Wikipedia.HopfProblem.SixSphereCubeFactorization
import Wikipedia.HopfProblem.SixthHurewiczNaturality

/-!
# Exact sixth Hurewicz compatibility of the genuine sphere factorization

The induced map sends the actual cube cycle of the quotient map to the
original cube cycle, and therefore sends its actual homology class to
the original Hurewicz class. No sphere orientation, generator assertion,
connectivity condition, or homology equivalence is assumed.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SixSphereCube

open FirstHurewicz SingularMayerVietoris

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {x : X}

/-- Uniqueness of the genuine quotient lift gives naturality under continuous postcomposition. -/
theorem factorMap_natural (f : C(X, Y)) (p : GenLoop (Fin 6) X x) :
    factorMap (SecondHurewicz.mapGenLoop f x p) = f.comp (factorMap p) := by
  symm
  apply factorMap_unique
  ext u
  change f (factorMap p (cubeSphereMap u)) = f (p u)
  rw [factorMap_cubeSphereMap]

/-- Exact equality of the actual singular six-chains, not just their homology classes. -/
theorem factor_cubeChain (p : GenLoop (Fin 6) X x) :
    inducedChain (factorMap p) 6 (SixthHurewicz.cubeChain cubeSphereLoop) =
      SixthHurewicz.cubeChain p := by
  calc
    _ = inducedChain ((factorMap p).comp cubeSphereMap) 6
        SixthHurewicz.fundamentalCubeChain := by
      rw [SixthHurewicz.cubeChain_eq_induced, cubeSphereLoop_val, inducedChain_comp,
        LinearMap.comp_apply]
    _ = _ := by
      rw [factorMap_comp_cubeSphereMap, SixthHurewicz.cubeChain_eq_induced]

/-- The induced chain map preserves the original native cube cycles exactly. -/
theorem factor_cubeCycle (p : GenLoop (Fin 6) X x) :
    ModuleHomology.mapCycles (singularChainMap (factorMap p)) 6
        (SixthHurewicz.cubeCycle cubeSphereLoop) =
      SixthHurewicz.cubeCycle p := by
  apply Subtype.ext
  rw [ModuleHomology.mapCycles_val, SixthHurewicz.cubeCycle_val, SixthHurewicz.cubeCycle_val]
  exact factor_cubeChain p

/-- The actual sphere map carries the quotient cube's class to the original cube's class. -/
theorem factor_cubeHomologyClass (p : GenLoop (Fin 6) X x) :
    singularHomologyMap (factorMap p) 6 (SixthHurewicz.cubeHomologyClass cubeSphereLoop) =
      SixthHurewicz.cubeHomologyClass p := by
  change (HomologicalComplex.homologyMap (singularChainMap (factorMap p)) 6).hom
    (ModuleHomology.cycleClass (singularComplex StandardSphere) 6
      (SixthHurewicz.cubeCycle cubeSphereLoop)) = _
  rw [ModuleHomology.homologyMap_cycleClass, factor_cubeCycle]
  rfl

/-- This is the commuting square for the genuine original native sixth Hurewicz maps. -/
theorem factor_hurewiczMap (p : GenLoop (Fin 6) X x) :
    singularHomologyMap (factorMap p) 6
        (SixthHurewicz.hurewiczMap sphereBasePoint
          (Additive.ofMul (⟦cubeSphereLoop⟧ : π_ 6 StandardSphere sphereBasePoint))) =
      SixthHurewicz.hurewiczMap x (Additive.ofMul (⟦p⟧ : π_ 6 X x)) :=
  factor_cubeHomologyClass p

end Wikipedia.HopfProblem.SixSphereCube
