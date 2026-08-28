import Wikipedia.NoExoticSixSphere.RelativeSimplexCycles
import Wikipedia.NoExoticSixSphere.RelativeSingularHomologyMaps

/-!
# Maps of pairs on the original relative-simplex classes

The quotient chain formula comes from the actual cokernel comparison.
It identifies the mapped cycle and class with the simplex obtained by
composing the original continuous maps.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris
open SecondHurewicz.SimplyConnected

namespace NoExoticSixSphere.RelativeSimplexCycles

open RelativeSingularHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {U : Set X} {V : Set Y} (f : C(X, Y)) (hf : Set.MapsTo f U V)

def mapSimplex (n : ℕ) (smp : RelativeSimplex U n) : RelativeSimplex V n :=
  ⟨f.comp smp.val, fun s hs ↦ hf (smp.property s hs)⟩

theorem map_quotientMap (n : ℕ) (c : Chains X n) :
    ((mapChain f hf).f n).hom (quotientMap U n c) = quotientMap V n (inducedChain f n c) :=
  congrArg (fun g : singularComplex X ⟶ complex V ↦ (g.f n).hom c) (projection_mapChain f hf)

theorem map_cycle (n : ℕ) (smp : RelativeSimplex U (n + 1)) :
    ModuleHomology.mapCycles (mapChain f hf) (n + 1) (cycle U n smp) =
      cycle V n (mapSimplex f hf (n + 1) smp) := by
  apply Subtype.ext
  rw [ModuleHomology.mapCycles_val]
  change ((mapChain f hf).f (n + 1)).hom
    (quotientMap U (n + 1) (simplexChain X (n + 1) smp.val)) =
      quotientMap V (n + 1) (simplexChain Y (n + 1) (f.comp smp.val))
  rw [map_quotientMap, inducedChain_simplex]

theorem map_homologyClass (n : ℕ) (smp : RelativeSimplex U (n + 1)) :
    RelativeSingularHomology.map f hf (n + 1) (homologyClass U n smp) =
      homologyClass V n (mapSimplex f hf (n + 1) smp) := by
  change (HomologicalComplex.homologyMap (mapChain f hf) (n + 1)).hom
      (ModuleHomology.cycleClass (complex U) (n + 1) (cycle U n smp)) =
    ModuleHomology.cycleClass (complex V) (n + 1) (cycle V n (mapSimplex f hf (n + 1) smp))
  rw [ModuleHomology.homologyMap_cycleClass, map_cycle]

end NoExoticSixSphere.RelativeSimplexCycles
