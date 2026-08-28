import Wikipedia.NoExoticSixSphere.SingularHomotopyPrismNaturality
import Wikipedia.NoExoticSixSphere.RelativeFiberConnecting
import Wikipedia.NoExoticSixSphere.RelativeFiberMap

/-!
# Naturality of the original fiber-to-relative-homology transgression

The actual evaluation homotopies form a commuting square. Naturality of
Mathlib's signed singular prism gives the ambient and relative chain
identities, and the original categorical homology construction descends
them. No different prism or abstract homology isomorphism is substituted.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris ModuleHomology
open PeriodTorusHigherHomology OrbitPair

namespace NoExoticSixSphere.RelativeFiberHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {U : Set X} {V : Set Y} (f : C(X, Y)) (hf : Set.MapsTo f U V)
  (a : U) (b : V) (hab : f a.val = b.val)

theorem ambientPrism_natural (n : ℕ) (c : Chains (Fiber U a) n) :
    inducedChain f (n + 1) (ambientPrism U a n c) =
      ambientPrism V b n (inducedChain (RelativeFiberMap.map f hf a b hab) n c) :=
  SingularHomotopyPrismNaturality.component_natural_apply
    (HomotopyFiber.projectionNullhomotopy (subtypeInclusion U) a).toHomotopy
    (HomotopyFiber.projectionNullhomotopy (subtypeInclusion V) b).toHomotopy
    (RelativeFiberMap.map f hf a b hab) f rfl n c

theorem relativePrism_natural (n : ℕ) (c : Chains (Fiber U a) n) :
    ((RelativeSingularHomology.mapChain f hf).f (n + 1)).hom
      (ChainHomotopyDegreeShift.prism (prism U a) n c) =
        ChainHomotopyDegreeShift.prism (prism V b) n
          (inducedChain (RelativeFiberMap.map f hf a b hab) n c) := by
  rw [← quotient_ambientPrism, ← quotient_ambientPrism,
    RelativeSimplexCycles.map_quotientMap, ambientPrism_natural f hf a b hab]

theorem transgression_natural (n : ℕ) (z : SingularHomology (Fiber U a) n) :
    RelativeSingularHomology.map f hf (n + 1) (transgression U a n z) =
      transgression V b n (singularHomologyMap (RelativeFiberMap.map f hf a b hab) n z) := by
  obtain ⟨c, rfl⟩ := cycleClass_surjective (singularComplex (Fiber U a)) n z
  rw [transgression_cycleClass]
  change (HomologicalComplex.homologyMap (RelativeSingularHomology.mapChain f hf) (n + 1)).hom
    (cycleClass (RelativeSingularHomology.complex U) (n + 1)
      (ChainHomotopyDegreeShift.cycleMap (prism U a) n c)) = _
  rw [homologyMap_cycleClass]
  change _ = transgression V b n
    ((HomologicalComplex.homologyMap
      (singularChainMap (RelativeFiberMap.map f hf a b hab)) n).hom
        (cycleClass (singularComplex (Fiber U a)) n c))
  rw [homologyMap_cycleClass, transgression_cycleClass]
  apply congrArg (cycleClass (RelativeSingularHomology.complex V) (n + 1))
  apply Subtype.ext
  rw [mapCycles_val, ChainHomotopyDegreeShift.cycleMap_val,
    ChainHomotopyDegreeShift.cycleMap_val, mapCycles_val]
  exact relativePrism_natural f hf a b hab n c.val

end NoExoticSixSphere.RelativeFiberHomology
