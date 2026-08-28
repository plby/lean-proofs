import Wikipedia.NoExoticSixSphere.RelativeSingularHomologyMaps
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-!
# Relative homology comparison for the original map of pairs

If the original ambient map and its actual subspace restriction induce
homology isomorphisms, the short exact singular-chain sequences give a
quasi-isomorphism of the actual relative complexes. This includes degree
zero and retains the original map of pairs as the resulting homology map.
-/

noncomputable section

open CategoryTheory HomologicalComplex
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.RelativeSingularHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

theorem map_congr {U : Set X} {V : Set Y} {f g : C(X, Y)}
    (hf : Set.MapsTo f U V) (hg : Set.MapsTo g U V) (h : f = g) (d : ℕ) :
    map f hf d = map g hg d := by
  subst g
  rfl

theorem singularChainMap_quasiIso_of_bijective (f : C(X, Y))
    (h : ∀ d, Function.Bijective (singularHomologyMap f d)) : QuasiIso (singularChainMap f) := by
  rw [quasiIso_iff]
  intro d
  rw [quasiIsoAt_iff_isIso_homologyMap]
  exact (ConcreteCategory.isIso_iff_bijective _).mpr (h d)

theorem mapChain_quasiIso_of_absolute {U : Set X} {V : Set Y}
    (f : C(X, Y)) (hf : Set.MapsTo f U V)
    (hX : ∀ d, Function.Bijective (singularHomologyMap f d))
    (hU : ∀ d, Function.Bijective (singularHomologyMap (restrictedMap f hf) d)) :
    QuasiIso (mapChain f hf) :=
  HomologySequence.quasiIso_τ₃ (sequenceMap f hf) (sequence_shortExact U) (sequence_shortExact V)
    (singularChainMap_quasiIso_of_bijective (restrictedMap f hf) hU)
    (singularChainMap_quasiIso_of_bijective f hX)

theorem map_bijective_of_absolute {U : Set X} {V : Set Y}
    (f : C(X, Y)) (hf : Set.MapsTo f U V)
    (hX : ∀ d, Function.Bijective (singularHomologyMap f d))
    (hU : ∀ d, Function.Bijective (singularHomologyMap (restrictedMap f hf) d)) (d : ℕ) :
    Function.Bijective (map f hf d) := by
  let := mapChain_quasiIso_of_absolute f hf hX hU
  exact (isoOfQuasiIsoAt (mapChain f hf) d).toLinearEquiv.bijective

end NoExoticSixSphere.RelativeSingularHomology
