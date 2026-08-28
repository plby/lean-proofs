import Wikipedia.NoExoticSixSphere.RelativeModTwoExcision
import Wikipedia.NoExoticSixSphere.RelativeHomologyMapComparison

/-!
# Relative mod-two cohomology comparison from actual homology equivalences

The original integral short exact pair sequences give a relative
quasi-isomorphism when the ambient and subspace maps are homology
equivalences. The relative integral chain groups are free, so the
proved projective-complex duality theorem makes the actual mod-two
pullback a quasi-isomorphism as well.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.RelativeModTwoCochains

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  {U : Set X} {V : Set Y}

theorem pullbackMap_quasiIso_of_absolute
    (f : C(X, Y)) (hf : Set.MapsTo f U V)
    (hX : ∀ n, Function.Bijective (singularHomologyMap f n))
    (hU : ∀ n, Function.Bijective
      (singularHomologyMap (RelativeSingularHomology.restrictedMap f hf) n)) :
    QuasiIso (pullbackMap f hf) := by
  let (n : ℕ) : Projective ((RelativeSingularHomology.complex U).X n) := by
    let := RelativeSingularHomology.chains_free U n
    infer_instance
  let (n : ℕ) : Projective ((RelativeSingularHomology.complex V).X n) := by
    let := RelativeSingularHomology.chains_free V n
    infer_instance
  let := RelativeSingularHomology.mapChain_quasiIso_of_absolute f hf hX hU
  exact ModTwoDualComplex.map_quasiIso_of_projective (RelativeSingularHomology.mapChain f hf)

def equivalenceOfAbsolute
    (f : C(X, Y)) (hf : Set.MapsTo f U V)
    (hX : ∀ n, Function.Bijective (singularHomologyMap f n))
    (hU : ∀ n, Function.Bijective
      (singularHomologyMap (RelativeSingularHomology.restrictedMap f hf) n)) (p : ℕ) :
    Cohomology V p ≃ₗ[ℤ] Cohomology U p := by
  let := pullbackMap_quasiIso_of_absolute f hf hX hU
  exact (isoOfQuasiIsoAt (pullbackMap f hf) p).toLinearEquiv

theorem equivalenceOfAbsolute_toLinearMap
    (f : C(X, Y)) (hf : Set.MapsTo f U V)
    (hX : ∀ n, Function.Bijective (singularHomologyMap f n))
    (hU : ∀ n, Function.Bijective
      (singularHomologyMap (RelativeSingularHomology.restrictedMap f hf) n)) (p : ℕ) :
    (equivalenceOfAbsolute f hf hX hU p).toLinearMap = cohomologyPullback f hf p := rfl

end NoExoticSixSphere.RelativeModTwoCochains
