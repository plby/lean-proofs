import Wikipedia.NoExoticSixSphere.ModTwoDualQuasiIso
import Wikipedia.NoExoticSixSphere.RelativeIntegralChainsFree
import Wikipedia.NoExoticSixSphere.RelativeModTwoCochainPullback
import Wikipedia.NoExoticSixSphere.RelativeSingularExcision

/-!
# Excision for the original relative mod-two cohomology

The actual integral excision map is a quasi-isomorphism, and both of its
relative chain complexes have proved free terms. Its original dual map
is therefore a quasi-isomorphism. The resulting cohomology equivalence
has the original inclusion-induced pair pullback as its forward map.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.RelativeModTwoCochains

variable {X : Type} [TopologicalSpace X] (U V : Set X)

/-- Original cochain restriction to the actual excised pair. -/
def excisionPullbackMap : complex V ⟶ complex (RelativeSingularHomology.overlapIn U V) :=
  pullbackMap (subtypeInclusion U)
    (show Set.MapsTo (subtypeInclusion U) (RelativeSingularHomology.overlapIn U V) V
      from fun _ hx => hx)

/-- Excision holds for the actual mod-two cochain pullback, in all degrees. -/
theorem excisionPullbackMap_quasiIso (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) : QuasiIso (excisionPullbackMap U V) := by
  let (n : ℕ) : Projective ((RelativeSingularHomology.complex V).X n) := by
    let := RelativeSingularHomology.chains_free V n
    infer_instance
  let (n : ℕ) :
      Projective ((RelativeSingularHomology.complex
        (RelativeSingularHomology.overlapIn U V)).X n) := by
    let := RelativeSingularHomology.chains_free (RelativeSingularHomology.overlapIn U V) n
    infer_instance
  let := RelativeSingularHomology.excisionChainMap_quasiIso U V hU hV hcover
  exact ModTwoDualComplex.map_quasiIso_of_projective
    (RelativeSingularHomology.excisionChainMap U V)

/-- The original inclusion-induced relative cohomology equivalence. -/
def excisionEquiv (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    Cohomology V n ≃ₗ[ℤ] Cohomology (RelativeSingularHomology.overlapIn U V) n := by
  let := excisionPullbackMap_quasiIso U V hU hV hcover
  exact (isoOfQuasiIsoAt (excisionPullbackMap U V) n).toLinearEquiv

theorem excisionEquiv_toLinearMap (hU : IsOpen U) (hV : IsOpen V)
    (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (excisionEquiv U V hU hV hcover n).toLinearMap =
      cohomologyPullback (subtypeInclusion U)
        (show Set.MapsTo (subtypeInclusion U) (RelativeSingularHomology.overlapIn U V) V
          from fun _ hx => hx) n := rfl

end NoExoticSixSphere.RelativeModTwoCochains
