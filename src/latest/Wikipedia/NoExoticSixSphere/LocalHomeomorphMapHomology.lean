import Wikipedia.NoExoticSixSphere.LocalSingularHomology
import Wikipedia.NoExoticSixSphere.RelativeHomologyMapComparison
import Wikipedia.NoExoticSixSphere.RelativeContractibleSubspace
import Mathlib.Topology.OpenPartialHomeomorph.Basic

/-!
# The actual homology map from a singleton local-homeomorphism fiber

Excision compares the original map of punctured pairs with its actual
source-target homeomorphism on an open neighborhood. If the two punctured
ambient spaces are contractible, naturality of absolute-to-relative
homology makes the original ambient homology map an isomorphism above
degree one. No degree or local orientation is assigned to the map.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.RelativeSingularHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  [T1Space X] [T1Space Y]

theorem localModel_map_bijective (f : C(X, Y)) (e : OpenPartialHomeomorph X Y)
    (x : X) (hx : x ∈ e.source) (he : Set.EqOn e f e.source)
    (hf : Set.MapsTo f ({x}ᶜ : Set X) ({e x}ᶜ : Set Y)) (n : ℕ) :
    Function.Bijective (map f hf n) := by
  let sx : e.source := ⟨x, hx⟩
  let H : e.source ≃ₜ e.target := e.toHomeomorphSourceTarget
  have hcomp : f.comp (subtypeInclusion e.source) =
      (subtypeInclusion e.target).comp (H : C(e.source, e.target)) := by
    ext z
    exact (he z.property).symm
  have hcomm : (map f hf n).comp (neighborhoodMap e.source sx n) =
      (neighborhoodMap e.target (H sx) n).comp
        (map (H : C(e.source, e.target)) (homeomorph_mapsTo_puncture H sx) n) := by
    change (map f hf n).comp
      (map (subtypeInclusion e.source) (inclusion_mapsTo_puncture e.source sx) n) =
      (map (subtypeInclusion e.target) (inclusion_mapsTo_puncture e.target (H sx)) n).comp
        (map (H : C(e.source, e.target)) (homeomorph_mapsTo_puncture H sx) n)
    rw [← map_comp, ← map_comp]
    exact map_congr _ _ hcomp n
  have hs := (neighborhoodEquiv e.source e.open_source sx n).bijective
  have ht := (neighborhoodEquiv e.target e.open_target (H sx) n).bijective
  have hh := (localHomeomorphEquiv H sx n).bijective
  apply (Function.Bijective.of_comp_iff (map f hf n) hs).mp
  change Function.Bijective ((map f hf n).comp (neighborhoodMap e.source sx n))
  rw [hcomm]
  exact ht.comp hh

theorem localModel_singularHomologyMap_bijective (f : C(X, Y))
    (e : OpenPartialHomeomorph X Y) (x : X) (hx : x ∈ e.source)
    (he : Set.EqOn e f e.source)
    (hf : Set.MapsTo f ({x}ᶜ : Set X) ({e x}ᶜ : Set Y))
    [ContractibleSpace ({x}ᶜ : Set X)] [ContractibleSpace ({e x}ᶜ : Set Y)] (n : ℕ) :
    Function.Bijective (singularHomologyMap f (n + 2)) := by
  have hs := contractibleSubspace_toRelative_bijective ({x}ᶜ : Set X) n
  have ht := contractibleSubspace_toRelative_bijective ({e x}ᶜ : Set Y) n
  have hm := localModel_map_bijective f e x hx he hf (n + 2)
  apply (Function.Bijective.of_comp_iff' ht (singularHomologyMap f (n + 2))).mp
  change Function.Bijective
    ((toRelative ({e x}ᶜ : Set Y) (n + 2)).comp (singularHomologyMap f (n + 2)))
  rw [← toRelative_naturality f hf]
  exact hm.comp hs

end NoExoticSixSphere.RelativeSingularHomology
