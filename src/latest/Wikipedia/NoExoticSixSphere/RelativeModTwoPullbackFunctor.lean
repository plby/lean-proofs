import Wikipedia.NoExoticSixSphere.RelativeModTwoCochainPullback
import Wikipedia.NoExoticSixSphere.ModTwoDualFunctor

/-! # Functoriality of the original relative mod-two pair pullbacks -/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.RelativeModTwoCochains

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem pullbackMap_id (U : Set X) :
    pullbackMap (ContinuousMap.id X) (show Set.MapsTo (ContinuousMap.id X) U U from
      fun _ hx ↦ hx) = 𝟙 (complex U) := by
  unfold pullbackMap
  rw [RelativeCoefficients.mapChain_id, ModTwoDualComplex.map_id]

theorem pullbackMap_comp {U : Set X} {V : Set Y} {W : Set Z}
    (f : C(X, Y)) (hf : Set.MapsTo f U V) (g : C(Y, Z)) (hg : Set.MapsTo g V W) :
    pullbackMap (g.comp f) (hg.comp hf) = pullbackMap g hg ≫ pullbackMap f hf := by
  unfold pullbackMap
  rw [RelativeCoefficients.mapChain_comp, ModTwoDualComplex.map_comp]

theorem cohomologyPullback_id (U : Set X) (p : ℕ) :
    cohomologyPullback (ContinuousMap.id X) (show Set.MapsTo (ContinuousMap.id X) U U from
      fun _ hx ↦ hx) p = LinearMap.id := by
  unfold cohomologyPullback
  rw [pullbackMap_id, HomologicalComplex.homologyMap_id]
  rfl

theorem cohomologyPullback_comp {U : Set X} {V : Set Y} {W : Set Z}
    (f : C(X, Y)) (hf : Set.MapsTo f U V) (g : C(Y, Z)) (hg : Set.MapsTo g V W) (p : ℕ) :
    cohomologyPullback (g.comp f) (hg.comp hf) p =
      (cohomologyPullback f hf p).comp (cohomologyPullback g hg p) := by
  unfold cohomologyPullback
  rw [pullbackMap_comp, HomologicalComplex.homologyMap_comp]
  rfl

theorem cohomologyPullback_congr {U : Set X} {V : Set Y} {f g : C(X, Y)}
    (hf : Set.MapsTo f U V) (hg : Set.MapsTo g U V) (he : f = g) (p : ℕ) :
    cohomologyPullback f hf p = cohomologyPullback g hg p := by
  subst g
  rfl

end NoExoticSixSphere.RelativeModTwoCochains
