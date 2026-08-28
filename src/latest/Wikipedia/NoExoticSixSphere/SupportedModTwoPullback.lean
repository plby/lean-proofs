import Wikipedia.NoExoticSixSphere.SupportedModTwoCohomology
import Wikipedia.NoExoticSixSphere.RelativeModTwoCochainPullback

/-!
# Actual inverse-image pullback of cohomology supports

The original continuous map of complement pairs induces literal
precomposition on the original relative cochains. Support enlargement,
composition, identity, and forgetting the support all commute with
these actual maps. Compact-support pullback will additionally require
compact inverse images, rather than imposing that on these pair maps.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Original cochain precomposition by the actual inverse-image map of complement pairs. -/
def pullbackCochain (f : C(X, Y)) (K : Set Y) : complex K ⟶ complex (f ⁻¹' K) :=
  RelativeModTwoCochains.pullbackMap f
    (show Set.MapsTo f (f ⁻¹' K)ᶜ Kᶜ from fun _ hx => hx)

/-- Pullback on the genuine supported cohomology groups. -/
abbrev pullback (f : C(X, Y)) (K : Set Y) (p : ℕ) :
    Cohomology K p →ₗ[ℤ] Cohomology (f ⁻¹' K) p :=
  (HomologicalComplex.homologyMap (pullbackCochain f K) p).hom

/-- Original inverse-image restriction commutes with enlargement of support on cochains. -/
theorem pullbackCochain_extend (f : C(X, Y)) {K L : Set Y} (h : K ⊆ L) :
    extendCochain h ≫ pullbackCochain f L =
      pullbackCochain f K ≫ extendCochain (Set.preimage_mono h) := by
  change ModTwoDualComplex.map _ ≫ ModTwoDualComplex.map _ =
    ModTwoDualComplex.map _ ≫ ModTwoDualComplex.map _
  rw [← ModTwoDualComplex.map_comp, ← ModTwoDualComplex.map_comp]
  apply congrArg ModTwoDualComplex.map
  change RelativeCoefficients.mapChain _ f _ ≫
      RelativeCoefficients.mapChain _ (ContinuousMap.id Y) _ =
    RelativeCoefficients.mapChain _ (ContinuousMap.id X) _ ≫
      RelativeCoefficients.mapChain _ f _
  rw [← RelativeCoefficients.mapChain_comp, ← RelativeCoefficients.mapChain_comp]
  rfl

/-- Support transition compatibility for the actual induced cohomology maps. -/
theorem pullback_extend (f : C(X, Y)) {K L : Set Y} (h : K ⊆ L) (p : ℕ)
    (a : Cohomology K p) :
    pullback f L p (extend h p a) = extend (Set.preimage_mono h) p (pullback f K p a) := by
  have he := congrArg (fun m => HomologicalComplex.homologyMap m p) (pullbackCochain_extend f h)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at he
  exact congrArg (fun m => m.hom a) he

/-- Identity is the original identity on supported cochains. -/
theorem pullbackCochain_id (K : Set X) :
    pullbackCochain (ContinuousMap.id X) K = 𝟙 (complex K) := by
  exact (congrArg ModTwoDualComplex.map
    (RelativeCoefficients.mapChain_id (ModuleCat.of ℤ ℤ) Kᶜ)).trans
      (ModTwoDualComplex.map_id _)

/-- Composition is literal precomposition by the original composite map of pairs. -/
theorem pullbackCochain_comp (f : C(X, Y)) (g : C(Y, Z)) (K : Set Z) :
    pullbackCochain (g.comp f) K = pullbackCochain g K ≫ pullbackCochain f (g ⁻¹' K) := by
  change ModTwoDualComplex.map _ = ModTwoDualComplex.map _ ≫ ModTwoDualComplex.map _
  rw [← ModTwoDualComplex.map_comp, ← RelativeCoefficients.mapChain_comp]

theorem pullback_id (K : Set X) (p : ℕ) (a : Cohomology K p) :
    pullback (ContinuousMap.id X) K p a = a := by
  change (HomologicalComplex.homologyMap
    (show complex K ⟶ complex K from pullbackCochain (ContinuousMap.id X) K) p).hom a = a
  rw [pullbackCochain_id, HomologicalComplex.homologyMap_id]
  rfl

theorem pullback_comp (f : C(X, Y)) (g : C(Y, Z)) (K : Set Z) (p : ℕ)
    (a : Cohomology K p) :
    pullback (g.comp f) K p a = pullback f (g ⁻¹' K) p (pullback g K p a) := by
  change (HomologicalComplex.homologyMap (pullbackCochain (g.comp f) K) p).hom a = _
  rw [pullbackCochain_comp, HomologicalComplex.homologyMap_comp]
  rfl

/-- Forgetting support commutes with pullback already on the original cochain complexes. -/
theorem toAbsoluteMap_pullback (f : C(X, Y)) (K : Set Y) :
    pullbackCochain f K ≫ RelativeModTwoCochains.toAbsoluteMap (f ⁻¹' K)ᶜ =
      RelativeModTwoCochains.toAbsoluteMap Kᶜ ≫ ModTwoCapProduct.cochainPullback f := by
  apply HomologicalComplex.hom_ext
  intro p
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  exact RelativeModTwoCochains.toAbsolute_pullback f
    (show Set.MapsTo f (f ⁻¹' K)ᶜ Kᶜ from fun _ hx => hx) p a

/-- The actual absolute cohomology value is the original pullback of the supported class. -/
theorem toAbsolute_pullback (f : C(X, Y)) (K : Set Y) (p : ℕ) (a : Cohomology K p) :
    RelativeModTwoCochains.toAbsoluteCohomology (f ⁻¹' K)ᶜ p (pullback f K p a) =
      ModTwoCapProduct.cohomologyPullback f p
        (RelativeModTwoCochains.toAbsoluteCohomology Kᶜ p a) := by
  have he := congrArg (fun m => HomologicalComplex.homologyMap m p) (toAbsoluteMap_pullback f K)
  rw [HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp] at he
  exact congrArg (fun m => m.hom a) he

end NoExoticSixSphere.SupportedModTwoCohomology
