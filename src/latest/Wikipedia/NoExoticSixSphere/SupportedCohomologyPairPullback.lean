import Wikipedia.NoExoticSixSphere.SupportedModTwoPullback
import Wikipedia.NoExoticSixSphere.OpenEmbeddingSupportCohomology

/-!
# Original pair pullbacks with separately named supports

The support in the source may be named independently of the inverse
image. Its complement still maps to the target complement, giving the
original relative cochain pullback. This is exactly inverse-image
pullback followed by original extension. Composition and inverse
open-embedding excision retain the original maps and classes.
-/

noncomputable section

open CategoryTheory Set

namespace NoExoticSixSphere.SupportedModTwoCohomology

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- The original map of complement pairs for a specified containing source support. -/
def pullbackToCochain (f : C(X, Y)) (K : Set Y) (L : Set X) (h : f ⁻¹' K ⊆ L) :
    complex K ⟶ complex L :=
  RelativeModTwoCochains.pullbackMap f
    (show MapsTo f Lᶜ Kᶜ from fun _ hx hy => hx (h hy))

/-- The actual induced relative cohomology map with the named source support. -/
abbrev pullbackTo (f : C(X, Y)) (K : Set Y) (L : Set X) (h : f ⁻¹' K ⊆ L) (p : ℕ) :
    Cohomology K p →ₗ[ℤ] Cohomology L p :=
  (HomologicalComplex.homologyMap (pullbackToCochain f K L h) p).hom

/-- The original pair composition law, already on the actual relative cochains. -/
theorem pullbackToCochain_comp (f : C(X, Y)) (g : C(Y, Z))
    (K : Set Z) (L : Set Y) (N : Set X) (hg : g ⁻¹' K ⊆ L) (hf : f ⁻¹' L ⊆ N) :
    pullbackToCochain (g.comp f) K N (fun _ hx => hf (hg hx)) =
      pullbackToCochain g K L hg ≫ pullbackToCochain f L N hf := by
  change ModTwoDualComplex.map _ = ModTwoDualComplex.map _ ≫ ModTwoDualComplex.map _
  rw [← ModTwoDualComplex.map_comp, ← RelativeCoefficients.mapChain_comp]

/-- Named-support composition is induced by the same original maps of pairs. -/
theorem pullbackTo_comp (f : C(X, Y)) (g : C(Y, Z))
    (K : Set Z) (L : Set Y) (N : Set X) (hg : g ⁻¹' K ⊆ L) (hf : f ⁻¹' L ⊆ N)
    (p : ℕ) (a : Cohomology K p) :
    pullbackTo (g.comp f) K N (fun _ hx => hf (hg hx)) p a =
      pullbackTo f L N hf p (pullbackTo g K L hg p a) := by
  change (HomologicalComplex.homologyMap
    (pullbackToCochain (g.comp f) K N (fun _ hx => hf (hg hx))) p).hom a = _
  rw [pullbackToCochain_comp, HomologicalComplex.homologyMap_comp]
  rfl

/-- The independently named support changes only by the original extension map. -/
theorem pullbackToCochain_eq_extend (f : C(X, Y)) (K : Set Y) (L : Set X)
    (h : f ⁻¹' K ⊆ L) :
    pullbackToCochain f K L h = pullbackCochain f K ≫ extendCochain h := by
  change ModTwoDualComplex.map _ = ModTwoDualComplex.map _ ≫ ModTwoDualComplex.map _
  rw [← ModTwoDualComplex.map_comp]
  apply congrArg ModTwoDualComplex.map
  change RelativeCoefficients.mapChain _ f _ =
    RelativeCoefficients.mapChain _ (ContinuousMap.id X) _ ≫ RelativeCoefficients.mapChain _ f _
  rw [← RelativeCoefficients.mapChain_comp]
  rfl

/-- Named-support pullback equals actual inverse-image pullback followed by extension. -/
theorem pullbackTo_eq_extend (f : C(X, Y)) (K : Set Y) (L : Set X)
    (h : f ⁻¹' K ⊆ L) (p : ℕ) (a : Cohomology K p) :
    pullbackTo f K L h p a = extend h p (pullback f K p a) := by
  change (HomologicalComplex.homologyMap (pullbackToCochain f K L h) p).hom a = _
  rw [pullbackToCochain_eq_extend, HomologicalComplex.homologyMap_comp]
  rfl

end NoExoticSixSphere.SupportedModTwoCohomology

namespace NoExoticSixSphere.OpenEmbeddingSupportCohomology

open SupportedModTwoCohomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
  (f : C(X, Y)) (hf : Topology.IsOpenEmbedding f)

include hf in
/-- The named image support has exactly the original source support as its inverse image. -/
theorem preimage_support (K : Set X) (L : Set Y) (hL : f '' K = L) : f ⁻¹' L = K := by
  rw [← hL, Set.preimage_image_eq K hf.injective]

variable [T2Space Y]

/-- Pullback along the original tube recovers the exact class used in its extension. -/
theorem pullbackTo_extension (K : Set X) (hK : IsCompact K)
    (L : Set Y) (hL : f '' K = L) (p : ℕ) (a : Cohomology K p) :
    pullbackTo f L K (preimage_support f hf K L hL).subset p
        (extension f hf K hK L hL p a) = a :=
  restriction_extension f hf K hK L hL p a

end NoExoticSixSphere.OpenEmbeddingSupportCohomology
