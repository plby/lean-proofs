import Wikipedia.NoExoticSixSphere.RelativeSingularHomology

/-!
# Maps of actual pairs and the relative homology sequence

A continuous map carrying the specified subspace into the specified subspace
induces a map of the actual relative singular complexes. Identity, composition,
and naturality of the connecting homomorphism are proved from the original
singular-chain maps and the universal property of their cokernels.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.RelativeSingularHomology

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem chainMap_id : singularChainMap (ContinuousMap.id X) = 𝟙 (singularComplex X) := by
  apply HomologicalComplex.hom_ext
  intro n
  exact ModuleCat.hom_ext (inducedChain_id n)

theorem chainMap_comp (f : C(X, Y)) (g : C(Y, Z)) :
    singularChainMap (g.comp f) = singularChainMap f ≫ singularChainMap g := by
  apply HomologicalComplex.hom_ext
  intro n
  exact ModuleCat.hom_ext (inducedChain_comp f g n)

/-- The actual restriction of a continuous map of pairs. -/
def restrictedMap {U : Set X} {V : Set Y} (f : C(X, Y)) (hf : Set.MapsTo f U V) :
    C(U, V) :=
  ⟨fun x => ⟨f x, hf x.2⟩, (f.continuous.comp continuous_subtype_val).subtype_mk _⟩

theorem inclusion_map {U : Set X} {V : Set Y} (f : C(X, Y))
    (hf : Set.MapsTo f U V) :
    inclusion U ≫ singularChainMap f = singularChainMap (restrictedMap f hf) ≫
      inclusion V := by
  change singularChainMap (subtypeInclusion U) ≫ singularChainMap f =
    singularChainMap (restrictedMap f hf) ≫ singularChainMap (subtypeInclusion V)
  rw [← chainMap_comp, ← chainMap_comp]
  rfl

/-- The chain map of the original continuous map of pairs. -/
def mapChain {U : Set X} {V : Set Y} (f : C(X, Y)) (hf : Set.MapsTo f U V) :
    complex U ⟶ complex V :=
  cokernel.map (inclusion U) (inclusion V) (singularChainMap (restrictedMap f hf))
    (singularChainMap f) (inclusion_map f hf)

@[reassoc]
theorem projection_mapChain {U : Set X} {V : Set Y} (f : C(X, Y))
    (hf : Set.MapsTo f U V) :
    projection U ≫ mapChain f hf = singularChainMap f ≫ projection V :=
  cokernel.π_desc _ _ _

theorem mapChain_id (U : Set X) :
    mapChain (ContinuousMap.id X) (show Set.MapsTo (ContinuousMap.id X) U U from
      fun _ hx => hx) = 𝟙 (complex U) := by
  apply (cancel_epi (cokernel.π (inclusion U))).mp
  change projection U ≫ _ = projection U ≫ _
  rw [projection_mapChain, chainMap_id, Category.id_comp, Category.comp_id]

theorem mapChain_comp {U : Set X} {V : Set Y} {W : Set Z}
    (f : C(X, Y)) (hf : Set.MapsTo f U V) (g : C(Y, Z)) (hg : Set.MapsTo g V W) :
    mapChain (g.comp f) (hg.comp hf) = mapChain f hf ≫ mapChain g hg := by
  apply (cancel_epi (cokernel.π (inclusion U))).mp
  change projection U ≫ _ = projection U ≫ _
  rw [projection_mapChain, chainMap_comp, Category.assoc,
    projection_mapChain_assoc, projection_mapChain]

/-- The homology map of the actual map of relative complexes. -/
abbrev map {U : Set X} {V : Set Y} (f : C(X, Y)) (hf : Set.MapsTo f U V) (n : ℕ) :
    Homology U n →ₗ[ℤ] Homology V n :=
  homologyLinearMap (mapChain f hf) n

theorem map_id (U : Set X) (n : ℕ) :
    map (ContinuousMap.id X) (show Set.MapsTo (ContinuousMap.id X) U U from
      fun _ hx => hx) n = LinearMap.id := by
  change homologyLinearMap _ n = _
  rw [mapChain_id]
  exact congrArg ModuleCat.Hom.hom (HomologicalComplex.homologyMap_id (complex U) n)

theorem map_comp {U : Set X} {V : Set Y} {W : Set Z}
    (f : C(X, Y)) (hf : Set.MapsTo f U V) (g : C(Y, Z)) (hg : Set.MapsTo g V W)
    (n : ℕ) :
    map (g.comp f) (hg.comp hf) n = (map g hg n).comp (map f hf n) := by
  change homologyLinearMap _ n = _
  rw [mapChain_comp, homologyLinearMap_comp]

/-- A continuous map of pairs gives a morphism of the proved chain sequences. -/
def sequenceMap {U : Set X} {V : Set Y} (f : C(X, Y)) (hf : Set.MapsTo f U V) :
    sequence U ⟶ sequence V where
  τ₁ := singularChainMap (restrictedMap f hf)
  τ₂ := singularChainMap f
  τ₃ := mapChain f hf
  comm₁₂ := (inclusion_map f hf).symm
  comm₂₃ := (projection_mapChain f hf).symm

theorem toRelative_naturality {U : Set X} {V : Set Y} (f : C(X, Y))
    (hf : Set.MapsTo f U V) (n : ℕ) :
    (map f hf n).comp (toRelative U n) =
      (toRelative V n).comp (singularHomologyMap f n) := by
  rw [← homologyLinearMap_comp, projection_mapChain, homologyLinearMap_comp]

/-- Naturality of the actual connecting maps, with the actual restriction on the subspace. -/
theorem connecting_naturality {U : Set X} {V : Set Y} (f : C(X, Y))
    (hf : Set.MapsTo f U V) (n : ℕ) :
    (singularHomologyMap (restrictedMap f hf) n).comp (connecting U n) =
      (connecting V n).comp (map f hf (n + 1)) :=
  connectingMap_naturality (sequence_shortExact U) (sequenceMap f hf)
    (sequence_shortExact V) n

end NoExoticSixSphere.RelativeSingularHomology
