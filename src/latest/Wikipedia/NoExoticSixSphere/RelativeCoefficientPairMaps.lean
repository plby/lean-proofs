import Wikipedia.NoExoticSixSphere.RelativeCoefficientSequence

/-!
# Maps of pairs with native coefficients

Continuous maps of actual pairs act on the original relative coefficient
complexes. These maps commute with coefficient change, so their maps on the
integral and finite-cyclic coefficient sequences form actual commutative
diagrams of short exact complexes.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris SphereHomologyCoefficients

namespace NoExoticSixSphere.RelativeCoefficients

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

theorem spaceMap_id (A : ModuleCat.{0} ℤ) :
    spaceMap A (ContinuousMap.id X) = 𝟙 (coefficientComplex A X) :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj A).map_id (TopCat.of X)

theorem spaceMap_comp (A : ModuleCat.{0} ℤ) (f : C(X, Y)) (g : C(Y, Z)) :
    spaceMap A (g.comp f) = spaceMap A f ≫ spaceMap A g :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).obj A).map_comp
    (TopCat.ofHom f) (TopCat.ofHom g)

theorem inclusion_pairMap (A : ModuleCat.{0} ℤ) {U : Set X} {V : Set Y}
    (f : C(X, Y)) (hf : Set.MapsTo f U V) :
    inclusion A U ≫ spaceMap A f =
      spaceMap A (RelativeSingularHomology.restrictedMap f hf) ≫ inclusion A V := by
  change spaceMap A (subtypeInclusion U) ≫ spaceMap A f =
    spaceMap A (RelativeSingularHomology.restrictedMap f hf) ≫ spaceMap A (subtypeInclusion V)
  rw [← spaceMap_comp, ← spaceMap_comp]
  rfl

/-- The actual chain map induced by the supplied continuous map of pairs. -/
def mapChain (A : ModuleCat.{0} ℤ) {U : Set X} {V : Set Y}
    (f : C(X, Y)) (hf : Set.MapsTo f U V) : complex A U ⟶ complex A V :=
  cokernel.map (inclusion A U) (inclusion A V)
    (spaceMap A (RelativeSingularHomology.restrictedMap f hf)) (spaceMap A f)
    (inclusion_pairMap A f hf)

@[reassoc]
theorem projection_mapChain (A : ModuleCat.{0} ℤ) {U : Set X} {V : Set Y}
    (f : C(X, Y)) (hf : Set.MapsTo f U V) :
    projection A U ≫ mapChain A f hf = spaceMap A f ≫ projection A V :=
  cokernel.π_desc _ _ _

theorem mapChain_id (A : ModuleCat.{0} ℤ) (U : Set X) :
    mapChain A (ContinuousMap.id X)
      (show Set.MapsTo (ContinuousMap.id X) U U from fun _ hx => hx) = 𝟙 (complex A U) := by
  apply (cancel_epi (cokernel.π (inclusion A U))).mp
  change projection A U ≫ _ = projection A U ≫ _
  rw [projection_mapChain, spaceMap_id, Category.id_comp, Category.comp_id]

theorem mapChain_comp (A : ModuleCat.{0} ℤ) {U : Set X} {V : Set Y} {W : Set Z}
    (f : C(X, Y)) (hf : Set.MapsTo f U V) (g : C(Y, Z)) (hg : Set.MapsTo g V W) :
    mapChain A (g.comp f) (hg.comp hf) = mapChain A f hf ≫ mapChain A g hg := by
  apply (cancel_epi (cokernel.π (inclusion A U))).mp
  change projection A U ≫ _ = projection A U ≫ _
  rw [projection_mapChain, spaceMap_comp, Category.assoc,
    ← Category.assoc (projection A U), projection_mapChain, Category.assoc, projection_mapChain]

/-- Integral coefficient specialization is exactly the earlier original pair map. -/
theorem mapChain_int {U : Set X} {V : Set Y} (f : C(X, Y)) (hf : Set.MapsTo f U V) :
    mapChain (ModuleCat.of ℤ ℤ) f hf = RelativeSingularHomology.mapChain f hf := rfl

theorem spaceMap_change {A B : ModuleCat.{0} ℤ} (r : A ⟶ B) (f : C(X, Y)) :
    spaceMap A f ≫ coefficientComplexMap r Y = coefficientComplexMap r X ≫ spaceMap B f :=
  ((AlgebraicTopology.singularChainComplexFunctor (ModuleCat ℤ)).map r).naturality
    (TopCat.ofHom f)

/-- Coefficient change commutes with the actual relative pair map. -/
theorem change_mapChain {A B : ModuleCat.{0} ℤ} (r : A ⟶ B) {U : Set X} {V : Set Y}
    (f : C(X, Y)) (hf : Set.MapsTo f U V) :
    change r U ≫ mapChain B f hf = mapChain A f hf ≫ change r V := by
  apply (cancel_epi (cokernel.π (inclusion A U))).mp
  change projection A U ≫ (_ ≫ _) = projection A U ≫ (_ ≫ _)
  rw [← Category.assoc, projection_change, Category.assoc, projection_mapChain,
    ← Category.assoc (projection A U), projection_mapChain, Category.assoc, projection_change,
    ← Category.assoc, ← spaceMap_change, Category.assoc]

/-- The map of the actual coefficient sequences, not just a homology-level square. -/
def coefficientSequenceMap (p : ℕ) {U : Set X} {V : Set Y} (f : C(X, Y))
    (hf : Set.MapsTo f U V) : coefficientSequence p U ⟶ coefficientSequence p V where
  τ₁ := mapChain (ModuleCat.of ℤ ℤ) f hf
  τ₂ := mapChain (ModuleCat.of ℤ ℤ) f hf
  τ₃ := mapChain (ModuleCat.of ℤ (ZMod p)) f hf
  comm₁₂ := (change_mapChain ((p : ℤ) • 𝟙 (ModuleCat.of ℤ ℤ)) f hf).symm
  comm₂₃ := (change_mapChain (reductionCoefficient p) f hf).symm

/-- The relative homology map with the original finite-cyclic coefficients. -/
abbrev modMap (p : ℕ) {U : Set X} {V : Set Y} (f : C(X, Y)) (hf : Set.MapsTo f U V)
    (n : ℕ) : ModHomology p U n →ₗ[ℤ] ModHomology p V n :=
  homologyLinearMap (mapChain (ModuleCat.of ℤ (ZMod p)) f hf) n

theorem reductionMap_naturality (p : ℕ) {U : Set X} {V : Set Y}
    (f : C(X, Y)) (hf : Set.MapsTo f U V) (n : ℕ) :
    (modMap p f hf n).comp (reductionMap p U n) =
      (reductionMap p V n).comp (RelativeSingularHomology.map f hf n) := by
  have h := congrArg (fun k => homologyLinearMap k n)
    (change_mapChain (reductionCoefficient p) f hf)
  simp only [homologyLinearMap_comp] at h
  exact h

theorem bockstein_naturality (p : ℕ) (hp : p ≠ 0) {U : Set X} {V : Set Y}
    (f : C(X, Y)) (hf : Set.MapsTo f U V) (n : ℕ) :
    (RelativeSingularHomology.map f hf n).comp (bockstein p hp U n) =
      (bockstein p hp V n).comp (modMap p f hf (n + 1)) := by
  exact connectingMap_naturality (coefficientSequence_shortExact p hp U)
    (coefficientSequenceMap p f hf) (coefficientSequence_shortExact p hp V) n

end NoExoticSixSphere.RelativeCoefficients
