import Wikipedia.NoExoticSixSphere.RelativeSingularHomologyMaps

/-!
# Relative homology under homeomorphisms of actual pairs

The forward maps below are induced by the supplied homeomorphism on the
original spaces and subspaces. These identifications do not replace their
chain complexes or assign homology groups by their expected isomorphism type.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.RelativeSingularHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The actual singular-chain isomorphism induced by a homeomorphism. -/
def chainHomeomorphIso (h : X ≃ₜ Y) : singularComplex X ≅ singularComplex Y where
  hom := singularChainMap (h : C(X, Y))
  inv := singularChainMap (h.symm : C(Y, X))
  hom_inv_id := by
    rw [← chainMap_comp]
    have he : (h.symm : C(Y, X)).comp (h : C(X, Y)) = ContinuousMap.id X := by
      ext x
      exact h.symm_apply_apply x
    rw [he, chainMap_id]
  inv_hom_id := by
    rw [← chainMap_comp]
    have he : (h : C(X, Y)).comp (h.symm : C(Y, X)) = ContinuousMap.id Y := by
      ext y
      exact h.apply_symm_apply y
    rw [he, chainMap_id]

/-- The relative-chain isomorphism for a homeomorphism preserving the specified pair. -/
def homeomorphChainIso {U : Set X} {V : Set Y} (h : X ≃ₜ Y)
    (hf : Set.MapsTo h U V) (hg : Set.MapsTo h.symm V U) : complex U ≅ complex V where
  hom := mapChain (h : C(X, Y)) hf
  inv := mapChain (h.symm : C(Y, X)) hg
  hom_inv_id := by
    rw [← mapChain_comp]
    have he : (h.symm : C(Y, X)).comp (h : C(X, Y)) = ContinuousMap.id X := by
      ext x
      exact h.symm_apply_apply x
    simp only [he, mapChain_id]
  inv_hom_id := by
    rw [← mapChain_comp]
    have he : (h : C(X, Y)).comp (h.symm : C(Y, X)) = ContinuousMap.id Y := by
      ext y
      exact h.apply_symm_apply y
    simp only [he, mapChain_id]

/-- Relative homology is transported along the actual homeomorphism of pairs. -/
def homeomorphEquiv {U : Set X} {V : Set Y} (h : X ≃ₜ Y)
    (hf : Set.MapsTo h U V) (hg : Set.MapsTo h.symm V U) (n : ℕ) :
    Homology U n ≃ₗ[ℤ] Homology V n :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).mapIso
    (homeomorphChainIso h hf hg)).toLinearEquiv

theorem homeomorphEquiv_toLinearMap {U : Set X} {V : Set Y} (h : X ≃ₜ Y)
    (hf : Set.MapsTo h U V) (hg : Set.MapsTo h.symm V U) (n : ℕ) :
    (homeomorphEquiv h hf hg n).toLinearMap = map (h : C(X, Y)) hf n := rfl

end NoExoticSixSphere.RelativeSingularHomology
