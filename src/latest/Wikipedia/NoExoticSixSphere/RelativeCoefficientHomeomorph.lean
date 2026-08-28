import Wikipedia.NoExoticSixSphere.RelativeCoefficientPairMaps

/-!
# Homeomorphisms of pairs with native coefficients

These isomorphisms are induced by the actual maps of pairs on the native
relative coefficient complexes. In particular their forward homology maps
are not arbitrary identifications with an abstractly isomorphic module.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.RelativeCoefficients

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- The original relative coefficient chain isomorphism of a homeomorphism of pairs. -/
def homeomorphChainIso (A : ModuleCat.{0} ℤ) {U : Set X} {V : Set Y} (h : X ≃ₜ Y)
    (hf : Set.MapsTo h U V) (hg : Set.MapsTo h.symm V U) : complex A U ≅ complex A V where
  hom := mapChain A (h : C(X, Y)) hf
  inv := mapChain A (h.symm : C(Y, X)) hg
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

/-- Native relative coefficient homology transported by the actual pair homeomorphism. -/
def homeomorphEquiv (A : ModuleCat.{0} ℤ) {U : Set X} {V : Set Y} (h : X ≃ₜ Y)
    (hf : Set.MapsTo h U V) (hg : Set.MapsTo h.symm V U) (n : ℕ) :
    (complex A U).homology n ≃ₗ[ℤ] (complex A V).homology n :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n).mapIso
    (homeomorphChainIso A h hf hg)).toLinearEquiv

theorem homeomorphEquiv_toLinearMap (A : ModuleCat.{0} ℤ) {U : Set X} {V : Set Y}
    (h : X ≃ₜ Y) (hf : Set.MapsTo h U V) (hg : Set.MapsTo h.symm V U) (n : ℕ) :
    (homeomorphEquiv A h hf hg n).toLinearMap =
      homologyLinearMap (mapChain A (h : C(X, Y)) hf) n := rfl

theorem point_complement_mapsTo (h : X ≃ₜ Y) (x : X) :
    Set.MapsTo h ({x}ᶜ : Set X) ({h x}ᶜ : Set Y) := by
  intro z hz
  change h z ≠ h x
  exact fun he => hz (h.injective he)

theorem point_complement_symm_mapsTo (h : X ≃ₜ Y) (x : X) :
    Set.MapsTo h.symm ({h x}ᶜ : Set Y) ({x}ᶜ : Set X) := by
  intro z hz
  change h.symm z ≠ x
  intro he
  apply hz
  exact (h.apply_symm_apply z).symm.trans (congrArg h he)

/-- Actual local coefficient homology isomorphism induced by a homeomorphism. -/
def localHomeomorphEquiv (A : ModuleCat.{0} ℤ) (h : X ≃ₜ Y) (x : X) (n : ℕ) :
    (complex A ({x}ᶜ : Set X)).homology n ≃ₗ[ℤ]
      (complex A ({h x}ᶜ : Set Y)).homology n :=
  homeomorphEquiv A h (point_complement_mapsTo h x) (point_complement_symm_mapsTo h x) n

end NoExoticSixSphere.RelativeCoefficients
