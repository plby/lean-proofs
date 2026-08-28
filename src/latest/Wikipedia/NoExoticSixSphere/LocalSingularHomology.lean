import Wikipedia.NoExoticSixSphere.RelativeSingularExcision

/-!
# Actual local singular homology

Local homology at a point is the homology of the original relative singular
complex modulo the punctured space. Inclusion of any open neighborhood of
the point induces an isomorphism, by the proved open-cover excision theorem.
Homeomorphisms transport these groups through their actual maps of pairs.
No local fundamental class or manifold duality theorem is assumed here.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem FirstHurewicz SingularMayerVietoris

namespace NoExoticSixSphere.RelativeSingularHomology

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- Local homology of the actual space at the specified point. -/
abbrev LocalHomology (x : X) (n : ℕ) := Homology ({x}ᶜ : Set X) n

omit [TopologicalSpace X] in
theorem overlap_puncture_eq (U : Set X) (x : U) :
    overlapIn U ({(x : X)}ᶜ : Set X) = ({x}ᶜ : Set U) := by
  ext y
  change ((y : X) ≠ (x : X)) ↔ y ≠ x
  constructor
  · intro h he
    exact h (congrArg Subtype.val he)
  · intro h he
    exact h (Subtype.ext he)

theorem inclusion_mapsTo_puncture (U : Set X) (x : U) :
    Set.MapsTo (subtypeInclusion U) ({x}ᶜ : Set U) ({(x : X)}ᶜ : Set X) := by
  intro y hy
  change y ≠ x at hy
  change (y : X) ≠ (x : X)
  exact fun h => hy (Subtype.ext h)

/-- The actual relative-chain map of inclusion of a pointed subspace. -/
def neighborhoodChainMap (U : Set X) (x : U) :
    complex ({x}ᶜ : Set U) ⟶ complex ({(x : X)}ᶜ : Set X) :=
  mapChain (subtypeInclusion U) (inclusion_mapsTo_puncture U x)

omit [TopologicalSpace X] in
theorem neighborhood_puncture_cover (U : Set X) (x : U) :
    U ∪ ({(x : X)}ᶜ : Set X) = Set.univ := by
  apply Set.eq_univ_of_forall
  intro y
  by_cases hy : y = (x : X)
  · exact Or.inl (hy ▸ x.2)
  · exact Or.inr hy

/-- The inclusion-induced chain map is a quasi-isomorphism for every open neighborhood. -/
theorem neighborhoodChainMap_quasiIso [T1Space X] (U : Set X) (hU : IsOpen U) (x : U) :
    QuasiIso (neighborhoodChainMap U x) := by
  have hgeneral (A : Set U) (hA : overlapIn U ({(x : X)}ᶜ : Set X) = A)
      (hf : Set.MapsTo (subtypeInclusion U) A ({(x : X)}ᶜ : Set X)) :
      QuasiIso (mapChain (subtypeInclusion U) hf) := by
    subst A
    exact excisionChainMap_quasiIso U ({(x : X)}ᶜ : Set X) hU
      isOpen_compl_singleton (neighborhood_puncture_cover U x)
  exact hgeneral ({x}ᶜ : Set U) (overlap_puncture_eq U x) (inclusion_mapsTo_puncture U x)

/-- Inclusion into the original space on actual local homology. -/
abbrev neighborhoodMap (U : Set X) (x : U) (n : ℕ) :
    LocalHomology x n →ₗ[ℤ] LocalHomology (x : X) n :=
  homologyLinearMap (neighborhoodChainMap U x) n

/-- Local homology can be computed in any actual open neighborhood. -/
def neighborhoodEquiv [T1Space X] (U : Set X) (hU : IsOpen U) (x : U) (n : ℕ) :
    LocalHomology x n ≃ₗ[ℤ] LocalHomology (x : X) n := by
  let := neighborhoodChainMap_quasiIso U hU x
  exact (isoOfQuasiIsoAt (neighborhoodChainMap U x) n).toLinearEquiv

theorem neighborhoodEquiv_toLinearMap [T1Space X] (U : Set X) (hU : IsOpen U)
    (x : U) (n : ℕ) :
    (neighborhoodEquiv U hU x n).toLinearMap = neighborhoodMap U x n := rfl

theorem homeomorph_mapsTo_puncture (h : X ≃ₜ Y) (x : X) :
    Set.MapsTo h ({x}ᶜ : Set X) ({h x}ᶜ : Set Y) := by
  intro y hy
  change y ≠ x at hy
  change h y ≠ h x
  exact fun he => hy (h.injective he)

theorem homeomorph_symm_mapsTo_puncture (h : X ≃ₜ Y) (x : X) :
    Set.MapsTo h.symm ({h x}ᶜ : Set Y) ({x}ᶜ : Set X) := by
  intro y hy
  change y ≠ h x at hy
  change h.symm y ≠ x
  intro he
  apply hy
  exact (h.apply_symm_apply y).symm.trans (congrArg h he)

/-- The homeomorphism induces the local homology equivalence at the corresponding points. -/
def localHomeomorphEquiv (h : X ≃ₜ Y) (x : X) (n : ℕ) :
    LocalHomology x n ≃ₗ[ℤ] LocalHomology (h x) n :=
  homeomorphEquiv h (homeomorph_mapsTo_puncture h x)
    (homeomorph_symm_mapsTo_puncture h x) n

theorem localHomeomorphEquiv_toLinearMap (h : X ≃ₜ Y) (x : X) (n : ℕ) :
    (localHomeomorphEquiv h x n).toLinearMap =
      map (h : C(X, Y)) (homeomorph_mapsTo_puncture h x) n := rfl

end NoExoticSixSphere.RelativeSingularHomology
