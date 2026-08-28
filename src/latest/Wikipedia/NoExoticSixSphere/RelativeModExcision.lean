import Wikipedia.NoExoticSixSphere.RelativeCoefficientPairMaps
import Wikipedia.NoExoticSixSphere.LocalSingularHomology

/-!
# Excision for native finite-cyclic relative homology

The natural coefficient short exact sequences transfer the proved integral
excision theorem to the actual relative complexes with coefficients `ℤ/p`.
The forward maps remain the original inclusion maps of pairs. The local
neighborhood case is included in every degree, in particular for `p = 2`.
-/

noncomputable section

open CategoryTheory
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.RelativeCoefficients

variable {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]

/-- A quasi-isomorphism on actual integral relative complexes stays one after native
finite-cyclic coefficient change, by the proved coefficient short exact sequences. -/
theorem mapChain_mod_quasiIso_of_integral (p : ℕ) (hp : p ≠ 0)
    {U : Set X} {V : Set Y} (f : C(X, Y)) (hf : Set.MapsTo f U V)
    (h : QuasiIso (RelativeSingularHomology.mapChain f hf)) :
    QuasiIso (mapChain (ModuleCat.of ℤ (ZMod p)) f hf) :=
  HomologicalComplex.HomologySequence.quasiIso_τ₃ (coefficientSequenceMap p f hf)
    (coefficientSequence_shortExact p hp U) (coefficientSequence_shortExact p hp V) h h

/-- The original open-cover inclusion of pairs, with the native finite-cyclic coefficients. -/
def modExcisionChainMap (p : ℕ) (U V : Set X) :
    complex (ModuleCat.of ℤ (ZMod p)) (RelativeSingularHomology.overlapIn U V) ⟶
      complex (ModuleCat.of ℤ (ZMod p)) V :=
  mapChain (ModuleCat.of ℤ (ZMod p)) (subtypeInclusion U)
    (show Set.MapsTo (subtypeInclusion U) (RelativeSingularHomology.overlapIn U V) V from
      fun _ hx => hx)

/-- Excision at the level of the actual coefficient chain map. -/
theorem modExcisionChainMap_quasiIso (p : ℕ) (hp : p ≠ 0) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) :
    QuasiIso (modExcisionChainMap p U V) :=
  mapChain_mod_quasiIso_of_integral p hp (subtypeInclusion U) _
    (RelativeSingularHomology.excisionChainMap_quasiIso U V hU hV hcover)

/-- The actual induced excision map. -/
abbrev modExcisionMap (p : ℕ) (U V : Set X) (n : ℕ) :
    ModHomology p (RelativeSingularHomology.overlapIn U V) n →ₗ[ℤ] ModHomology p V n :=
  homologyLinearMap (modExcisionChainMap p U V) n

/-- Native finite-cyclic relative excision in every degree. -/
def modExcisionEquiv (p : ℕ) (hp : p ≠ 0) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    ModHomology p (RelativeSingularHomology.overlapIn U V) n ≃ₗ[ℤ] ModHomology p V n := by
  let := modExcisionChainMap_quasiIso p hp U V hU hV hcover
  exact (isoOfQuasiIsoAt (modExcisionChainMap p U V) n).toLinearEquiv

theorem modExcisionEquiv_toLinearMap (p : ℕ) (hp : p ≠ 0) (U V : Set X)
    (hU : IsOpen U) (hV : IsOpen V) (hcover : U ∪ V = Set.univ) (n : ℕ) :
    (modExcisionEquiv p hp U V hU hV hcover n).toLinearMap = modExcisionMap p U V n := rfl

/-- The actual inclusion of a pointed subspace on native relative coefficient complexes. -/
def modNeighborhoodChainMap (p : ℕ) (U : Set X) (x : U) :
    complex (ModuleCat.of ℤ (ZMod p)) ({x}ᶜ : Set U) ⟶
      complex (ModuleCat.of ℤ (ZMod p)) ({(x : X)}ᶜ : Set X) :=
  mapChain (ModuleCat.of ℤ (ZMod p)) (subtypeInclusion U)
    (RelativeSingularHomology.inclusion_mapsTo_puncture U x)

/-- The actual pointed neighborhood inclusion is a quasi-isomorphism. -/
theorem modNeighborhoodChainMap_quasiIso [T1Space X] (p : ℕ) (hp : p ≠ 0)
    (U : Set X) (hU : IsOpen U) (x : U) : QuasiIso (modNeighborhoodChainMap p U x) :=
  mapChain_mod_quasiIso_of_integral p hp (subtypeInclusion U) _
    (RelativeSingularHomology.neighborhoodChainMap_quasiIso U hU x)

abbrev modNeighborhoodMap (p : ℕ) (U : Set X) (x : U) (n : ℕ) :
    ModHomology p ({x}ᶜ : Set U) n →ₗ[ℤ] ModHomology p ({(x : X)}ᶜ : Set X) n :=
  homologyLinearMap (modNeighborhoodChainMap p U x) n

/-- Local homology with native cyclic coefficients is computed in any open neighborhood. -/
def modNeighborhoodEquiv [T1Space X] (p : ℕ) (hp : p ≠ 0)
    (U : Set X) (hU : IsOpen U) (x : U) (n : ℕ) :
    ModHomology p ({x}ᶜ : Set U) n ≃ₗ[ℤ] ModHomology p ({(x : X)}ᶜ : Set X) n := by
  let := modNeighborhoodChainMap_quasiIso p hp U hU x
  exact (isoOfQuasiIsoAt (modNeighborhoodChainMap p U x) n).toLinearEquiv

theorem modNeighborhoodEquiv_toLinearMap [T1Space X] (p : ℕ) (hp : p ≠ 0)
    (U : Set X) (hU : IsOpen U) (x : U) (n : ℕ) :
    (modNeighborhoodEquiv p hp U hU x n).toLinearMap = modNeighborhoodMap p U x n := rfl

end NoExoticSixSphere.RelativeCoefficients
