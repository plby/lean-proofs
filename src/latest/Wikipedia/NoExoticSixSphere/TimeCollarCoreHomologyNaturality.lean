import Wikipedia.NoExoticSixSphere.TimeCollarCoreHomology
import Wikipedia.NoExoticSixSphere.TimeCollarCoreNaturality
import Wikipedia.NoExoticSixSphere.SupportedRelativeHomology

/-!
# Support restriction preserves the actual boundary-relative homology comparison

The original relative pair maps commute before taking homology. Transport
from an actual compact core into the boundary pair therefore commutes with
restriction of support, with the actual maps retained in every degree.
-/

noncomputable section

open Set Function CategoryTheory ContinuousMap

namespace NoExoticSixSphere.TimeCollarDuality

open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
open Wikipedia.HopfProblem.SingularMayerVietoris
open RelativeCoefficients

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B] [CompactSpace M]
  {t : M → ℝ} (C : TimeCollar t B)
  (δ : ℝ) (hδ : 0 < δ) (hδw : δ ≤ C.width)
  (ε : ℝ) (hε : 0 < ε) (hεw : ε ≤ C.width) (hεδ : ε ≤ δ)

def collarModHomologyMap (p q : ℕ) :
    ModHomology p (collarRegion C ε : Set (NonnegativeHalf t)) q →ₗ[ℤ]
      ModHomology p (collarRegion C δ : Set (NonnegativeHalf t)) q :=
  modMap p (ContinuousMap.id (NonnegativeHalf t)) (collar_antitone C δ ε hεδ) q

theorem boundaryToCollarModEquiv_natural (p : ℕ) (hp : p ≠ 0) (q : ℕ)
    (c : ModHomology p (boundary t) q) :
    collarModHomologyMap C δ ε hεδ p q (boundaryToCollarModEquiv C ε hε hεw p hp q c) =
      boundaryToCollarModEquiv C δ hδ hδw p hp q c := by
  have h := mapChain_comp (ModuleCat.of ℤ (ZMod p))
    (ContinuousMap.id (NonnegativeHalf t)) (boundary_subset_collar C ε hε)
    (ContinuousMap.id (NonnegativeHalf t)) (collar_antitone C δ ε hεδ)
  simp only [ContinuousMap.id_comp] at h
  have he := congrArg (fun k ↦ homologyLinearMap k q) h
  simp only [homologyLinearMap_comp] at he
  exact (LinearMap.congr_fun he c).symm

theorem coreModHomologyEquiv_natural (p : ℕ) (hp : p ≠ 0) (q : ℕ)
    (c : ModHomology p (compactCore C ε hε : Set C.positiveInterior)ᶜ q) :
    collarModHomologyMap C δ ε hεδ p q (coreModHomologyEquiv C ε hε p hp q c) =
      coreModHomologyEquiv C δ hδ p hp q
        (SupportedRelativeHomology.restrict (ModuleCat.of ℤ (ZMod p))
          (compactCore_mono C δ ε hδ hε hεδ) q c) := by
  let hK := compactCore_mono C δ ε hδ hε hεδ
  have h₁ := mapChain_comp (ModuleCat.of ℤ (ZMod p))
    C.interiorToHalf (coreComplement_mapsTo_collar C ε hε)
    (ContinuousMap.id (NonnegativeHalf t)) (collar_antitone C δ ε hεδ)
  have h₂ := mapChain_comp (ModuleCat.of ℤ (ZMod p)) (ContinuousMap.id C.positiveInterior)
    (show MapsTo (ContinuousMap.id C.positiveInterior)
      (compactCore C ε hε : Set C.positiveInterior)ᶜ
      (compactCore C δ hδ : Set C.positiveInterior)ᶜ from fun _ hx hy ↦ hx (hK hy))
    C.interiorToHalf (coreComplement_mapsTo_collar C δ hδ)
  simp only [ContinuousMap.id_comp] at h₁
  simp only [ContinuousMap.comp_id] at h₂
  have he := congrArg (fun k ↦ homologyLinearMap k q) (h₁.symm.trans h₂)
  simp only [homologyLinearMap_comp] at he
  exact LinearMap.congr_fun he c

theorem coreToBoundaryModEquiv_natural (p : ℕ) (hp : p ≠ 0) (q : ℕ)
    (c : ModHomology p (compactCore C ε hε : Set C.positiveInterior)ᶜ q) :
    coreToBoundaryModEquiv C ε hε hεw p hp q c =
      coreToBoundaryModEquiv C δ hδ hδw p hp q
        (SupportedRelativeHomology.restrict (ModuleCat.of ℤ (ZMod p))
          (compactCore_mono C δ ε hδ hε hεδ) q c) := by
  apply (boundaryToCollarModEquiv C δ hδ hδw p hp q).injective
  rw [← boundaryToCollarModEquiv_natural C δ hδ hδw ε hε hεw hεδ p hp q]
  rw [coreToBoundaryModEquiv_collar, coreModHomologyEquiv_natural C δ hδ ε hε hεδ p hp q]
  exact (coreToBoundaryModEquiv_collar C δ hδ hδw p hp q _).symm

end NoExoticSixSphere.TimeCollarDuality
