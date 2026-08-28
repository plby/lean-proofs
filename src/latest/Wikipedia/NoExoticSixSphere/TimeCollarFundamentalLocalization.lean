import Wikipedia.NoExoticSixSphere.TimeCollarRelativeFundamentalClass

/-!
# Localization of the collared half's relative fundamental class

Actual pair maps send the constructed class to the original interior local
class. Composing the interior inclusion with the half's ambient inclusion is
the genuine open-neighborhood map, so the interior-to-half local map is
injective. In particular every interior localization is nonzero.
-/

noncomputable section

open Set Function CategoryTheory ContinuousMap
open scoped Manifold ContDiff

namespace NoExoticSixSphere.TimeCollarDuality

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
open Wikipedia.HopfProblem.SingularMayerVietoris
open RelativeCoefficients
open ModTwoCapProduct (Coefficient)

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  {t : M → ℝ} (C : TimeCollar t B)

theorem boundary_avoid_interior (x : C.positiveInterior) :
    MapsTo (ContinuousMap.id (NonnegativeHalf t)) (boundary t)
      ({C.interiorToHalf x}ᶜ : Set (NonnegativeHalf t)) := by
  intro y hy he
  have he' : y = C.interiorToHalf x := Set.mem_singleton_iff.mp he
  subst y
  exact (ne_of_gt x.property) hy

theorem interiorToHalf_mapsTo_puncture (x : C.positiveInterior) :
    MapsTo C.interiorToHalf ({x}ᶜ : Set C.positiveInterior)
      ({C.interiorToHalf x}ᶜ : Set (NonnegativeHalf t)) := by
  intro y hy he
  apply hy
  apply Subtype.ext
  exact congrArg (fun z : NonnegativeHalf t ↦ z.val) (Set.mem_singleton_iff.mp he)

def interiorLocalMap (p : ℕ) (x : C.positiveInterior) (n : ℕ) :
    RelativeCoefficients.ModHomology p ({x}ᶜ : Set C.positiveInterior) n →ₗ[ℤ]
      RelativeCoefficients.ModHomology p
        ({C.interiorToHalf x}ᶜ : Set (NonnegativeHalf t)) n :=
  RelativeCoefficients.modMap p C.interiorToHalf (interiorToHalf_mapsTo_puncture C x) n

theorem interiorLocalMap_injective [T1Space M] (p : ℕ) (hp : p ≠ 0)
    (x : C.positiveInterior) (n : ℕ) : Injective (interiorLocalMap C p x n) := by
  have hhalf : MapsTo (halfInclusion t)
      ({C.interiorToHalf x}ᶜ : Set (NonnegativeHalf t)) ({x.val}ᶜ : Set M) := by
    intro y hy he
    exact hy (Subtype.ext (Set.mem_singleton_iff.mp he))
  have he := RelativeCoefficients.mapChain_comp (ModuleCat.of ℤ (ZMod p))
    C.interiorToHalf (interiorToHalf_mapsTo_puncture C x) (halfInclusion t) hhalf
  have he' := congrArg (fun k ↦ homologyLinearMap k n) he
  simp only [homologyLinearMap_comp] at he'
  intro a b hab
  apply (RelativeCoefficients.modNeighborhoodEquiv p hp
    (C.positiveInterior : Set M) C.positiveInterior.isOpen x n).injective
  exact (LinearMap.congr_fun he' a).trans
    ((congrArg (RelativeCoefficients.modMap p (halfInclusion t) hhalf n) hab).trans
      (LinearMap.congr_fun he' b).symm)

variable [ChartedSpace (Vector 7) M] [IsManifold (𝓡 7) ∞ M] [T2Space M] [CompactSpace M]

local instance : Fact (Module.finrank ℝ (Vector 7) = (4 + 2) + 1) := ⟨by simp⟩

def interiorLocalClass (x : C.positiveInterior) :
    RelativeCoefficients.ModHomology 2 ({x}ᶜ : Set C.positiveInterior) 7 :=
  ModTwoLocalClass.manifoldClass (E := Vector 7) 4 x

theorem interiorLocalClass_ne_zero (x : C.positiveInterior) :
    interiorLocalClass C x ≠ 0 :=
  ModTwoLocalClass.manifoldClass_ne_zero (E := Vector 7) 4 x

variable (δ : ℝ) (hδ : 0 < δ) (hδw : δ ≤ C.width)

theorem coreFundamentalClass_evaluate (x : C.positiveInterior)
    (hx : x ∈ compactCore C δ hδ) :
    SupportedRelativeHomology.evaluate Coefficient
        (compactCore C δ hδ : Set C.positiveInterior) x hx 7 (coreFundamentalClass C δ hδ) =
      interiorLocalClass C x :=
  CompactSupportedFundamentalClass.isFundamentalOn (E := Vector 7) 4
    (compactCore C δ hδ : Set C.positiveInterior) (compactCore C δ hδ).isCompact x hx

include hδw in
theorem relativeFundamentalClass_local_onCore (x : C.positiveInterior)
    (hx : x ∈ compactCore C δ hδ) :
    RelativeCoefficients.modMap 2 (ContinuousMap.id (NonnegativeHalf t))
        (boundary_avoid_interior C x) 7 (relativeFundamentalClass C) =
      interiorLocalMap C 2 x 7 (interiorLocalClass C x) := by
  have hV : MapsTo (ContinuousMap.id (NonnegativeHalf t))
      (collarRegion C δ : Set (NonnegativeHalf t))
      ({C.interiorToHalf x}ᶜ : Set (NonnegativeHalf t)) := by
    intro y hy he
    have he' : y = C.interiorToHalf x := Set.mem_singleton_iff.mp he
    subst y
    exact (not_lt_of_ge ((mem_compactCore_iff C δ hδ x).mp hx)) hy
  let hK : MapsTo (ContinuousMap.id C.positiveInterior)
      (compactCore C δ hδ : Set C.positiveInterior)ᶜ ({x}ᶜ : Set C.positiveInterior) := by
    intro y hy he
    have he' : y = x := Set.mem_singleton_iff.mp he
    exact hy (he'.symm ▸ hx)
  have h₁ := RelativeCoefficients.mapChain_comp Coefficient
    (ContinuousMap.id (NonnegativeHalf t)) (boundary_subset_collar C δ hδ)
    (ContinuousMap.id (NonnegativeHalf t)) hV
  simp only [ContinuousMap.id_comp] at h₁
  have he₁ := congrArg (fun k ↦ homologyLinearMap k 7) h₁
  simp only [homologyLinearMap_comp] at he₁
  have h₂ := RelativeCoefficients.mapChain_comp Coefficient
    C.interiorToHalf (coreComplement_mapsTo_collar C δ hδ)
    (ContinuousMap.id (NonnegativeHalf t)) hV
  have h₃ := RelativeCoefficients.mapChain_comp Coefficient
    (ContinuousMap.id C.positiveInterior) hK
    C.interiorToHalf (interiorToHalf_mapsTo_puncture C x)
  simp only [ContinuousMap.id_comp] at h₂
  simp only [ContinuousMap.comp_id] at h₃
  have he₂ := congrArg (fun k ↦ homologyLinearMap k 7) (h₂.symm.trans h₃)
  simp only [homologyLinearMap_comp] at he₂
  have hF : boundaryToCollarModEquiv C δ hδ hδw 2 (by decide) 7
      (relativeFundamentalClass C) =
        coreModHomologyEquiv C δ hδ 2 (by decide) 7 (coreFundamentalClass C δ hδ) := by
    rw [relativeFundamentalClass_eq_onCore C δ hδ hδw]
    exact relativeFundamentalClassOnCore_collar C δ hδ hδw
  apply (LinearMap.congr_fun he₁ (relativeFundamentalClass C)).trans
  apply (congrArg (RelativeCoefficients.modMap 2 (ContinuousMap.id (NonnegativeHalf t))
    hV 7) hF).trans
  apply (LinearMap.congr_fun he₂ (coreFundamentalClass C δ hδ)).trans
  exact congrArg (interiorLocalMap C 2 x 7) (coreFundamentalClass_evaluate C δ hδ x hx)

theorem relativeFundamentalClass_local (x : C.positiveInterior) :
    RelativeCoefficients.modMap 2 (ContinuousMap.id (NonnegativeHalf t))
        (boundary_avoid_interior C x) 7 (relativeFundamentalClass C) =
      interiorLocalMap C 2 x 7 (interiorLocalClass C x) := by
  let K : TopologicalSpace.Compacts C.positiveInterior := ⟨{x}, isCompact_singleton⟩
  obtain ⟨δ, hδ, hδw, hK⟩ := compactCore_cofinal C K
  exact relativeFundamentalClass_local_onCore C δ hδ hδw.le x (hK (Set.mem_singleton x))

theorem relativeFundamentalClass_local_ne_zero (x : C.positiveInterior) :
    RelativeCoefficients.modMap 2 (ContinuousMap.id (NonnegativeHalf t))
        (boundary_avoid_interior C x) 7 (relativeFundamentalClass C) ≠ 0 := by
  rw [relativeFundamentalClass_local]
  intro hz
  apply interiorLocalClass_ne_zero C x
  exact interiorLocalMap_injective C 2 (by decide) x 7 (hz.trans (map_zero _).symm)

end NoExoticSixSphere.TimeCollarDuality
