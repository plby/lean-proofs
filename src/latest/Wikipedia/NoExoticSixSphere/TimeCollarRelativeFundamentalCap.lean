import Wikipedia.NoExoticSixSphere.TimeCollarRelativeFundamentalClass
import Wikipedia.NoExoticSixSphere.TimeCollarBoundaryDuality

/-!
# The half's duality map is cap with its actual relative fundamental class

Naturality for the original boundary-to-collar identity and the actual
interior inclusion identifies the constructed duality map with the genuine
relative cap product. Thus cap with this actual class is bijective.
No boundary connecting-class identification is assumed here.
-/

noncomputable section

open Set Function ContinuousMap
open scoped Manifold ContDiff

namespace NoExoticSixSphere.TimeCollarDuality

open GLOrthonormalization RelativeModTwoCochains
open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
open Wikipedia.HopfProblem.SphereHomologyCoefficients

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  [ChartedSpace (Vector 7) M] [IsManifold (𝓡 7) ∞ M] [T2Space M] [CompactSpace M]
  {t : M → ℝ} (C : TimeCollar t B) (δ : ℝ) (hδ : 0 < δ) (hδw : δ ≤ C.width)

theorem interiorCapMap_boundaryCompactSupportMap (p q : ℕ) (h : p + q = 7)
    (c : Cohomology (boundary t) p) :
    interiorCapMap C p q h (boundaryCompactSupportMap C δ hδ hδw p c) =
      modHomologyMap 2 C.interiorToHalf q
        (RelativeModTwoCap.capProductInDegree (compactCore C δ hδ : Set C.positiveInterior)ᶜ h
          (boundaryCoreEquiv C δ hδ hδw p c) (coreFundamentalClass C δ hδ)) := rfl

theorem cap_relativeFundamentalClassOnCore (p q : ℕ) (h : p + q = 7)
    (c : Cohomology (boundary t) p) :
    RelativeModTwoCap.capProductInDegree (boundary t) h c
      (relativeFundamentalClassOnCore C δ hδ hδw) =
      interiorCapMap C p q h (boundaryCompactSupportMap C δ hδ hδw p c) := by
  obtain ⟨v, rfl⟩ := (collarRelativeEquiv C δ hδ hδw p).surjective c
  have h₁ := RelativeModTwoCap.capProductInDegree_naturality
    (ContinuousMap.id (NonnegativeHalf t)) (boundary_subset_collar C δ hδ) h v
    (relativeFundamentalClassOnCore C δ hδ hδw)
  rw [modHomologyMap_id, LinearMap.id_apply] at h₁
  change RelativeModTwoCap.capProductInDegree (boundary t) h
    (collarRelativeEquiv C δ hδ hδw p v) (relativeFundamentalClassOnCore C δ hδ hδw) =
      RelativeModTwoCap.capProductInDegree (collarRegion C δ : Set (NonnegativeHalf t)) h v
        (boundaryToCollarModEquiv C δ hδ hδw 2 (by decide) 7
          (relativeFundamentalClassOnCore C δ hδ hδw)) at h₁
  rw [relativeFundamentalClassOnCore_collar] at h₁
  have h₂ := RelativeModTwoCap.capProductInDegree_naturality C.interiorToHalf
    (coreComplement_mapsTo_collar C δ hδ) h v (coreFundamentalClass C δ hδ)
  have hE : coreExcisionEquiv C δ hδ p v =
      cohomologyPullback C.interiorToHalf (coreComplement_mapsTo_collar C δ hδ) p v :=
    LinearMap.congr_fun (coreExcisionEquiv_toLinearMap C δ hδ p) v
  rw [interiorCapMap_boundaryCompactSupportMap, boundaryCoreEquiv_collar, hE]
  exact h₁.trans h₂.symm

theorem boundaryCompactSupportCanonical_eq_map (p : ℕ) :
    (boundaryCompactSupportCanonical C p).toLinearMap =
      boundaryCompactSupportMap C δ hδ hδw p := by
  unfold boundaryCompactSupportCanonical
  exact boundaryCompactSupportMap_independent C (C.width / 2) (half_pos C.width_pos)
    (half_lt_self C.width_pos).le δ hδ hδw p

theorem cap_relativeFundamentalClass (p q : ℕ) (h : p + q = 7)
    (c : Cohomology (boundary t) p) :
    RelativeModTwoCap.capProductInDegree (boundary t) h c (relativeFundamentalClass C) =
      boundaryDualityMap C p q h c :=
  cap_relativeFundamentalClassOnCore C (C.width / 2) (half_pos C.width_pos)
    (half_lt_self C.width_pos).le p q h c

theorem cap_relativeFundamentalClass_bijective (p q : ℕ) (h : p + q = 7) :
    Bijective (fun c : Cohomology (boundary t) p ↦
      RelativeModTwoCap.capProductInDegree (boundary t) h c (relativeFundamentalClass C)) := by
  have he : (fun c : Cohomology (boundary t) p ↦
      RelativeModTwoCap.capProductInDegree (boundary t) h c (relativeFundamentalClass C)) =
      boundaryDualityMap C p q h := funext (cap_relativeFundamentalClass C p q h)
  rw [he]
  exact boundaryDualityMap_bijective C p q h

end NoExoticSixSphere.TimeCollarDuality
