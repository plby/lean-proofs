import Wikipedia.HopfProblem.DegreeCollapsePatchSourceCoordinates
import Wikipedia.HopfProblem.DegreeCollapseNativeMapOrientation
import Wikipedia.HopfProblem.OrbitPairOrientationWeights

/-!
# Coherent source orientation factors along an immersed branch arc

The inverse ambient strip chart induces genuine coordinates on the
selected immersed source patch. Their normalized determinant sign is
constant along the whole original source arc. Equivalently, the two
orientation-weighted endpoint determinants have positive product.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource

open Wikipedia.SmoothSixDPoincare
open OrbitPair.DeterminantSignCover OrbitPair.OrientationWeights

variable {D B E M G N : Type*}
  [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace N] [ChartedSpace G N] [IsManifold 𝓘(ℝ, G) ∞ N]
  (o : Orientation (tangentBundleCore 𝓘(ℝ, G) N))
  (Φ : PartialDiffeomorph 𝓘(ℝ, D × B) 𝓘(ℝ, E) (D × B) M ∞)
  (F : N → M) (J : D ≃L[ℝ] G)

theorem patch_source_orientation_endpoints
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F)
    (hi : ∀ x, Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x))
    {K U : Set N} (hU : IsOpen U) (hUK : U ⊆ K)
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ F '' K ↔ q.2 = 0)
    {a : ℝ → N} (ha : Continuous a)
    (haU : MapsTo a (Icc (0 : ℝ) 1) U)
    (haT : MapsTo (F ∘ a) (Icc (0 : ℝ) 1) Φ.target) :
    NativeMapOrientation.sign o (patchSourceCoordinates Φ F) J (a 0) =
      NativeMapOrientation.sign o (patchSourceCoordinates Φ F) J (a 1) := by
  let W := U ∩ F ⁻¹' Φ.target
  have hW : IsOpen W := hU.inter (Φ.open_target.preimage hF.continuous)
  have hg : ContMDiffOn 𝓘(ℝ, G) 𝓘(ℝ, D) ∞ (patchSourceCoordinates Φ F) W :=
    (contMDiffOn_patchSourceCoordinates Φ F hF).mono inter_subset_right
  have hbij : ∀ x ∈ W, Bijective
      (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, D) (patchSourceCoordinates Φ F) x) := by
    intro x hx
    exact bijective_mfderiv_patchSourceCoordinates Φ F hF hclean
      (mem_of_superset (hU.mem_nhds hx.1) hUK) hx.2 (hi x) J.symm.toLinearEquiv.finrank_eq
  exact NativeMapOrientation.sign_eq_on_preconnected o (patchSourceCoordinates Φ F) J
    hW hg hbij (convex_Icc (0 : ℝ) 1).isPreconnected ha.continuousOn
    (fun t ht => ⟨haU ht, haT ht⟩) (by simp) (by simp)

theorem weighted_patch_source_determinants_pos
    (hF : ContMDiff 𝓘(ℝ, G) 𝓘(ℝ, E) ∞ F)
    (hi : ∀ x, Injective (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, E) F x))
    {K U : Set N} (hU : IsOpen U) (hUK : U ⊆ K)
    (hclean : ∀ q ∈ Φ.source, Φ q ∈ F '' K ↔ q.2 = 0)
    {a : ℝ → N} (ha : Continuous a)
    (haU : MapsTo a (Icc (0 : ℝ) 1) U)
    (haT : MapsTo (F ∘ a) (Icc (0 : ℝ) 1) Φ.target) :
    0 < (weight (o.rawSign (a 0)) *
        (NativeMapOrientation.nativeFrame (I := 𝓘(ℝ, G))
          (patchSourceCoordinates Φ F) J (a 0)).det) *
      (weight (o.rawSign (a 1)) *
        (NativeMapOrientation.nativeFrame (I := 𝓘(ℝ, G))
          (patchSourceCoordinates Φ F) J (a 1)).det) := by
  have hbij (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : Bijective
      (mfderiv 𝓘(ℝ, G) 𝓘(ℝ, D) (patchSourceCoordinates Φ F) (a t)) :=
    bijective_mfderiv_patchSourceCoordinates Φ F hF hclean
      (mem_of_superset (hU.mem_nhds (haU ht)) hUK) (haT ht) (hi (a t))
      J.symm.toLinearEquiv.finrank_eq
  exact (action_eq_iff_product_pos _ _
    (NativeMapOrientation.nativeFrame_det_ne_zero (patchSourceCoordinates Φ F) J (hbij 0 (by simp)))
    (NativeMapOrientation.nativeFrame_det_ne_zero (patchSourceCoordinates Φ F) J (hbij 1 (by simp)))
    (o.rawSign (a 0)) (o.rawSign (a 1))).mp
      (patch_source_orientation_endpoints o Φ F J hF hi hU hUK hclean ha haU haT)

end Wikipedia.HopfProblem.DegreeCollapse.ImmersedSource
