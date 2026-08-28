import Wikipedia.NoExoticSixSphere.SphereFourTubeRegions
import Wikipedia.NoExoticSixSphere.SmoothManifoldLocalExtension

/-!
# Actual smooth radial extension and cutoff for a four-normal tube

Extend the inverse-coordinate squared radius from a compact tube region.
A separate smooth cutoff is one on a smaller closed region and zero
outside a larger open region. Both functions are globally smooth on the
original manifold, including outside the partial inverse's target.
-/

noncomputable section

open Set Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.SphereFourTube

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] [CompactSpace M] [T2Space M]
  (Φ : PartialDiffeomorph ((𝓡 3).prod (𝓡 4)) (𝓡 7) (Sphere 3 × Vector 4) M ∞)

theorem exists_radial_cutoff_extension (hΦ : Φ.source = univ) :
    ∃ Q χ : C^∞⟮𝓡 7, M; 𝓘(ℝ, ℝ), ℝ⟯,
      (∀ x ∈ closedRegion Φ 2, Q x = radiusSquared Φ x) ∧
      (∀ x ∈ closedRegion Φ (3 / 2), χ x = 1) ∧
      (∀ x ∉ openRegion Φ 2, χ x = 0) ∧ ∀ x, χ x ∈ Icc 0 1 := by
  obtain ⟨Q, hQs, hQeq⟩ := exists_contMDiff_eqOn_closed (radiusSquared Φ)
    (isCompact_closedRegion Φ hΦ 2).isClosed Φ.open_target
    (closedRegion_subset_target Φ hΦ 2) (contMDiffOn_radiusSquared Φ)
  have hd : Disjoint (openRegion Φ 2)ᶜ (closedRegion Φ (3 / 2)) :=
    disjoint_left.mpr (fun x hx hy ↦ hx
      (closedRegion_subset_openRegion Φ (by norm_num : (3 / 2 : ℝ) < 2) hy))
  obtain ⟨χ, hχ0, hχ1, hχrange⟩ := exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓡 7)
    (isOpen_openRegion Φ hΦ 2).isClosed_compl
    (isCompact_closedRegion Φ hΦ (3 / 2)).isClosed hd (n := (⊤ : ℕ∞))
  exact ⟨⟨Q, hQs⟩, χ, hQeq,
    fun x hx ↦ hχ1.self_of_nhdsSet x hx,
    fun x hx ↦ hχ0.self_of_nhdsSet x hx, hχrange⟩

end NoExoticSixSphere.SphereFourTube
