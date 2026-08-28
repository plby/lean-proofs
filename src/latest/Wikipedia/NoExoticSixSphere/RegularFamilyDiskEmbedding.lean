import Wikipedia.NoExoticSixSphere.RegularFamilyCollar
import Wikipedia.NoExoticSixSphere.FamilyDiskEmbedding

/-!
# Immersed disk families with embedded selected slices

One supported graph construction is immersive throughout the parameter set
and embedded on the selected subset. All slices retain their exact boundary
germ, even when the intermediate boundary spheres have self-intersections.
-/

noncomputable section

open Function Set Metric Topology
open scoped ContDiff

namespace NoExoticSixSphere.DiskGraph

variable {P E F : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [HasContDiffBump E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]

theorem exists_regular_family_embedding_rel_sphere_avoiding {K B : Set P}
    (hK : IsCompact K) (hB : IsCompact B) (hBK : B ⊆ K)
    (f : P → E → F) (hf : ContDiff ℝ ∞ (uncurry f))
    (hi : ∀ t ∈ B, InjOn (f t) (sphere (0 : E) 1))
    (hd : ∀ t ∈ K, ∀ x ∈ sphere (0 : E) 1, Injective (fderiv ℝ (f t) x))
    {U : Set (P × E)} (hU : IsOpen U) (hSU : K ×ˢ sphere (0 : E) 1 ⊆ U)
    (S : P → Set F) (ha : ∀ t ∈ K, ∀ x ∈ ball (0 : E) 1,
      (t, x) ∈ U → f t x ∉ S t) :
    ∃ G : P → E → F × (ℝ × E), ContDiff ℝ ∞ (uncurry G) ∧
      (∀ t ∈ B, IsClosedEmbedding (fun x : closedBall (0 : E) 1 ↦ G t x.val)) ∧
      (∀ t ∈ K, ∀ x ∈ closedBall (0 : E) 1, Injective (fderiv ℝ (G t) x)) ∧
      (∀ t ∈ K, ∀ x ∈ ball (0 : E) 1, G t x ∉ S t ×ˢ ({0} : Set (ℝ × E))) ∧
      ∃ V : Set E, IsOpen V ∧ sphere (0 : E) 1 ⊆ V ∧
        ∀ t ∈ K, ∀ x ∈ V, G t x = (f t x, 0) := by
  obtain ⟨r, hr, hr1, hsub, hfi, hfd⟩ :=
    FamilyEmbedding.exists_uniform_regular_annulus hK hB hBK f hf hi hd hU hSU
  have hs (t : P) : ContDiff ℝ ∞ (f t) := hf.comp (contDiff_const.prodMk contDiff_id)
  refine ⟨fun t ↦ map (f t) r hr, contDiff_family_map f hf r hr, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact isClosedEmbedding_disk (f t) r hr (fun _ _ ↦ (hs t).contDiffAt) (hfi t ht)
  · intro t ht x hx
    exact injective_fderiv_map (f t) r hr (hs t).contDiffAt (hfd t ht x hx)
  · intro t ht
    apply avoids_oldAmbient (f t) r hr (S t)
    intro x hx hrx
    exact ha t ht x hx (hsub ⟨ht, ball_subset_closedBall hx, hrx⟩)
  · refine ⟨{x : E | r < ‖x‖}, isOpen_lt continuous_const continuous_norm, ?_, ?_⟩
    · intro x hx
      have hn : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
      exact hr1.trans_eq hn.symm
    · intro t _ x hx
      exact map_eq_on_collar (f t) r hr hx.le

end NoExoticSixSphere.DiskGraph
