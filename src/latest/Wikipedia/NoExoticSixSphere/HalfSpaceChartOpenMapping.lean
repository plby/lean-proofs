import Wikipedia.NoExoticSixSphere.HalfSpaceHomeomorphNeighborhood

/-!
# Relative openness from actual half-space chart coordinates

The hypotheses retain the chart's neighborhood filter and the actual map's
local agreement with an ambient homeomorphism. Boundary and positive-side
conditions are checked on points of the source, not on a presumed extension.
-/

open Set Function Filter Metric
open scoped Topology

namespace NoExoticSixSphere.ProductHalfSpace

variable {B C X : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [TopologicalSpace X]

theorem image_mem_nhdsWithin_of_halfSpace_chart
    (c : X → ℝ × B) (f : X → ℝ × C) (G : (ℝ × B) ≃ₜ (ℝ × C)) {x : X}
    (hc : Filter.map c (𝓝 x) = 𝓝[{z | 0 ≤ z.1}] (c x)) (hx : (c x).1 = 0)
    (he : ∀ᶠ y in 𝓝 x, f y = G (c y) ∧
      ((c y).1 = 0 → (f y).1 = 0) ∧ (0 < (c y).1 → 0 < (f y).1))
    {s : Set X} (hs : s ∈ 𝓝 x) : f '' s ∈ 𝓝[{z | 0 ≤ z.1}] (f x) := by
  let W := s ∩ {y | f y = G (c y) ∧
    ((c y).1 = 0 → (f y).1 = 0) ∧ (0 < (c y).1 → 0 < (f y).1)}
  have hW : W ∈ 𝓝 x := inter_mem hs he
  have hcW : c '' W ∈ 𝓝[{z | 0 ≤ z.1}] (c x) := by
    rw [← hc]
    exact Filter.image_mem_map hW
  obtain ⟨δ, hδ, hsmall⟩ := Metric.mem_nhdsWithin_iff.mp hcW
  have hzero : ∀ z ∈ ball (c x) δ, z.1 = 0 → (G z).1 = 0 := by
    intro z hz hz0
    obtain ⟨y, hy, hcy⟩ := hsmall ⟨hz, le_of_eq hz0.symm⟩
    have h : (f y).1 = 0 := hy.2.2.1 (by rw [hcy]; exact hz0)
    rwa [hy.2.1, hcy] at h
  have hpos : ∀ z ∈ ball (c x) δ, 0 < z.1 → 0 < (G z).1 := by
    intro z hz hz0
    obtain ⟨y, hy, hcy⟩ := hsmall ⟨hz, hz0.le⟩
    have h : 0 < (f y).1 := hy.2.2.2 (by rw [hcy]; exact hz0)
    rwa [hy.2.1, hcy] at h
  obtain ⟨r, hr, hinv⟩ := exists_inverse_halfSpace_neighborhood G hx isOpen_ball
    (mem_ball_self hδ) hzero hpos
  have hxG : f x = G (c x) := (mem_of_mem_nhds hW).2.1
  apply Metric.mem_nhdsWithin_iff.mpr
  refine ⟨r, hr, ?_⟩
  intro z hz
  have hzball : z ∈ ball (G (c x)) r := by simpa only [← hxG] using hz.1
  obtain ⟨hzin, hz0⟩ := hinv z hzball hz.2
  obtain ⟨y, hy, hcy⟩ := hsmall ⟨hzin, hz0⟩
  refine ⟨y, hy.1, ?_⟩
  rw [hy.2.1, hcy, G.apply_symm_apply]

end NoExoticSixSphere.ProductHalfSpace
