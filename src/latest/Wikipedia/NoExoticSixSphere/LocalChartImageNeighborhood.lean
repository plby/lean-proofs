import Mathlib.Topology.Homeomorph.Defs
import Mathlib.Topology.Neighborhoods

/-!
# Images of neighborhoods under an ambient homeomorphism in local coordinates
-/

open Set Function Filter
open scoped Topology

namespace NoExoticSixSphere

variable {X E F : Type*} [TopologicalSpace X] [TopologicalSpace E] [TopologicalSpace F]

theorem image_mem_nhds_of_homeomorph_chart (c : X → E) (f : X → F) (G : E ≃ₜ F) {x : X}
    (hc : Filter.map c (𝓝 x) = 𝓝 (c x)) (he : ∀ᶠ y in 𝓝 x, f y = G (c y))
    {s : Set X} (hs : s ∈ 𝓝 x) : f '' s ∈ 𝓝 (f x) := by
  let W := s ∩ {y | f y = G (c y)}
  have hW : W ∈ 𝓝 x := inter_mem hs he
  have hcW : c '' W ∈ 𝓝 (c x) := by
    rw [← hc]
    exact Filter.image_mem_map hW
  have hG : G '' (c '' W) ∈ 𝓝 (G (c x)) := by
    rw [← G.map_nhds_eq]
    exact Filter.image_mem_map hcW
  have hxG : f x = G (c x) := (mem_of_mem_nhds hW).2
  rw [← hxG] at hG
  apply mem_of_superset hG
  rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
  exact ⟨y, hy.1, hy.2⟩

end NoExoticSixSphere
