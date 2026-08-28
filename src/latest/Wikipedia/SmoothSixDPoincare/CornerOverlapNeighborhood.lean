import Mathlib.Topology.ContinuousOn

/-!
# Exact overlap near a common injective corner map

Full local equality with one corner map determines the overlap of two
parametrizations on actual open neighborhoods, not only at their center points.
-/

open Set Function Filter Topology

namespace Wikipedia.SmoothSixDPoincare

variable {X Y D M : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  [TopologicalSpace D]

/-- Common injective corner coordinates determine the whole local overlap relation. -/
theorem exists_open_corner_overlap
    {k : X → M} {l : Y → M} {c : D → M} {a : X → D} {b : Y → D}
    {x₀ : X} {y₀ : Y} {W : Set D} (hW : IsOpen W) (hc : InjOn c W)
    (ha : ContinuousAt a x₀) (hb : ContinuousAt b y₀)
    (haW : a x₀ ∈ W) (hbW : b y₀ ∈ W)
    (hk : k =ᶠ[𝓝 x₀] c ∘ a) (hl : l =ᶠ[𝓝 y₀] c ∘ b) :
    ∃ U : Set X, ∃ V : Set Y, IsOpen U ∧ IsOpen V ∧ x₀ ∈ U ∧ y₀ ∈ V ∧
      ∀ x ∈ U, ∀ y ∈ V, k x = l y ↔ a x = b y := by
  obtain ⟨U, hUsub, hU, hxU⟩ :=
    mem_nhds_iff.mp (hk.and (ha.preimage_mem_nhds (hW.mem_nhds haW)))
  obtain ⟨V, hVsub, hV, hyV⟩ :=
    mem_nhds_iff.mp (hl.and (hb.preimage_mem_nhds (hW.mem_nhds hbW)))
  refine ⟨U, V, hU, hV, hxU, hyV, ?_⟩
  intro x hx y hy
  obtain ⟨hkx, hax⟩ := hUsub hx
  obtain ⟨hly, hby⟩ := hVsub hy
  rw [hkx, hly]
  exact ⟨hc hax hby, congrArg c⟩

end Wikipedia.SmoothSixDPoincare
