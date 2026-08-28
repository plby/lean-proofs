import Mathlib.Topology.Separation.Hausdorff

/-!
# Compact-source neighborhoods excluding all unwanted branches

If an open source set contains an entire fiber, the complement of the
image of its closed complement is an open target neighborhood whose full
preimage stays in that source set. This excludes global branches, not
merely branches of a selected local parametrization.
-/

open Set Function Topology

namespace NoExoticSixSphere

theorem exists_open_full_preimage_subset {X Y : Type*}
    [TopologicalSpace X] [CompactSpace X] [TopologicalSpace Y] [T2Space Y]
    {f : X → Y} (hf : Continuous f) {U : Set X} (hU : IsOpen U) {y : Y}
    (hy : ∀ x, f x = y → x ∈ U) :
    ∃ O : Set Y, IsOpen O ∧ y ∈ O ∧ ∀ x, f x ∈ O → x ∈ U := by
  refine ⟨(f '' Uᶜ)ᶜ, (hU.isClosed_compl.isCompact.image hf).isClosed.isOpen_compl, ?_, ?_⟩
  · rintro ⟨x, hx, he⟩
    exact hx (hy x he)
  · intro x hx
    by_contra hn
    exact hx ⟨x, hn, rfl⟩

end NoExoticSixSphere
