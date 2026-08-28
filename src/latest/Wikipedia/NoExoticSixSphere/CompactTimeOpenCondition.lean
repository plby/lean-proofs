import Mathlib.Topology.Maps.Proper.Basic
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Open conditions holding for every time in a compact parameter space
-/

open Set

namespace NoExoticSixSphere

theorem isOpen_forall_compact_time {T X Y : Type*}
    [TopologicalSpace T] [CompactSpace T] [TopologicalSpace X] [TopologicalSpace Y]
    (H : C(T × X, Y)) (W : Set Y) (hW : IsOpen W) :
    IsOpen {x | ∀ t, H (t, x) ∈ W} := by
  have hc : IsClosed (Prod.snd '' (H ⁻¹' W)ᶜ) :=
    isClosedMap_snd_of_compactSpace _ (hW.isClosed_compl.preimage H.continuous)
  have he : {x | ∀ t, H (t, x) ∈ W} = (Prod.snd '' (H ⁻¹' W)ᶜ)ᶜ := by
    ext x
    simp
  rw [he]
  exact hc.isOpen_compl

end NoExoticSixSphere
