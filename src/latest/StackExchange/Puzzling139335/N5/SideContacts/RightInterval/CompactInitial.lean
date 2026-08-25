import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Compact initial intervals in the unit interval

A nontrivial closed subset of the unit interval that is closed downward
from zero is a closed initial interval. Excluding one makes its upper
endpoint strictly less than one.
-/

open Set

namespace Puzzling139335.N5.SideContacts

theorem exists_positive_initial_interval {T : Set ℝ}
    (hclosed : IsClosed T) (hsub : T ⊆ Icc 0 1) (hzero : 0 ∈ T) (hone : 1 ∉ T)
    (hpos : ∃ y ∈ T, 0 < y)
    (hdown : ∀ {y}, y ∈ T → ∀ z ∈ Icc 0 y, z ∈ T) :
    ∃ b, 0 < b ∧ b < 1 ∧ ∀ y, y ∈ T ↔ 0 ≤ y ∧ y ≤ b := by
  have hcompact : IsCompact T := isCompact_Icc.of_isClosed_subset hclosed hsub
  obtain ⟨b, hb⟩ := hcompact.exists_isGreatest ⟨0, hzero⟩
  obtain ⟨a, ha, ha0⟩ := hpos
  have hb0 : 0 < b := lt_of_lt_of_le ha0 (hb.2 ha)
  have hb_ne : b ≠ 1 := by
    intro heq
    exact hone (heq ▸ hb.1)
  have hb1 : b < 1 := lt_of_le_of_ne (hsub hb.1).2 hb_ne
  refine ⟨b, hb0, hb1, ?_⟩
  intro y
  constructor
  · intro hy
    exact ⟨(hsub hy).1, hb.2 hy⟩
  · intro hy
    exact hdown hb.1 y hy

end Puzzling139335.N5.SideContacts
