import StackExchange.Puzzling139335.CentralRotation.LocalInvariantArc.Component
import StackExchange.Puzzling139335.CentralRotation.LocalInvariantArc.CompactSubarc

/-!
# A local invariant arc at a fixed point

An isometry carrying one subarc of a Jordan curve to another preserves a
smaller subarc around every common internal fixed point.  The smaller arc is
obtained as a connected component of the curve in a small closed ball.

No orientation assumption, differentiability, or length assumption is used.
-/

open Set

namespace Puzzling139335.CentralRotation

/-- An internal fixed point in the overlap of two matching Jordan subarcs has
an invariant simple subarc around it. -/
theorem exists_invariant_subarc {C I J : Set Plane} {p q r s z : Plane}
    (hC : Schoenflies.IsJordanCurve C) (hI : Schoenflies.IsArcBetween I p q)
    (hJ : Schoenflies.IsArcBetween J r s) (hIC : I ⊆ C) (hJC : J ⊆ C)
    (k : Plane ≃ᵃⁱ[ℝ] Plane) (hmap : k '' I = J) (hzI : z ∈ I \ {p, q})
    (hzJ : z ∈ J \ {r, s}) (hfix : k z = z) :
    ∃ E a b, Schoenflies.IsArcBetween E a b ∧ z ∈ E \ {a, b} ∧
      E ⊆ I ∩ J ∧ k '' E = E := by
  obtain ⟨E, hEcompact, hEconn, hEsub, hEnbhd, hEmap⟩ :=
    exists_invariant_arc_component hC hI hJ hIC hJC k hmap hzI hzJ hfix
  obtain ⟨a, b, hEarc, hzE⟩ :=
    hI.exists_isArcBetween_compact_connected_neighborhood hEcompact hEconn
      (hEsub.trans inter_subset_left) hzI hEnbhd
  exact ⟨E, a, b, hEarc, hzE, hEsub, hEmap⟩

end Puzzling139335.CentralRotation
