import StackExchange.Puzzling139335.HalfTurnRemainder.JordanUnion.ConnectedSubset.Arc
import StackExchange.Puzzling139335.HalfTurnRemainder.JordanUnion.ConnectedSubset.Enclosure

/-!
# Compact connected proper subsets of a Jordan curve

A missing point on the curve has a neighborhood disjoint from the compact
subset.  Deleting a smaller open subarc around that point encloses the subset
in a compact arc.  Connectedness then identifies its parameter set with a
closed interval, which is nondegenerate when the subset contains two distinct
points.
-/

open Set

namespace Schoenflies

/-- A compact connected proper subset of a Jordan curve containing two
distinct points is an arc.  No arc structure on the subset is assumed. -/
theorem IsJordanCurve.exists_isArcBetween_compact_connected_subset
    {C E : Set Plane} (hC : IsJordanCurve C)
    (hE : IsCompact E) (hc : IsConnected E) (hsub : E ⊆ C)
    (hproper : E ≠ C) (hnt : E.Nontrivial) :
    ∃ a b : Plane, IsArcBetween E a b := by
  obtain ⟨A, p, q, hA, hEA, _⟩ :=
    hC.exists_arc_enclosing_compact_subset hE hsub hproper
  exact hA.exists_isArcBetween_compact_connected hE hc hEA hnt

end Schoenflies
