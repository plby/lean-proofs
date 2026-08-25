import StackExchange.Puzzling139335.N5.Remainder.Complement
import StackExchange.Puzzling139335.N5.Remainder.Interior
import StackExchange.Puzzling139335.N5.SingletonAsymmetry.Reflection
import StackExchange.Puzzling139335.HalfTurnRemainder.JordanUnion

/-!
# The actual five-incidence remainder is a Jordan region

The retained pair consists of pieces two and three of a normalized
configuration.  Its diagonal symmetry, connected complement, and connected
interior are proved from the actual dissection.  The two original Jordan
pieces therefore meet in a proper Jordan crosscut of their Jordan union.
-/

open Set Schoenflies

namespace Puzzling139335.N5

theorem Normalized.remainder_isConnected_interior {d : SquareDissection}
    (h : Normalized d) (hc : d.HasProtectedCenter) :
    IsConnected (interior (d.piece 2 ∪ d.piece 3)) :=
  h.remainder_isConnected_interior_of_not_invariant (h.singleton_not_diagonal_invariant hc)

theorem Normalized.remainder_isConnected {d : SquareDissection}
    (h : Normalized d) (hc : d.HasProtectedCenter) :
    IsConnected (d.piece 2 ∪ d.piece 3) :=
  h.remainder_isConnected_of_not_invariant (h.singleton_not_diagonal_invariant hc)

/-- The Jordan conclusion needs no assumed connectedness, boundary arc,
rectifiability, or polygonal structure. -/
theorem Normalized.remainder_jordan {d : SquareDissection}
    (h : Normalized d) (hc : d.HasProtectedCenter) :
    IsJordanRegion (d.piece 2 ∪ d.piece 3) :=
  HalfTurnRemainder.isJordanRegion_union_of_connected_interior_compl
    (d.jordan 2) (d.jordan 3) (d.disjoint_interiors (by decide))
    (h.remainder_isConnected_interior hc) h.remainder_isConnected_compl

/-- The whole intersection of the two retained pieces is the proper
crosscut, and the pieces are its actual closed sides. -/
theorem Normalized.remainder_jordanCrosscut {d : SquareDissection}
    (h : Normalized d) (hc : d.HasProtectedCenter) :
    ∃ p q M N,
      JordanCrosscut (frontier (d.piece 2 ∪ d.piece 3))
        (d.piece 2 ∩ d.piece 3) p q ∧
      IsCutPair (frontier (d.piece 2 ∪ d.piece 3)) p q M N ∧
      d.piece 2 = closure (inside (M ∪ (d.piece 2 ∩ d.piece 3))) ∧
      d.piece 3 = closure (inside (N ∪ (d.piece 2 ∩ d.piece 3))) :=
  HalfTurnRemainder.exists_jordanCrosscut_inter_of_connected_interior_compl
    (d.jordan 2) (d.jordan 3) (d.disjoint_interiors (by decide))
    (h.remainder_isConnected_interior hc) h.remainder_isConnected_compl

theorem Normalized.remainder_inter_isArcBetween {d : SquareDissection}
    (h : Normalized d) (hc : d.HasProtectedCenter) :
    ∃ p q, IsArcBetween (d.piece 2 ∩ d.piece 3) p q :=
  HalfTurnRemainder.exists_inter_isArcBetween_of_connected_interior_compl
    (d.jordan 2) (d.jordan 3) (d.disjoint_interiors (by decide))
    (h.remainder_isConnected_interior hc) h.remainder_isConnected_compl

end Puzzling139335.N5
