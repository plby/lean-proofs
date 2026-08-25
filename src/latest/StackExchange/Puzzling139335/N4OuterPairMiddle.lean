import StackExchange.Puzzling139335.N4Remainder
import StackExchange.Puzzling139335.HalfTurnPair

/-!
# The middle remainder with the half-turn alternative discharged

These are consequences of an actual reflected outer-pair configuration and
a hypothetical protected center. The general half-turn-pair obstruction
removes the only exceptional case in the Jordan-remainder reduction.
-/

open Set Schoenflies

namespace Puzzling139335.N4OuterPair.Configuration

variable {d : SquareDissection}

/-- The outer pair cannot also be exchanged by the centered half-turn. -/
theorem no_outer_halfTurn_of_protected (_h : Configuration d)
    (hc : d.HasProtectedCenter) :
    AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece 0 ≠ d.piece 1 :=
  fun hpair => d.not_hasProtectedCenter_of_halfTurn_pair (by decide) hpair hc

/-- The actual middle union and common cut, with no remaining symmetry
exclusion among the hypotheses. -/
theorem middle_union_jordanCrosscut_of_protected (h : Configuration d)
    (hc : d.HasProtectedCenter) :
    IsJordanRegion (d.piece 2 ∪ d.piece 3) ∧ ∃ p q M N,
      JordanCrosscut (frontier (d.piece 2 ∪ d.piece 3)) (d.piece 2 ∩ d.piece 3) p q ∧
      IsCutPair (frontier (d.piece 2 ∪ d.piece 3)) p q M N ∧
      d.piece 2 = closure (inside (M ∪ (d.piece 2 ∩ d.piece 3))) ∧
      d.piece 3 = closure (inside (N ∪ (d.piece 2 ∩ d.piece 3))) :=
  h.middle_union_jordanCrosscut_of_no_outer_halfTurn hc
    (h.no_outer_halfTurn_of_protected hc)

/-- The actual middle union is a Jordan region. -/
theorem middle_union_jordan_of_protected (h : Configuration d)
    (hc : d.HasProtectedCenter) : IsJordanRegion (d.piece 2 ∪ d.piece 3) :=
  (h.middle_union_jordanCrosscut_of_protected hc).1

/-- The actual middle intersection contains two distinct points. -/
theorem middle_inter_nontrivial_of_protected (h : Configuration d)
    (hc : d.HasProtectedCenter) : (d.piece 2 ∩ d.piece 3).Nontrivial :=
  h.middle_inter_nontrivial_of_no_outer_halfTurn hc
    (h.no_outer_halfTurn_of_protected hc)

end Puzzling139335.N4OuterPair.Configuration
