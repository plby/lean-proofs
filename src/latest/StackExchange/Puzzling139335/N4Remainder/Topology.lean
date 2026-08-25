import StackExchange.Puzzling139335.N4Remainder.Symmetry
import StackExchange.Puzzling139335.N4Remainder.ConnectedInterior
import StackExchange.Puzzling139335.N4Remainder.NoHoles
import StackExchange.Puzzling139335.N4OuterPair.Remainder
import StackExchange.Puzzling139335.HalfTurnRemainder.JordanUnion

/-!
# The actual two-piece middle remainder

The given horizontal reflection preserves the middle union.  If the
union's interior is disconnected, the component containing the protected
center is individually invariant.  Intrinsic symmetry rigidity then
forces the outer pair to be a central half-turn pair.

Once that explicitly recorded alternative is removed, the middle union
has connected interior and connected complement.  The proved Jordan-union
theorem supplies its Jordan boundary and its single proper common arc;
neither is assumed as a geometric certificate.
-/

open Set Schoenflies

namespace Puzzling139335.N4OuterPair.Configuration

open N4Remainder HalfTurnRemainder

variable {d : SquareDissection}

/-- An actual outer half-turn pair is the only alternative to connected
interior of the middle union. -/
theorem outer_halfTurn_or_middle_connected_interior (h : Configuration d)
    (hc : d.HasProtectedCenter) :
    (AffineIsometryEquiv.pointReflection ℝ squareCenter) '' d.piece 0 = d.piece 1 ∨
      IsConnected (interior (d.piece 2 ∪ d.piece 3)) := by
  rcases h.center_in_middle hc with hc2 | hc3
  · rcases isConnected_interior_union_or_image_eq
        (d.jordan 2) (d.jordan 3) (d.disjoint_interiors (by decide)) hc2
        ReflectionSeparation.horizontal.toHomeomorph
        ReflectionSeparation.horizontal_center h.middle_union_reflected with hint | hinv
    · exact Or.inr hint
    · exact Or.inl (h.outer_halfTurn_of_piece_horizontal_symmetry hc 2 hinv)
  · have hsym : ReflectionSeparation.horizontal.toHomeomorph ''
          (d.piece 3 ∪ d.piece 2) = d.piece 3 ∪ d.piece 2 := by
      have hsymBase : ReflectionSeparation.horizontal.toHomeomorph ''
          (d.piece 2 ∪ d.piece 3) = d.piece 2 ∪ d.piece 3 := h.middle_union_reflected
      simpa only [union_comm] using hsymBase
    rcases isConnected_interior_union_or_image_eq
        (d.jordan 3) (d.jordan 2) (d.disjoint_interiors (by decide)) hc3
        ReflectionSeparation.horizontal.toHomeomorph
        ReflectionSeparation.horizontal_center hsym with hint | hinv
    · exact Or.inr (by simpa only [union_comm] using hint)
    · exact Or.inl (h.outer_halfTurn_of_piece_horizontal_symmetry hc 3 hinv)

/-- Removing the explicit central outer-pair case gives connected interior
of the actual remainder. -/
theorem middle_union_isConnected_interior_of_no_outer_halfTurn (h : Configuration d)
    (hc : d.HasProtectedCenter)
    (hno : (AffineIsometryEquiv.pointReflection ℝ squareCenter) '' d.piece 0 ≠ d.piece 1) :
    IsConnected (interior (d.piece 2 ∪ d.piece 3)) :=
  (h.outer_halfTurn_or_middle_connected_interior hc).resolve_left hno

/-- The actual middle union is a Jordan region, and its whole common set
is one proper Jordan crosscut with the original tiles as its closed sides. -/
theorem middle_union_jordanCrosscut_of_no_outer_halfTurn (h : Configuration d)
    (hc : d.HasProtectedCenter)
    (hno : (AffineIsometryEquiv.pointReflection ℝ squareCenter) '' d.piece 0 ≠ d.piece 1) :
    IsJordanRegion (d.piece 2 ∪ d.piece 3) ∧ ∃ p q M N,
      JordanCrosscut (frontier (d.piece 2 ∪ d.piece 3)) (d.piece 2 ∩ d.piece 3) p q ∧
      IsCutPair (frontier (d.piece 2 ∪ d.piece 3)) p q M N ∧
      d.piece 2 = closure (inside (M ∪ (d.piece 2 ∩ d.piece 3))) ∧
      d.piece 3 = closure (inside (N ∪ (d.piece 2 ∩ d.piece 3))) :=
  jordan_union_of_connected_interior_compl
    (d.jordan 2) (d.jordan 3) (d.disjoint_interiors (by decide))
    (h.middle_union_isConnected_interior_of_no_outer_halfTurn hc hno)
    h.middle_union_isConnected_compl

/-- The Jordan-union projection, retaining the explicit half-turn exclusion. -/
theorem middle_union_jordan_of_no_outer_halfTurn (h : Configuration d)
    (hc : d.HasProtectedCenter)
    (hno : (AffineIsometryEquiv.pointReflection ℝ squareCenter) '' d.piece 0 ≠ d.piece 1) :
    IsJordanRegion (d.piece 2 ∪ d.piece 3) :=
  (h.middle_union_jordanCrosscut_of_no_outer_halfTurn hc hno).1

/-- In unconditional form, the proof records the actual central outer pair
as its only exceptional case. -/
theorem outer_halfTurn_or_middle_union_jordan (h : Configuration d)
    (hc : d.HasProtectedCenter) :
    (AffineIsometryEquiv.pointReflection ℝ squareCenter) '' d.piece 0 = d.piece 1 ∨
      IsJordanRegion (d.piece 2 ∪ d.piece 3) := by
  rcases h.outer_halfTurn_or_middle_connected_interior hc with hpair | hint
  · exact Or.inl hpair
  · exact Or.inr (isJordanRegion_union_of_connected_interior_compl
      (d.jordan 2) (d.jordan 3) (d.disjoint_interiors (by decide)) hint
      h.middle_union_isConnected_compl)

/-- The actual common set is one nondegenerate arc. -/
theorem middle_inter_isArcBetween_of_no_outer_halfTurn (h : Configuration d)
    (hc : d.HasProtectedCenter)
    (hno : (AffineIsometryEquiv.pointReflection ℝ squareCenter) '' d.piece 0 ≠ d.piece 1) :
    ∃ p q : Plane, IsArcBetween (d.piece 2 ∩ d.piece 3) p q :=
  exists_inter_isArcBetween_of_connected_interior_compl
    (d.jordan 2) (d.jordan 3) (d.disjoint_interiors (by decide))
    (h.middle_union_isConnected_interior_of_no_outer_halfTurn hc hno)
    h.middle_union_isConnected_compl

/-- The two middle pieces share at least two distinct actual points. -/
theorem middle_inter_nontrivial_of_no_outer_halfTurn (h : Configuration d)
    (hc : d.HasProtectedCenter)
    (hno : (AffineIsometryEquiv.pointReflection ℝ squareCenter) '' d.piece 0 ≠ d.piece 1) :
    (d.piece 2 ∩ d.piece 3).Nontrivial :=
  inter_nontrivial_of_connected_interior_union
    (d.jordan 2) (d.jordan 3) (d.disjoint_interiors (by decide))
    (h.middle_union_isConnected_interior_of_no_outer_halfTurn hc hno)

end Puzzling139335.N4OuterPair.Configuration
