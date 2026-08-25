import StackExchange.Puzzling139335.N4OuterPair.Defs
import StackExchange.Puzzling139335.HalfTurnRemainder.Symmetry

/-!
# The actual middle union inherits the outer reflection

The middle union is recovered as the closure of the square after removal of
the outer pair.  This remains exact when Jordan boundaries have positive area.
No connectedness or interface property of the middle union is assumed here.
-/

open Set

namespace Puzzling139335.N4OuterPair

theorem middle_union_eq_closure (d : SquareDissection) :
    d.piece 2 ∪ d.piece 3 = closure (unitSquare \ (d.piece 0 ∪ d.piece 1)) := by
  apply HalfTurnRemainder.union_eq_closure_sdiff
    (d.jordan 2).isClosed (d.jordan 3).isClosed
    (d.jordan 2).closure_interior (d.jordan 3).closure_interior
  · rw [union_comm]
    exact d.four_piece_pair_union
  · exact disjoint_union_right.mpr
      ⟨d.disjoint_interior_piece (by decide), d.disjoint_interior_piece (by decide)⟩
  · exact disjoint_union_right.mpr
      ⟨d.disjoint_interior_piece (by decide), d.disjoint_interior_piece (by decide)⟩

namespace Configuration

variable {d : SquareDissection}

theorem reflection_back (h : Configuration d) :
    ReflectionSeparation.horizontal '' d.piece 1 = d.piece 0 := by
  rw [← h.reflected, image_image]
  change (fun p => ReflectionSeparation.horizontal (ReflectionSeparation.horizontal p)) ''
    d.piece 0 = d.piece 0
  simp only [ReflectionSeparation.horizontal_involutive, image_id']

theorem outer_union_reflected (h : Configuration d) :
    ReflectionSeparation.horizontal '' (d.piece 0 ∪ d.piece 1) =
      d.piece 0 ∪ d.piece 1 := by
  rw [image_union, h.reflected, h.reflection_back, union_comm]

/-- Reflection invariance is proved for the actual union, including its boundary. -/
theorem middle_union_reflected (h : Configuration d) :
    ReflectionSeparation.horizontal '' (d.piece 2 ∪ d.piece 3) =
      d.piece 2 ∪ d.piece 3 := by
  let e := ReflectionSeparation.horizontal.toHomeomorph
  have hQ : e '' unitSquare = unitSquare :=
    ReflectionSeparation.horizontal_image_unitSquare
  have houter : e '' (d.piece 0 ∪ d.piece 1) = d.piece 0 ∪ d.piece 1 :=
    h.outer_union_reflected
  change e '' (d.piece 2 ∪ d.piece 3) = d.piece 2 ∪ d.piece 3
  rw [middle_union_eq_closure d, e.image_closure, image_sdiff e.injective, hQ, houter]

end Configuration

end Puzzling139335.N4OuterPair
