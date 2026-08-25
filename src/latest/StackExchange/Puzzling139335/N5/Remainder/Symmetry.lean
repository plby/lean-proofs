import StackExchange.Puzzling139335.N5.Normalized
import StackExchange.Puzzling139335.HalfTurnRemainder.Symmetry

/-!
# Diagonal invariance of the actual five-incidence remainder

The two removed pieces are exchanged by the diagonal reflection.  Recovering
the other two pieces as a regular closed remainder proves its symmetry before
any connectedness or Jordan property of that remainder is used.
-/

open Set

namespace Puzzling139335.N5

theorem Normalized.remainder_diagonal_image {d : SquareDissection}
    (h : Normalized d) :
    ReflectionSeparation.diagonal '' (d.piece 2 ∪ d.piece 3) =
      d.piece 2 ∪ d.piece 3 := by
  let e := ReflectionSeparation.diagonal.toHomeomorph
  have hback : e '' d.piece 1 = d.piece 0 := by
    rw [← h.diagonal_image, image_image]
    change (fun x => ReflectionSeparation.diagonal
      (ReflectionSeparation.diagonal x)) '' d.piece 0 = d.piece 0
    have hee : (fun x => ReflectionSeparation.diagonal
        (ReflectionSeparation.diagonal x)) = id :=
      funext ReflectionSeparation.diagonal_involutive
    rw [hee, image_id]
  have hremoved : e '' (d.piece 0 ∪ d.piece 1) = d.piece 0 ∪ d.piece 1 := by
    rw [image_union, show e '' d.piece 0 = d.piece 1 from h.diagonal_image,
      hback, union_comm]
  have hcover : (d.piece 2 ∪ d.piece 3) ∪ (d.piece 0 ∪ d.piece 1) =
      unitSquare := by
    rw [union_comm]
    exact d.four_piece_pair_union
  change e '' (d.piece 2 ∪ d.piece 3) = d.piece 2 ∪ d.piece 3
  apply HalfTurnRemainder.image_union_eq_of_invariant_outer_removed e
    (d.jordan 2).isClosed (d.jordan 3).isClosed
    (d.jordan 2).closure_interior (d.jordan 3).closure_interior hcover
  · exact disjoint_union_right.mpr ⟨d.disjoint_interior_piece (by decide),
      d.disjoint_interior_piece (by decide)⟩
  · exact disjoint_union_right.mpr ⟨d.disjoint_interior_piece (by decide),
      d.disjoint_interior_piece (by decide)⟩
  · exact ReflectionSeparation.diagonal_image_unitSquare
  · exact hremoved

end Puzzling139335.N5
