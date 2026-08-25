import StackExchange.Puzzling139335.N5.Remainder.Symmetry
import StackExchange.Puzzling139335.N5.Remainder.InvariantInterior
import StackExchange.Puzzling139335.DoubleCorner.RotationBoundary

/-!
# Connected interior of the actual five-incidence remainder

Unique ownership of the top-right corner gives a diagonal fixed point in the
interior of the singleton-corner piece.  If its interior component in the
remainder did not meet the other tile, the diagonal would preserve the
singleton-corner piece itself.
-/

open Set Metric

namespace Puzzling139335.N5

/-- The actual relative neighborhood at the uniquely owned top-right corner
contains a diagonal fixed point in the ambient interior of its owner. -/
theorem Normalized.exists_fixed_diagonal_interior_singleton
    {d : SquareDissection} (h : Normalized d) :
    ∃ x ∈ interior (d.piece 2), ReflectionSeparation.diagonal x = x := by
  obtain ⟨ε, hε, hnear⟩ := d.unique_piece_relative_neighborhood 2 h.unique_top_right
  let δ : ℝ := min ε 1 / 4
  have hδ : 0 < δ := by
    exact div_pos (lt_min hε (by norm_num)) (by norm_num)
  have hδε : 4 * δ ≤ ε := by
    have hm := min_le_left ε (1 : ℝ)
    dsimp only [δ]
    linarith
  have hδone : δ ≤ 1 / 4 := by
    exact div_le_div_of_nonneg_right (min_le_right ε (1 : ℝ)) (by norm_num)
  let x : Plane := !₂[1 - δ, 1 - δ]
  have hxSquare : x ∈ interior unitSquare := by
    apply DoubleCorner.interior_unitSquare_of_coordinates
    · change 0 < 1 - δ ∧ 1 - δ < 1
      constructor <;> linarith
    · change 0 < 1 - δ ∧ 1 - δ < 1
      constructor <;> linarith
  have hd : dist x (corner 2) ^ 2 = 2 * δ ^ 2 := by
    rw [plane_dist_sq]
    norm_num [x, corner, Fin.ext_iff] <;> ring
  have hdist : dist x (corner 2) ≤ 2 * δ := by
    apply (sq_le_sq₀ dist_nonneg (by positivity : 0 ≤ 2 * δ)).mp
    nlinarith [sq_nonneg δ]
  have hxball : x ∈ ball (corner 2) ε := by
    apply mem_ball.mpr
    linarith
  have hopen : IsOpen (ball (corner 2) ε ∩ interior unitSquare) :=
    isOpen_ball.inter isOpen_interior
  have hsub : ball (corner 2) ε ∩ interior unitSquare ⊆ d.piece 2 :=
    fun _ hx => hnear ⟨hx.1, interior_subset hx.2⟩
  exact ⟨x, interior_maximal hsub hopen ⟨hxball, hxSquare⟩,
    ReflectionSeparation.diagonal_fixed rfl⟩

/-- The non-invariance premise concerns an actual tile image, and is
discharged from the protected center in the public remainder module. -/
theorem Normalized.remainder_isConnected_interior_of_not_invariant
    {d : SquareDissection} (h : Normalized d)
    (hnot : ReflectionSeparation.diagonal '' d.piece 2 ≠ d.piece 2) :
    IsConnected (interior (d.piece 2 ∪ d.piece 3)) := by
  obtain ⟨x, hx, hfix⟩ := h.exists_fixed_diagonal_interior_singleton
  exact Remainder.isConnected_interior_union_of_invariant_homeomorph
    (d.jordan 2) (d.jordan 3) ReflectionSeparation.diagonal.toHomeomorph
    hx hfix h.remainder_diagonal_image hnot

theorem Normalized.remainder_isConnected_of_not_invariant
    {d : SquareDissection} (h : Normalized d)
    (hnot : ReflectionSeparation.diagonal '' d.piece 2 ≠ d.piece 2) :
    IsConnected (d.piece 2 ∪ d.piece 3) := by
  rw [← HalfTurnRemainder.closure_interior_union
    (d.jordan 2).isClosed (d.jordan 3).isClosed
    (d.jordan 2).closure_interior (d.jordan 3).closure_interior]
  exact (h.remainder_isConnected_interior_of_not_invariant hnot).closure

end Puzzling139335.N5
