import StackExchange.Puzzling139335.N4Remainder.IntrinsicReflection
import StackExchange.Puzzling139335.N4Remainder.PairReflection
import StackExchange.Puzzling139335.N4Remainder.Conjugation

/-!
# Intrinsic reversing symmetry forces the outer half-turn pair

The bottom piece's actual endpoint pair is preserved by any of its
intrinsic isometries.  A reversing symmetry is therefore the vertical
midline reflection.  Combining it with the given horizontal reflection
of the outer pair gives the square's central half-turn.

The conclusion is transported from any congruent piece.  No assumption
that an isometry permutes the dissection is used.
-/

open Set

namespace Puzzling139335.N4OuterPair.Configuration

open N4Remainder PlaneIsometries

variable {d : SquareDissection}

/-- Every reversing intrinsic symmetry of the bottom piece forces its
actual partner to be the global half-turn image.  Involutivity need not be
assumed: endpoint rigidity already gives the vertical reflection. -/
theorem outer_halfTurn_of_reversing_symmetry (h : Configuration d)
    (hc : d.HasProtectedCenter) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hdet : (linearMatrix e).det = -1) (he : e '' d.piece 0 = d.piece 0) :
    (AffineIsometryEquiv.pointReflection ℝ squareCenter) '' d.piece 0 = d.piece 1 := by
  have hpair := intrinsic_symmetry_bottom_pair_image h hc e he
  have himage := horizontal_image_eq_pointReflection_image_of_invariant_bottom_pair
    e hdet hpair (d.piece_subset 0) (d.jordan 0).interior_nonempty he
  exact himage.symm.trans h.reflected

/-- The same conclusion holds if any congruent piece has a reversing
intrinsic symmetry. -/
theorem outer_halfTurn_of_piece_reversing_symmetry (h : Configuration d)
    (hc : d.HasProtectedCenter) (i : Fin 4) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (hdet : (linearMatrix e).det = -1) (he : e '' d.piece i = d.piece i) :
    (AffineIsometryEquiv.pointReflection ℝ squareCenter) '' d.piece 0 = d.piece 1 := by
  obtain ⟨f, hf⟩ := d.congruent 0 i
  apply h.outer_halfTurn_of_reversing_symmetry hc ((f.trans e).trans f.symm)
  · exact (conjugate_det f e).trans hdet
  · exact conjugate_image_eq f e hf he

/-- In particular, a middle piece cannot be individually invariant under
the horizontal reflection unless the outer pair is a central half-turn pair. -/
theorem outer_halfTurn_of_piece_horizontal_symmetry (h : Configuration d)
    (hc : d.HasProtectedCenter) (i : Fin 4)
    (he : ReflectionSeparation.horizontal '' d.piece i = d.piece i) :
    (AffineIsometryEquiv.pointReflection ℝ squareCenter) '' d.piece 0 = d.piece 1 :=
  h.outer_halfTurn_of_piece_reversing_symmetry hc i ReflectionSeparation.horizontal
    horizontal_det he

/-- With the explicit outer half-turn case removed, no congruent piece
admits an orientation-reversing intrinsic symmetry. -/
theorem no_reversing_symmetry_of_no_outer_halfTurn (h : Configuration d)
    (hc : d.HasProtectedCenter)
    (hno : (AffineIsometryEquiv.pointReflection ℝ squareCenter) '' d.piece 0 ≠ d.piece 1)
    (i : Fin 4) (e : Plane ≃ᵃⁱ[ℝ] Plane) (hdet : (linearMatrix e).det = -1) :
    e '' d.piece i ≠ d.piece i := by
  intro he
  exact hno (h.outer_halfTurn_of_piece_reversing_symmetry hc i e hdet he)

end Puzzling139335.N4OuterPair.Configuration
