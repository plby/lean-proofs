import StackExchange.Puzzling139335.N5.TypeReduction
import StackExchange.Puzzling139335.N8.Pairs

/-!
# Counting occurrences of full intrinsic corner types

For an actual corner occurrence, belonging to a full intrinsic type is
equivalent to unique ownership of the physical corner.  Pullback by the
placement is injective, so counting such occurrences by pieces counts each
uniquely owned square corner exactly once.
-/

open scoped BigOperators

namespace Puzzling139335.N7

/-- At an actual square-corner occurrence, fullness of its intrinsic type
is equivalent to unique ownership of that physical corner. -/
theorem intrinsicCorner_mem_full_iff_count_one (d : SquareDissection) {i j : Fin 4}
    (hi : corner j ∈ d.piece i) :
    d.intrinsicCorner i j ∈ N5.fullCornerTypes d ↔ d.cornerTileCount j = 1 := by
  constructor
  · intro hfull
    exact N5.corner_count_one_of_unique_owner d hi
      (N5.unique_corner_of_type_mem_full d hfull)
  · intro hcount
    exact (N5.mem_fullCornerTypes d).mpr ⟨i, j, hi, hcount, rfl⟩

open scoped Classical in
/-- Injectivity of a placement identifies the full types occurring in one
piece with that piece's uniquely owned physical square corners. -/
theorem full_intrinsicPair_card (d : SquareDissection) (i : Fin 4) :
    ((N8.intrinsicPair d i).filter fun v => v ∈ N5.fullCornerTypes d).card =
      (Finset.univ.filter fun j : Fin 4 =>
        corner j ∈ d.piece i ∧ d.cornerTileCount j = 1).card := by
  classical
  rw [N8.intrinsicPair, Finset.filter_image,
    Finset.card_image_of_injective _ (d.intrinsicCorner_injective i)]
  congr 1
  ext j
  simp only [Finset.mem_filter, N8.mem_cornerSet, Finset.mem_univ, true_and]
  exact and_congr_right fun hi => intrinsicCorner_mem_full_iff_count_one d hi

open scoped Classical in
/-- Double-counting the actual full occurrences. No incidence-pattern or
protected-center assumption is needed for this identity. -/
theorem unique_corner_count_eq_full_occurrences (d : SquareDissection) :
    (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card =
      ∑ i : Fin 4,
        ((N8.intrinsicPair d i).filter fun v => v ∈ N5.fullCornerTypes d).card := by
  classical
  symm
  calc
    (∑ i : Fin 4,
        ((N8.intrinsicPair d i).filter fun v => v ∈ N5.fullCornerTypes d).card) =
        ∑ i : Fin 4, (Finset.univ.filter fun j : Fin 4 =>
          corner j ∈ d.piece i ∧ d.cornerTileCount j = 1).card := by
      exact Finset.sum_congr rfl fun i _ => full_intrinsicPair_card d i
    _ = ∑ j : Fin 4, (Finset.univ.filter fun i : Fin 4 =>
          corner j ∈ d.piece i ∧ d.cornerTileCount j = 1).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
      exact Finset.sum_comm
    _ = ∑ j : Fin 4, if d.cornerTileCount j = 1 then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro j _
      by_cases hcount : d.cornerTileCount j = 1
      · have hcard : (Finset.univ.filter fun i : Fin 4 =>
            corner j ∈ d.piece i).card = 1 := hcount
        simpa only [hcount, and_true, if_true] using hcard
      · simp only [hcount, and_false, Finset.filter_false, Finset.card_empty, if_false]
    _ = (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]

end Puzzling139335.N7
