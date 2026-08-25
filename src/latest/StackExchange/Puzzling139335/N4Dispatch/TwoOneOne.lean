import StackExchange.Puzzling139335.N4Dispatch.TwoOneOne.Normalization
import StackExchange.Puzzling139335.N4Dispatch.TwoOneOne.Types
import StackExchange.Puzzling139335.N4Dispatch.TwoOneOne.Reflection
import StackExchange.Puzzling139335.N4TwoOneOne.Configuration

/-!
# Routing the actual degree-(2,1,1,0) case

The corner-count pattern is normalized by a common symmetry and a
relabeling of the four pieces. The two singleton types must coincide:
otherwise the double piece and the two singleton pieces would use four
distinct supporting corner types. Unique corner ownership then makes
their relative placement a square symmetry. Its ordered top-corner map
leaves only vertical reflection or a quarter-turn, and the latter is
excluded by the actual quarter-turn-pair theorem.
-/

open Set

namespace Puzzling139335.N4Dispatch.TwoOneOne

/-- The reflection in the normalized configuration is a consequence of
the actual dissection and its physical corner pattern. -/
theorem CornerPattern.configuration {d : SquareDissection}
    (h : CornerPattern d) (hc : d.HasProtectedCenter) :
    N4TwoOneOne.Configuration d := by
  have htype := singleton_types_eq d hc h.four_incidences
    h.bottom_left h.bottom_right h.top_right h.top_left
    h.count_zero h.count_one h.count_two
  have hS := d.relativePlacement_preserves_square_of_unique_corner
    (d.unique_corner_owner_of_four_incidences h.four_incidences h.top_right) htype
  refine ⟨h.bottom_left, h.bottom_right, h.top_right, h.top_left, ?_, ?_, ?_, ?_⟩
  · intro k hk
    exact corner_index_eq_of_count_one d h.count_one hk h.top_right
  · intro k hk
    exact corner_index_eq_of_count_one d h.count_two hk h.top_left
  · exact N5.no_corner_of_count_zero d 3 h.count_three
  · exact vertical_image_of_top_corner_pair d hc (by decide : (1 : Fin 4) ≠ 2)
      (d.relativePlacement 1 2) (d.relativePlacement_image 1 2) hS.subset
      (d.relativePlacement_corner htype)

/-- The degree pattern `(2,1,1,0)` produces the normalized actual
configuration used by the analytic `2110` obstruction. -/
theorem exists_configuration_of_degree2110 (d : SquareDissection)
    (hc : d.HasProtectedCenter)
    (h0 : d.tileCornerCount 0 = 2) (h1 : d.tileCornerCount 1 = 1)
    (h2 : d.tileCornerCount 2 = 1) (h3 : d.tileCornerCount 3 = 0) :
    ∃ D : SquareDissection, D.HasProtectedCenter ∧ N4TwoOneOne.Configuration D := by
  obtain ⟨D, hD, hpattern⟩ := exists_cornerPattern_of_degree2110 d hc h0 h1 h2 h3
  exact ⟨D, hD, hpattern.configuration hD⟩

/-- Permutation form for the exhaustive corner-count dispatcher. No
intrinsic-type or geometric normalization premise remains. -/
theorem exists_configuration_of_permuted_degree2110 (d : SquareDissection)
    (hc : d.HasProtectedCenter) (σ : Equiv.Perm (Fin 4))
    (h0 : d.tileCornerCount (σ 0) = 2) (h1 : d.tileCornerCount (σ 1) = 1)
    (h2 : d.tileCornerCount (σ 2) = 1) (h3 : d.tileCornerCount (σ 3) = 0) :
    ∃ D : SquareDissection, D.HasProtectedCenter ∧ N4TwoOneOne.Configuration D :=
  exists_configuration_of_degree2110 (d.reindex σ)
    ((d.reindex_hasProtectedCenter σ).mpr hc) h0 h1 h2 h3

end Puzzling139335.N4Dispatch.TwoOneOne
