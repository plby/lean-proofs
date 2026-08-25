import StackExchange.Puzzling139335.N8.PairCounting
import StackExchange.Puzzling139335.N8.Geometric

/-!
# Excluding eight corner incidences with at most three intrinsic types

All assumptions about pair counts, repeated placements, and actual side
ownership are derived from the square dissection. The proof applies to
arbitrary closed Jordan regions, without polygonality or null boundaries.
-/

open Set

namespace Puzzling139335.SquareDissection

open N8

/-- The extremal eight-incidence case cannot protect the center when there
are at most three used intrinsic square-corner types. -/
theorem not_hasProtectedCenter_of_eight_incidences_of_le_three_types
    (d : SquareDissection) (hN : d.cornerIncidenceCount = 8)
    (hTypes : d.usedCornerTypes.card ≤ 3) : ¬ d.HasProtectedCenter := by
  classical
  intro hc
  have hcount := d.tileCornerCount_eq_two_of_eight_incidences hc hN
  obtain ⟨s, hs⟩ := exists_side_assignment d hc hcount
  obtain ⟨center, hcenter⟩ := hc
  obtain ⟨a, b, c, hab, hac, hbc, htypes, habpair, hbcpair, hcapair⟩ :=
    exists_three_types_and_all_pairs d.usedCornerTypes (intrinsicPair d) center
      hTypes (fun i => (intrinsicPair_card d i).trans (hcount i))
      (intrinsicPair_subset_usedCornerTypes d)
      (center_pair_unique d hs hcenter) (no_three_equal_pairs d ⟨center, hcenter⟩ hs)
  have hunitab : UnitPairs.IsUnitSidePair (d.piece 0) a b := by
    obtain ⟨i, hi⟩ := habpair
    exact isUnitSidePair_of_pair_eq d hs hab hi
  have hunitbc : UnitPairs.IsUnitSidePair (d.piece 0) b c := by
    obtain ⟨i, hi⟩ := hbcpair
    exact isUnitSidePair_of_pair_eq d hs hbc hi
  have hunitca : UnitPairs.IsUnitSidePair (d.piece 0) c a := by
    obtain ⟨i, hi⟩ := hcapair
    exact isUnitSidePair_of_pair_eq d hs (Ne.symm hac) hi
  exact no_dissection_of_three_side_pairs d hs htypes hunitab hunitbc hunitca
    habpair hbcpair hcapair

end Puzzling139335.SquareDissection
