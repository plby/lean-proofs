import StackExchange.Puzzling139335.N6.Enumeration
import StackExchange.Puzzling139335.N6.TwoDouble.SingleSplit
import StackExchange.Puzzling139335.N6.TwoDouble.Normalization.Transport
import StackExchange.Puzzling139335.N6.TwoDouble.Normalization.CanonicalMaps
import StackExchange.Puzzling139335.N7.FullPairNormalization.Frame
import StackExchange.Puzzling139335.N5.Transport
import StackExchange.Puzzling139335.GeometricReduction

/-!
# Canonical normalization of the actual full-corner pair

The original two-double-corner dissection supplies two occurrences of the
same full intrinsic corner and its unit partner. A genuine square symmetry
puts the ordered pair at the bottom side, and a permutation puts its two
copies first. The relative congruence is conjugated into this frame.

The resulting dissection retains its protected center, six incidences,
two-double-corner pattern, and uniquely owned bottom-left corner. Its
intrinsic type bound is proved anew, rather than transported across the
independent choices of prototype placements.
-/

open Set

namespace Puzzling139335.N6.TwoDouble

noncomputable section

/-- Normalize the actual full-corner pair, with no canonical-shape or
canonical-type premise on the original dissection. -/
theorem exists_canonical_full_pair (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (hD : HasTwoDoubleCorners d) :
    ∃ D : SquareDissection, D.HasProtectedCenter ∧ D.cornerIncidenceCount = 6 ∧
      D.usedCornerTypes.card ≤ 3 ∧ HasTwoDoubleCorners D ∧
      corner 0 ∈ D.piece 0 ∧ corner 1 ∈ D.piece 0 ∧ D.cornerTileCount 0 = 1 ∧
      (ReflectionSeparation.horizontal '' D.piece 0 = D.piece 1 ∨
        ReflectionSeparation.antiDiagonal '' D.piece 0 = D.piece 1 ∨
        AffineIsometryEquiv.pointReflection ℝ squareCenter '' D.piece 0 = D.piece 1) := by
  classical
  have hU := d.usedCornerTypes_card_le_three hc
  obtain ⟨i, j, a, b, hij, _, ha, hb, hca, hcb, htype, v, hrv, _, _, hipair,
    _, hS, _, _⟩ := exists_actual_full_pair_with_unique d hc hN hU hD
  have hcount : d.tileCornerCount i = 2 := by
    rw [← N8.intrinsicPair_card, hipair, Finset.card_pair hrv]
  obtain ⟨q, hq, hqr, hqv⟩ := N7.FullPairNormalization.exists_ordered_pair_frame d hc i
    hcount (d.intrinsicCorner i a) v hrv hipair
  have hqa : q (corner a) = corner 0 := by
    simpa only [d.placement_intrinsicCorner] using hqr
  obtain ⟨σ, hσ0, hσ1⟩ := extend_two_indices i j hij
  let D : SquareDissection := (d.map q hq).reindex σ
  have hDpiece (k : Fin 4) : D.piece k = q '' d.piece (σ k) := rfl
  have hcD : D.HasProtectedCenter :=
    ((d.map q hq).reindex_hasProtectedCenter σ).mpr ((d.map_hasProtectedCenter q hq).mpr hc)
  have hND : D.cornerIncidenceCount = 6 := by
    change ((d.map q hq).reindex σ).cornerIncidenceCount = 6
    rw [SquareDissection.reindex_cornerIncidenceCount, N5.cornerIncidenceCount_map, hN]
  have hUD : D.usedCornerTypes.card ≤ 3 := D.usedCornerTypes_card_le_three hcD
  have hDD : HasTwoDoubleCorners D :=
    hasTwoDoubleCorners_reindex (d.map q hq) σ (hasTwoDoubleCorners_map d q hq hD)
  have hBL : corner 0 ∈ D.piece 0 := by
    rw [hDpiece, hσ0]
    exact ⟨corner a, ha, hqa⟩
  have hvP : v ∈ d.piece 0 := by
    apply d.usedCornerTypes_subset
    apply N8.intrinsicPair_subset_usedCornerTypes d i
    rw [hipair]
    simp
  have hvi : d.placement i v ∈ d.piece i := by
    rw [← d.placement_image i]
    exact mem_image_of_mem _ hvP
  have hBR : corner 1 ∈ D.piece 0 := by
    rw [hDpiece, hσ0]
    exact ⟨d.placement i v, hvi, hqv⟩
  have hzeroCount : D.cornerTileCount 0 = 1 := by
    change ((d.map q hq).reindex σ).cornerTileCount 0 = 1
    rw [SquareDissection.reindex_cornerTileCount,
      N7.FullPairNormalization.cornerTileCount_map_of_corner_image d q hq hqa, hca]
  let g := frameConjugate q (d.relativePlacement i j)
  have hg : g '' D.piece 0 = D.piece 1 := by
    rw [hDpiece, hDpiece, hσ0, hσ1]
    change frameConjugate q (d.relativePlacement i j) '' (q '' d.piece i) = q '' d.piece j
    rw [frameConjugate_image, d.relativePlacement_image]
  have hgS : g '' unitSquare = unitSquare := frameConjugate_preserves_square q _ hq hS
  have hg0 : g (corner 0) = q (corner b) := by
    calc
      _ = g (q (corner a)) := by rw [hqa]
      _ = q (d.relativePlacement i j (corner a)) := frameConjugate_apply_image q _ _
      _ = q (corner b) := by rw [d.relativePlacement_corner htype]
  have havoid : g (corner 0) ∉ D.piece 0 := by
    rw [hg0, hDpiece, hσ0]
    rintro ⟨p, hp, hpeq⟩
    have hpEq : p = corner b := q.injective hpeq
    have hbi : corner b ∈ d.piece i := hpEq ▸ hp
    exact N5.unique_corner_of_count_one d hcb hb i hij hbi
  exact ⟨D, hcD, hND, hUD, hDD, hBL, hBR, hzeroCount,
    canonical_square_pair_image_cases D hcD g hg hgS hBL hBR havoid⟩

end

end Puzzling139335.N6.TwoDouble
