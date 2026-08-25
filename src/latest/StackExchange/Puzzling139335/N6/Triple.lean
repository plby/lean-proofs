import StackExchange.Puzzling139335.N6.Enumeration
import StackExchange.Puzzling139335.N6.TripleNormalized
import StackExchange.Puzzling139335.N6.TripleStraight
import StackExchange.Puzzling139335.N6.TripleSectors.Normalization
import StackExchange.Puzzling139335.N5.Transport
import StackExchange.Puzzling139335.N4Dispatch.FiniteRouting

/-!
# Exclusion of the triple-corner six-incidence case

The original dissection determines its intrinsic types and its two
straight boundary branches. Actual local sector trisection determines the
two possible outer parities. A common square symmetry and a permutation
of the four actual pieces then put it into one of the two proved
normalized obstructions.
-/

open Set

namespace Puzzling139335.N6

open TripleSectors

noncomputable section

/-- A six-incidence dissection with a three-way square corner cannot have
a piece containing a neighborhood of the square center. -/
theorem triple_corner_impossible (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hN : d.cornerIncidenceCount = 6) {s : Fin 4} (hs : d.cornerTileCount s = 3) :
    False := by
  obtain ⟨i, hi⟩ := d.exists_piece_mem (corner_mem_unitSquare s)
  have hcommon : ∀ j, corner s ∈ d.piece j →
      d.intrinsicCorner j s = d.intrinsicCorner i s := by
    intro j hj
    exact intrinsicCorners_eq_at_triple d hc hN
      (d.usedCornerTypes_card_le_three hc) hs hj hi
  obtain ⟨f, hf, howners, hmiddle, hlast, hcone, _⟩ :=
    exists_actual_ordered_cone d s (d.intrinsicCorner i s) hs hcommon
  obtain ⟨σ, hσ0, hσ1, hσ2⟩ := extend_three_indices f hf
  let q := SquareSymmetry.cornerFlip s
  have hq : q '' unitSquare = unitSquare := SquareSymmetry.cornerFlip_image_unitSquare s
  let D : SquareDissection := (d.map q hq).reindex σ
  have hDpiece (k : Fin 4) : D.piece k = cornerPiece d s (σ k) := rfl
  have hcD : D.HasProtectedCenter :=
    ((d.map q hq).reindex_hasProtectedCenter σ).mpr ((d.map_hasProtectedCenter q hq).mpr hc)
  have hND : D.cornerIncidenceCount = 6 := by
    change ((d.map q hq).reindex σ).cornerIncidenceCount = 6
    rw [SquareDissection.reindex_cornerIncidenceCount, N5.cornerIncidenceCount_map, hN]
  have hzero : (0 : Plane) ∈ D.piece 0 := by
    rw [hDpiece, hσ0]
    exact (zero_mem_cornerFlip_image_iff s (d.piece (f 0))).mpr
      ((howners (f 0)).mpr ⟨0, rfl⟩)
  have hconeD : D.piece 0 ⊆ thirtyCone := by
    rw [hDpiece, hσ0]
    exact hcone
  have hmiddleD : D.piece 1 = rotateThirty '' D.piece 0 ∨
      D.piece 1 = reflectThirty '' D.piece 0 := by
    rw [hDpiece, hDpiece, hσ0, hσ1]
    exact hmiddle
  have hlastD : D.piece 2 = rotateSixty '' D.piece 0 ∨
      D.piece 2 = ReflectionSeparation.diagonal '' D.piece 0 := by
    rw [hDpiece, hDpiece, hσ0, hσ2]
    exact hlast
  rcases hlastD with hdirect | hreflected
  · exact TripleEqualParity.normalized_equal_parity_impossible D hdirect hmiddleD
  · exact normalized_opposite_parity_impossible D hcD hND hzero hconeD hmiddleD hreflected

theorem not_hasProtectedCenter_of_triple_corner (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 6) (htriple : HasTripleCorner d) :
    ¬ d.HasProtectedCenter := by
  intro hc
  obtain ⟨s, hs, _⟩ := htriple
  exact triple_corner_impossible d hc hN hs

end

end Puzzling139335.N6
