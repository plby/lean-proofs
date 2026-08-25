import StackExchange.Puzzling139335.N5.PairTypes
import StackExchange.Puzzling139335.N5.TwoCorner
import StackExchange.Puzzling139335.N8.Pairs

/-!
# Excluding four corner-bearing pieces in the five-incidence case

In the `2111` count pattern, the sole double-corner piece contains the
split corner.  A putative center-owning singleton omits that corner.  The
double and that singleton account for at most three square corners, so
another singleton owns a remaining unique corner.  Its full intrinsic
type must repeat the center-owning singleton's type, which excludes the
center by the actual square-symmetry rigidity theorem.
-/

open Set

namespace Puzzling139335.N5

/-- The `2111` branch cannot protect the center once its double-corner
piece contains the split corner and both owners of that corner exclude
the center.  All corner counts and intrinsic types refer to the actual
dissection placements. -/
theorem not_hasProtectedCenter_of_unique_double_split (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 5)
    (hfull : (fullCornerTypes d).card ≤ 2) {s p : Fin 4}
    (hs : d.cornerTileCount s = 2) (hp : d.tileCornerCount p = 2)
    (hother : ∀ i, i ≠ p → d.tileCornerCount i = 1)
    (hsp : corner s ∈ d.piece p)
    (hcenter : ∀ i, corner s ∈ d.piece i →
      squareCenter ∉ interior (d.piece i)) : ¬ d.HasProtectedCenter := by
  classical
  rintro ⟨i, hicenter⟩
  have his : corner s ∉ d.piece i := fun hi => hcenter i hi hicenter
  have hip : i ≠ p := by
    intro h
    apply his
    simpa only [h] using hsp
  have hi : d.tileCornerCount i = 1 := hother i hip
  obtain ⟨a, ha⟩ := Finset.card_pos.mp
    (show 0 < (N8.cornerSet d i).card by rw [N8.cornerSet_card, hi]; decide)
  have hai : corner a ∈ d.piece i := (N8.mem_cornerSet d i a).mp ha
  have has : a ≠ s := by
    intro h
    exact his (h ▸ hai)
  have hafull : d.intrinsicCorner i a ∈ fullCornerTypes d :=
    (mem_fullCornerTypes d).mpr
      ⟨i, a, hai, count_one_of_ne_split d hN hs has, rfl⟩
  obtain ⟨b, hb, hbs⟩ := Finset.exists_mem_ne
    (show 1 < (N8.cornerSet d p).card by rw [N8.cornerSet_card, hp]; decide) s
  have hbp : corner b ∈ d.piece p := (N8.mem_cornerSet d p b).mp hb
  have hbfull : d.intrinsicCorner p b ∈ fullCornerTypes d :=
    (mem_fullCornerTypes d).mpr
      ⟨p, b, hbp, count_one_of_ne_split d hN hs hbs, rfl⟩
  have hcard : (N8.cornerSet d p ∪ N8.cornerSet d i).card <
      (Finset.univ : Finset (Fin 4)).card := by
    have hle := Finset.card_union_le (N8.cornerSet d p) (N8.cornerSet d i)
    rw [N8.cornerSet_card, N8.cornerSet_card, hp, hi] at hle
    have hfour : (Finset.univ : Finset (Fin 4)).card = 4 := by decide
    rw [hfour]
    omega
  obtain ⟨c, _, hcnot⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  have hcp : corner c ∉ d.piece p := by
    intro hc
    exact hcnot (Finset.mem_union_left _ ((N8.mem_cornerSet d p c).mpr hc))
  have hci : corner c ∉ d.piece i := by
    intro hc
    exact hcnot (Finset.mem_union_right _ ((N8.mem_cornerSet d i c).mpr hc))
  obtain ⟨k, hck⟩ := d.exists_piece_mem (corner_mem_unitSquare c)
  have hkp : k ≠ p := by
    intro h
    apply hcp
    simpa only [h] using hck
  have hki : k ≠ i := by
    intro h
    apply hci
    simpa only [h] using hck
  have hk : d.tileCornerCount k = 1 := hother k hkp
  have hcs : c ≠ s := by
    intro h
    apply hcp
    simpa only [h] using hsp
  have hcfull : d.intrinsicCorner k c ∈ fullCornerTypes d :=
    (mem_fullCornerTypes d).mpr
      ⟨k, c, hck, count_one_of_ne_split d hN hs hcs, rfl⟩
  have htype := equal_full_types_of_count_ne_third d hfull
    hafull hcfull hbfull (by omega) (by omega)
  exact (d.center_not_mem_of_repeated_unique_corner hki.symm
    (unique_corner_of_type_mem_full d hafull) htype).1 hicenter

/-- The actual incidence patterns leave a cornerless piece when every
double-corner piece contains the split corner and the split owners exclude
the center. -/
theorem exists_cornerless_of_double_contains_split (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 5)
    (htypes : d.usedCornerTypes.card ≤ 3) {s : Fin 4}
    (hs : d.cornerTileCount s = 2)
    (hdouble : ∀ i, d.tileCornerCount i = 2 → corner s ∈ d.piece i)
    (hcenter : ∀ i, corner s ∈ d.piece i →
      squareCenter ∉ interior (d.piece i)) :
    ∃ i, d.tileCornerCount i = 0 := by
  obtain ⟨σ, hpattern⟩ := tile_count_patterns d hc hN
  rcases hpattern with h | h
  · have hother : ∀ i, i ≠ σ 0 → d.tileCornerCount i = 1 := by
      intro i hi
      obtain ⟨j, rfl⟩ := σ.surjective i
      fin_cases j
      · exact False.elim (hi rfl)
      · exact h.2.1
      · exact h.2.2.1
      · exact h.2.2.2
    exact False.elim (not_hasProtectedCenter_of_unique_double_split d hN
      (type_cardinalities_of_five d hc hN htypes).1.le hs h.1 hother
      (hdouble (σ 0) h.1) hcenter hc)
  · exact ⟨σ 3, h.2.2.2⟩

/-- A forty-five-degree support at the shared intrinsic type forces the
five-incidence dissection into the branch with a cornerless piece.  The
double-corner membership premise is supplied by the actual support
geometry, rather than by an additional incidence assumption. -/
theorem exists_cornerless_of_split_support (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 5)
    (htypes : d.usedCornerTypes.card ≤ 3) {s : Fin 4} {A : Plane}
    (hs : d.cornerTileCount s = 2) (hA : A ∈ splitCornerTypes d)
    (h45 : AcuteCorner.Supports45 (d.piece 0) A)
    (hcenter : ∀ i, corner s ∈ d.piece i →
      squareCenter ∉ interior (d.piece i)) :
    ∃ i, d.tileCornerCount i = 0 :=
  exists_cornerless_of_double_contains_split d hc hN htypes hs
    (double_contains_split_of_support45 d hc hN hs hA h45) hcenter

end Puzzling139335.N5
