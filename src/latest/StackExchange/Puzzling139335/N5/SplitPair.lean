import StackExchange.Puzzling139335.N5.TwoCorner
import StackExchange.Puzzling139335.N5.PairTypes

/-!
# The two double-corner tiles use one intrinsic side pair

This reduction uses actual incidences, the diameter obstruction, and
invariance of corner counts under repeated full-type placements.  It
identifies the remaining singleton with the opposite physical corner.
-/

open Set

namespace Puzzling139335.N5

theorem split_membership_iff_of_two_owners (d : SquareDissection)
    {s p q : Fin 4} (hs : d.cornerTileCount s = 2) (hpq : p ≠ q)
    (hp : corner s ∈ d.piece p) (hq : corner s ∈ d.piece q) (k : Fin 4) :
    corner s ∈ d.piece k ↔ k = p ∨ k = q := by
  classical
  constructor
  · intro hk
    by_cases hkp : k = p
    · exact Or.inl hkp
    by_cases hkq : k = q
    · exact Or.inr hkq
    have hcard : (Finset.univ.filter fun i => corner s ∈ d.piece i).card ≤ 2 := hs.le
    have heq : p = k := eq_of_mem_two_type_set hcard
      (by simp [hp]) (by simp [hk]) (by simp [hq]) hpq hkq
    exact (hkp heq.symm).elim
  · rintro (rfl | rfl)
    · exact hp
    · exact hq

private theorem adjacent_cases {s a : Fin 4} (hne : a ≠ s) (hopp : a ≠ s + 2) :
    a = s + 1 ∨ a = s + 3 := by
  fin_cases s <;> fin_cases a <;> simp_all

private theorem adjacent_order {s a b : Fin 4}
    (ha : a = s + 1 ∨ a = s + 3) (hb : b = s + 1 ∨ b = s + 3)
    (hab : a ≠ b) :
    (a = s + 1 ∧ b = s + 3) ∨ (a = s + 3 ∧ b = s + 1) := by
  rcases ha with ha | ha <;> rcases hb with hb | hb
  · exact (hab (ha.trans hb.symm)).elim
  · exact Or.inl ⟨ha, hb⟩
  · exact Or.inr ⟨ha, hb⟩
  · exact (hab (ha.trans hb.symm)).elim

private theorem remaining_corner {s a b c : Fin 4}
    (horder : (a = s + 1 ∧ b = s + 3) ∨ (a = s + 3 ∧ b = s + 1))
    (hcs : c ≠ s) (hca : c ≠ a) (hcb : c ≠ b) : c = s + 2 := by
  rcases horder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
    fin_cases s <;> fin_cases c <;> simp_all

/-- Two distinct double-corner tiles meeting at the unique split corner
occupy its two neighboring corners and use the same second intrinsic
point.  A singleton tile occupies the opposite corner. -/
theorem two_double_tiles_share_pair (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 5)
    (htypes : d.usedCornerTypes.card ≤ 3) {s p q r : Fin 4}
    (hs : d.cornerTileCount s = 2) (hpq : p ≠ q)
    (hpcount : d.tileCornerCount p = 2) (hqcount : d.tileCornerCount q = 2)
    (hrcount : d.tileCornerCount r = 1)
    (hsp : corner s ∈ d.piece p) (hsq : corner s ∈ d.piece q) :
    ∃ a b : Fin 4,
      ((a = s + 1 ∧ b = s + 3) ∨ (a = s + 3 ∧ b = s + 1)) ∧
      corner a ∈ d.piece p ∧ corner b ∈ d.piece q ∧
      corner (s + 2) ∈ d.piece r ∧
      d.intrinsicCorner p s = d.intrinsicCorner q s ∧
      d.intrinsicCorner p a = d.intrinsicCorner q b := by
  classical
  obtain ⟨a, has, hpa⟩ := second_corner_of_count_two d p s hpcount hsp
  obtain ⟨b, hbs, hqb⟩ := second_corner_of_count_two d q s hqcount hsq
  have hrpos : (Finset.univ.filter fun c => corner c ∈ d.piece r).Nonempty := by
    apply Finset.card_pos.mp
    change 0 < d.tileCornerCount r
    omega
  obtain ⟨c, hcMem⟩ := hrpos
  have hrc : corner c ∈ d.piece r := (Finset.mem_filter.mp hcMem).2
  have hrp : r ≠ p := by intro h; subst r; omega
  have hrq : r ≠ q := by intro h; subst r; omega
  have hcs : c ≠ s := by
    intro h
    have hsr : corner s ∈ d.piece r := h ▸ hrc
    rcases (split_membership_iff_of_two_owners d hs hpq hsp hsq r).mp hsr with h | h
    · exact hrp h
    · exact hrq h
  have haCount := count_one_of_ne_split d hN hs has
  have hbCount := count_one_of_ne_split d hN hs hbs
  have hcCount := count_one_of_ne_split d hN hs hcs
  have haUnique := unique_corner_of_count_one d haCount hpa
  have hbUnique := unique_corner_of_count_one d hbCount hqb
  have hab : a ≠ b := by
    intro h
    exact haUnique q hpq.symm (by simpa only [h] using hqb)
  have hca : c ≠ a := by
    intro h
    exact haUnique r hrp (h ▸ hrc)
  have hcb : c ≠ b := by
    intro h
    exact hbUnique r hrq (h ▸ hrc)
  have haOpp : a ≠ s + 2 := by
    intro h
    exact d.no_opposite_corners hc p s ⟨hsp, h ▸ hpa⟩
  have hbOpp : b ≠ s + 2 := by
    intro h
    exact d.no_opposite_corners hc q s ⟨hsq, h ▸ hqb⟩
  have horder := adjacent_order (adjacent_cases has haOpp) (adjacent_cases hbs hbOpp) hab
  have hcOpp := remaining_corner horder hcs hca hcb
  refine ⟨a, b, horder, hpa, hqb, hcOpp ▸ hrc,
    intrinsicCorners_eq_at_split d hc hN htypes hs hsp hsq, ?_⟩
  exact double_tiles_full_types_equal d hc hN htypes hpcount hqcount hrcount
    hpa hqb hrc haCount hbCount hcCount

end Puzzling139335.N5
