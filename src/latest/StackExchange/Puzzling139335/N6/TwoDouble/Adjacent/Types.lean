import StackExchange.Puzzling139335.N6.TwoDouble.Adjacent.Types.Counting
import StackExchange.Puzzling139335.N6.TwoDouble.SingleSplit
import StackExchange.Puzzling139335.AcuteCorner

/-!
# The acute type in a singleton of the adjacent configuration

The exact corner table gives one full intrinsic type and two split types.
If both top-left copies omitted the bottom-right type, they would use the
same other split type. Their actual double-corner germ would then support
that type in a forty-five-degree cone. The source's two square corners
force it to be one of the source endpoints, contradicting either the
omission or the separation of full and split types.
-/

open Set

namespace Puzzling139335.N6.TwoDouble.Adjacent

theorem NormalizedCornerData.hasTwoDoubleCorners {d : SquareDissection}
    (h : NormalizedCornerData d) : HasTwoDoubleCorners d := by
  refine ⟨1, 3, by decide, h.corner_count_one, h.corner_count_three, ?_⟩
  intro j hj1 hj3
  fin_cases j
  · exact h.corner_count_zero
  · exact (hj1 rfl).elim
  · exact h.corner_count_two
  · exact (hj3 rfl).elim

theorem NormalizedCornerData.full_type_zero {d : SquareDissection}
    (h : NormalizedCornerData d) : d.intrinsicCorner 0 0 ∈ N5.fullCornerTypes d := by
  exact (N5.mem_fullCornerTypes d).mpr
    ⟨0, 0, (h.corner_zero_iff 0).mpr rfl, h.corner_count_zero, rfl⟩

theorem NormalizedCornerData.full_support_zero {d : SquareDissection}
    (h : NormalizedCornerData d) :
    UnitPairs.IsFullSquareCorner (d.piece 0) (d.intrinsicCorner 0 0) :=
  N5.isFullSquareCorner_of_mem_fullCornerTypes d h.full_type_zero

theorem NormalizedCornerData.split_type_one {d : SquareDissection}
    (h : NormalizedCornerData d) : d.intrinsicCorner 0 1 ∈ N5.splitCornerTypes d := by
  exact (N5.mem_splitCornerTypes d).mpr
    ⟨0, 1, (h.corner_one_iff 0).mpr (Or.inl rfl), by rw [h.corner_count_one]; decide, rfl⟩

theorem NormalizedCornerData.split_type_three {d : SquareDissection}
    (h : NormalizedCornerData d) (i : Fin 4) (hi : i = 2 ∨ i = 3) :
    d.intrinsicCorner i 3 ∈ N5.splitCornerTypes d := by
  exact (N5.mem_splitCornerTypes d).mpr
    ⟨i, 3, (h.corner_three_iff i).mpr hi, by rw [h.corner_count_three]; decide, rfl⟩

private theorem eq_of_mem_two_of_ne {S : Finset Plane} {a b c : Plane}
    (hcard : S.card = 2) (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S)
    (hba : b ≠ a) (hca : c ≠ a) : b = c := by
  classical
  have hrem : (S.erase a).card = 1 := by
    rw [Finset.card_erase_of_mem ha, hcard]
  exact Finset.card_le_one_iff.mp hrem.le
    (Finset.mem_erase.mpr ⟨hba, hb⟩) (Finset.mem_erase.mpr ⟨hca, hc⟩)

/-- At least one top-left singleton uses the intrinsic endpoint that the
two-corner source uses at bottom right. -/
theorem top_left_uses_bottom_right_type_of_corner_data (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hU : d.usedCornerTypes.card ≤ 3)
    (h : NormalizedCornerData d) :
    d.intrinsicCorner 2 3 = d.intrinsicCorner 0 1 ∨
      d.intrinsicCorner 3 3 = d.intrinsicCorner 0 1 := by
  classical
  by_contra hnone
  have h2ne : d.intrinsicCorner 2 3 ≠ d.intrinsicCorner 0 1 :=
    fun heq => hnone (Or.inl heq)
  have h3ne : d.intrinsicCorner 3 3 ≠ d.intrinsicCorner 0 1 :=
    fun heq => hnone (Or.inr heq)
  have hcounts := type_cardinalities d hc hU h.hasTwoDoubleCorners
  have hA := h.split_type_one
  have hB := h.split_type_three 2 (Or.inl rfl)
  have hC := h.split_type_three 3 (Or.inr rfl)
  have hsame : d.intrinsicCorner 2 3 = d.intrinsicCorner 3 3 :=
    eq_of_mem_two_of_ne hcounts.2.1 hA hB hC h2ne h3ne
  have hTL2 : corner 3 ∈ d.piece 2 := (h.corner_three_iff 2).mpr (Or.inl rfl)
  have hTL3 : corner 3 ∈ d.piece 3 := (h.corner_three_iff 3).mpr (Or.inr rfl)
  have hother : ∀ l, l ≠ (2 : Fin 4) → l ≠ 3 → corner 3 ∉ d.piece l := by
    intro l hl2 hl3 hl
    exact ((h.corner_three_iff l).mp hl).elim hl2 hl3
  have hsupport := d.same_intrinsic_double_corner_prototype_support
    (by decide : (2 : Fin 4) ≠ 3) hTL2 hTL3 hother hsame
  have hv : d.intrinsicCorner 2 3 ∈ d.piece 0 :=
    (d.intrinsicCorner_mem_iff 2 3).mpr hTL2
  have hBL : corner 0 ∈ d.piece 0 := (h.corner_zero_iff 0).mpr rfl
  have hBR : corner 1 ∈ d.piece 0 := (h.corner_one_iff 0).mpr (Or.inl rfl)
  have hends := d.support45_preimage_eq_of_two_corners hc 0 0 1 (by decide)
    hBL hBR (d.placement 0) (d.placement_image 0) hv hsupport
  change d.intrinsicCorner 2 3 = d.intrinsicCorner 0 0 ∨
    d.intrinsicCorner 2 3 = d.intrinsicCorner 0 1 at hends
  rcases hends with hfull | hacute
  · exact Finset.disjoint_left.mp (N5.full_split_disjoint d)
      h.full_type_zero (hfull ▸ hB)
  · exact h2ne hacute

/-- The type conclusion under just the actual normalized dissection
assumptions. The corner table and all type cardinalities are derived. -/
theorem top_left_uses_bottom_right_type (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 6)
    (hU : d.usedCornerTypes.card ≤ 3)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hanti : ReflectionSeparation.antiDiagonal '' d.piece 0 = d.piece 1)
    (hTL2 : corner 3 ∈ d.piece 2) (hTL3 : corner 3 ∈ d.piece 3) :
    d.intrinsicCorner 2 3 = d.intrinsicCorner 0 1 ∨
      d.intrinsicCorner 3 3 = d.intrinsicCorner 0 1 :=
  top_left_uses_bottom_right_type_of_corner_data d hc hU
    (normalized_corner_data d hc hN hBL hBR hanti hTL2 hTL3)

end Puzzling139335.N6.TwoDouble.Adjacent
