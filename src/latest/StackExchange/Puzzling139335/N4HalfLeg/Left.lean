import StackExchange.Puzzling139335.N4HalfLeg.Normals
import StackExchange.Puzzling139335.N4HalfLeg.Spans
import StackExchange.Puzzling139335.N4HalfLeg.Packing
import StackExchange.Puzzling139335.N4OuterPair.GapOwnership
import StackExchange.Puzzling139335.N4OuterPair.FullHeightLegs

/-!
# A left outer leg reaching the midline leaves too much right-side gap

The right gap is covered by the two actual middle contacts. If one contact
is a subsingleton, closedness gives the whole gap to the other. Otherwise
their two actual contact spans are packed in the source. The only separate
input is the exclusion of equal actual first matrix rows.
-/

open Set

namespace Puzzling139335.N4HalfLeg

open N4OuterPair SourceFaceBridge PlaneIsometries

private theorem source_subset_lowerHalfSquare {d : SquareDissection}
    (h : Configuration d) : d.piece 0 ⊆ lowerHalfSquare := by
  intro p hp
  exact h.outer_halves.1 hp

/-- A single actual middle owner cannot supply the entire right gap when
the source also has a full left leg. -/
theorem single_gap_owner_false {d : SquareDissection} (h : Configuration d)
    (hc : d.HasProtectedCenter)
    (hleft : Schoenflies.Plane.mk 0 (1 / 2) ∈ d.piece 0)
    {b : ℝ} (hb : b < 1 / 2) (hB : point 1 b ∈ d.piece 0)
    {i : Fin 4} (hi : i = 2 ∨ i = 3)
    (hgap : Icc b (1 - b) ⊆ sideContact d i 1) : False := by
  have hnontriv : (d.piece i ∩ {p : Plane | p 0 = 1}).Nontrivial := by
    refine ⟨Schoenflies.Plane.mk 1 b, ⟨hgap ⟨le_rfl, ?_⟩, rfl⟩,
      Schoenflies.Plane.mk 1 (1 - b), ⟨hgap ⟨?_, le_rfl⟩, rfl⟩, ?_⟩
    · linarith
    · linarith
    · intro heq
      have hy := congrArg (fun p : Plane => p 1) heq
      change b = 1 - b at hy
      linarith
  obtain ⟨e, he⟩ := d.congruent 0 i
  obtain ⟨hc', hs, _⟩ := right_normal_bounds_of_left_halfleg h hc hleft hi e he hnontriv
  obtain ⟨F⟩ := exists_rightSpan e he (d.jordan i).isCompact (d.piece_subset i)
    hnontriv hc' hs
  have hlo := (F.bounds b (hgap ⟨le_rfl, by linarith⟩)).1
  have hhi := (F.bounds (1 - b) (hgap ⟨by linarith, le_rfl⟩)).2
  have hlength : 1 - 2 * b ≤ F.face.length := by
    rw [F.length_eq]
    linarith
  exact F.face.not_length_ge (source_subset_lowerHalfSquare h) hB hb hlength

/-- The left-leg obstruction reduced only to the actual equal-normal
exception. Both row inequalities are about genuine congruences of the
bottom piece onto the two middle pieces. -/
theorem left_halfleg_impossible_of_distinct_rows {d : SquareDissection}
    (h : Configuration d) (hc : d.HasProtectedCenter)
    (hleft : Schoenflies.Plane.mk 0 (1 / 2) ∈ d.piece 0)
    (hrows : ∀ e f : Plane ≃ᵃⁱ[ℝ] Plane,
      e '' d.piece 0 = d.piece 2 → f '' d.piece 0 = d.piece 3 →
      (d.piece 2 ∩ {p : Plane | p 0 = 1}).Nontrivial →
      (d.piece 3 ∩ {p : Plane | p 0 = 1}).Nontrivial →
      (linearMatrix e 0 0, linearMatrix e 0 1) ≠
        (linearMatrix f 0 0, linearMatrix f 0 1)) : False := by
  obtain ⟨b, hb, hcontact⟩ :=
    h.side_contact_interval hc (x := (1 : ℝ)) (Or.inr rfl)
  have hbHalf : b < 1 / 2 := by
    by_contra hnot
    apply h.full_height_legs_impossible hc hleft
    exact (hcontact (1 / 2)).mpr ⟨by norm_num, le_of_not_gt hnot⟩
  have hB : point 1 b ∈ d.piece 0 := by
    simpa only [point, Schoenflies.Plane.mk] using (hcontact b).mpr ⟨hb.1, le_rfl⟩
  have hcover : Icc b (1 - b) ⊆ sideContact d 2 1 ∪ sideContact d 3 1 :=
    h.closed_side_gap_covered (x := (1 : ℝ)) (c := b) (Or.inr rfl)
      hb.1 hbHalf hcontact
  have hinterval : b < 1 - b := by linarith
  rcases (sideContact d 2 1).subsingleton_or_nontrivial with htwo | htwo
  · have hthree : Icc b (1 - b) ⊆ sideContact d 3 1 :=
      closed_interval_subset_of_subsingleton_set (sideContact_isClosed d 3 1)
        (by simpa only [union_comm] using hcover) htwo hinterval
    exact single_gap_owner_false h hc hleft hbHalf hB (Or.inr rfl) hthree
  · rcases (sideContact d 3 1).subsingleton_or_nontrivial with hthree | hthree
    · have htwo' : Icc b (1 - b) ⊆ sideContact d 2 1 :=
        closed_interval_subset_of_subsingleton_set (sideContact_isClosed d 2 1)
          hcover hthree hinterval
      exact single_gap_owner_false h hc hleft hbHalf hB (Or.inl rfl) htwo'
    · have htwo' := sideContact_nontrivial_to_plane htwo
      have hthree' := sideContact_nontrivial_to_plane hthree
      obtain ⟨e, he⟩ := d.congruent 0 2
      obtain ⟨f, hf⟩ := d.congruent 0 3
      obtain ⟨hc₂, hs₂, _⟩ :=
        right_normal_bounds_of_left_halfleg h hc hleft (Or.inl rfl) e he htwo'
      obtain ⟨hc₃, hs₃, _⟩ :=
        right_normal_bounds_of_left_halfleg h hc hleft (Or.inr rfl) f hf hthree'
      obtain ⟨F⟩ := exists_rightSpan e he (d.jordan 2).isCompact (d.piece_subset 2)
        htwo' hc₂ hs₂
      obtain ⟨G⟩ := exists_rightSpan f hf (d.jordan 3).isCompact (d.piece_subset 3)
        hthree' hc₃ hs₃
      have hlength : 1 - 2 * b ≤ F.face.length + G.face.length :=
        F.middle_length_le_add_lengths G hcover
      exact F.face.not_total_length_ge G.face (source_subset_lowerHalfSquare h) hB
        hbHalf (hrows e f he hf htwo' hthree') hlength

end Puzzling139335.N4HalfLeg
