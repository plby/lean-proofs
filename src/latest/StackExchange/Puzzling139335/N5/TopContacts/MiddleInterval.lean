import StackExchange.Puzzling139335.N5.SideExclusion.Normalized
import StackExchange.Puzzling139335.N5.TopContacts.MiddleInterval.Supporting

/-!
# The actual middle top interval belongs exactly to the cornerless piece

The lower outer piece has no top contacts.  Given the initial top interval
of the reflected outer piece and the terminal top interval of the singleton
piece, coverage assigns the intervening open interval to the cornerless
piece.  Closedness supplies its two endpoints.  The actual supporting
segments of the neighboring Jordan pieces exclude every other top contact.
-/

open Set

namespace Puzzling139335.N5

/-- A top contact of the below-diagonal piece would be the top-right
corner, which has a different unique owner. -/
theorem Normalized.top_side_not_mem_zero {d : SquareDissection}
    (h : Normalized d) (x : ℝ) :
    Schoenflies.Plane.mk x 1 ∉ d.piece 0 := by
  intro hx
  have hx1 : x = 1 :=
    le_antisymm (d.piece_subset 0 hx).1.2 (h.below_diagonal hx)
  subst x
  apply h.unique_top_right 0 (by decide)
  simpa [corner, Fin.ext_iff, Schoenflies.Plane.mk] using hx

/-- Two actual neighboring contact intervals determine the whole contact
set of the cornerless piece, including both endpoints and no extra points. -/
theorem Normalized.top_side_mem_three_iff_of_neighbor_intervals
    {d : SquareDissection} (h : Normalized d) {b m : ℝ}
    (hb : 0 < b) (hbm : b < m) (hm : m < 1)
    (hOne : ∀ x : ℝ,
      Schoenflies.Plane.mk x 1 ∈ d.piece 1 ↔ 0 ≤ x ∧ x ≤ b)
    (hTwo : ∀ x : ℝ,
      Schoenflies.Plane.mk x 1 ∈ d.piece 2 ↔ m ≤ x ∧ x ≤ 1) :
    ∀ x : ℝ, Schoenflies.Plane.mk x 1 ∈ d.piece 3 ↔ b ≤ x ∧ x ≤ m := by
  let T : Set ℝ := {x | Schoenflies.Plane.mk x 1 ∈ d.piece 3}
  have hTclosed : IsClosed T := (d.jordan 3).isClosed.preimage (by fun_prop)
  have hmiddle : Ioo b m ⊆ T := by
    intro x hx
    have hxS : Schoenflies.Plane.mk x 1 ∈ unitSquare :=
      ⟨⟨(hb.trans hx.1).le, (hx.2.trans hm).le⟩, by norm_num⟩
    obtain ⟨i, hi⟩ := d.exists_piece_mem hxS
    fin_cases i
    · exact (h.top_side_not_mem_zero x hi).elim
    · exact (not_le_of_gt hx.1 ((hOne x).mp hi).2).elim
    · exact (not_le_of_gt hx.2 ((hTwo x).mp hi).1).elim
    · exact hi
  have hclosed : Icc b m ⊆ T := by
    rw [← closure_Ioo hbm.ne]
    exact closure_minimal hmiddle hTclosed
  have hsegmentOne : segment ℝ (Schoenflies.Plane.mk 0 1)
      (Schoenflies.Plane.mk b 1) ⊆ d.piece 1 :=
    TopContacts.top_segment_subset_of_interval hb.le
      (fun x hx => (hOne x).mpr hx)
  have hsegmentTwo : segment ℝ (Schoenflies.Plane.mk m 1)
      (Schoenflies.Plane.mk 1 1) ⊆ d.piece 2 :=
    TopContacts.top_segment_subset_of_interval hm.le
      (fun x hx => (hTwo x).mpr hx)
  intro x
  constructor
  · intro hx
    have hx0 : 0 < x := (h.piece_three_coordinates_pos hx).1
    have hx1 : x < 1 := lt_of_le_of_ne (d.piece_subset 3 hx).1.2 (by
      intro heq
      apply h.unique_top_right 3 (by decide)
      simpa [heq, corner, Fin.ext_iff, Schoenflies.Plane.mk] using hx)
    constructor
    · by_contra hxb
      have hxb' : x < b := lt_of_not_ge hxb
      exact TopContacts.top_open_not_mem_of_segment d
        (by decide : (1 : Fin 4) ≠ 3) hb hsegmentOne hx0 hxb' hx
    · by_contra hmx
      have hmx' : m < x := lt_of_not_ge hmx
      exact TopContacts.top_open_not_mem_of_segment d
        (by decide : (2 : Fin 4) ≠ 3) hm hsegmentTwo hmx' hx1 hx
  · intro hx
    exact hclosed hx

end Puzzling139335.N5
