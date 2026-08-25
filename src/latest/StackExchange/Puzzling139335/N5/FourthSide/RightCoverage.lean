import StackExchange.Puzzling139335.N5.Normalized
import StackExchange.Puzzling139335.N4TwoOneOne.BoundaryIntervals

/-!
# The actual terminal right-side interval of the singleton piece

The reflected outer piece has no right-side contacts. If the cornerless piece has at most
one such contact, the actual Jordan side-cutoff theorem partitions the right side between
the bottom piece and the top-right singleton piece. No protected-center hypothesis is
needed for this conclusion.
-/

open Set

namespace Puzzling139335.N5.FourthSide

open N4TwoOneOne.BoundaryIntervals

variable {d : SquareDissection}

/-- Reflection in the diagonal puts the second outer piece above that diagonal. Its only
possible right-side point would be the uniquely owned top-right corner. -/
theorem reflected_piece_misses_right (h : Normalized d) (y : ℝ) :
    Schoenflies.Plane.mk 1 y ∉ d.piece 1 := by
  intro hy
  have habove : d.piece 1 ⊆ {p | p 0 ≤ p 1} := by
    intro p hp
    rw [← h.diagonal_image] at hp
    obtain ⟨q, hq, rfl⟩ := hp
    change q 1 ≤ q 0
    exact h.below_diagonal hq
  have hy1 : y = 1 := le_antisymm (d.piece_subset 1 hy).2.2 (habove hy)
  subst y
  apply h.unique_top_right 1 (by decide)
  simpa [corner, Fin.ext_iff, Schoenflies.Plane.mk] using hy

/-- An exact terminal contact interval contains the corresponding actual straight segment. -/
theorem right_segment_subset_of_contact_interval {P : Set Plane} {b : ℝ}
    (hb : b ≤ 1)
    (hmem : ∀ y : ℝ, Schoenflies.Plane.mk 1 y ∈ P ↔ b ≤ y ∧ y ≤ 1) :
    segment ℝ (Schoenflies.Plane.mk 1 b) (corner 2) ⊆ P := by
  have htop : corner 2 = Schoenflies.Plane.mk 1 1 := by
    simp [corner, Fin.ext_iff, Schoenflies.Plane.mk]
  rw [htop]
  intro p hp
  rw [Schoenflies.mem_segment_vert, segment_eq_Icc hb] at hp
  have heq : p = Schoenflies.Plane.mk 1 (p 1) := by
    ext i
    fin_cases i
    · exact hp.1
    · rfl
  rw [heq]
  exact (hmem (p 1)).mpr hp.2

/-- A singleton exceptional contact leaves the whole right side partitioned into one
initial interval of piece 0 and one terminal interval of piece 2, with a common endpoint. -/
theorem exists_right_contact_partition (h : Normalized d)
    (hD : (d.piece 3 ∩ {p : Plane | p 0 = 1}).Subsingleton) :
    ∃ b : ℝ, 0 < b ∧ b < 1 ∧
      (∀ y : ℝ, Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ 0 ≤ y ∧ y ≤ b) ∧
      (∀ y : ℝ, Schoenflies.Plane.mk 1 y ∈ d.piece 2 ↔ b ≤ y ∧ y ≤ 1) ∧
      segment ℝ (Schoenflies.Plane.mk 1 b) (corner 2) ⊆ d.piece 2 := by
  have hBR_unique : ∀ k, k ≠ 0 → corner 1 ∉ d.piece k :=
    unique_corner_of_count_one d
      (count_one_of_ne_split d h.incidence_count h.split_count (by decide)) h.bottom_right
  have h0P : sidePoint 1 0 ∈ d.piece 0 := by
    simpa [corner, Fin.ext_iff, Schoenflies.Plane.mk] using h.bottom_right
  have h0R : sidePoint 1 0 ∉ d.piece 2 := by
    simpa [corner, Fin.ext_iff, Schoenflies.Plane.mk] using hBR_unique 2 (by decide)
  have h1P : sidePoint 1 1 ∉ d.piece 0 := by
    simpa [corner, Fin.ext_iff, Schoenflies.Plane.mk] using
      h.unique_top_right 0 (by decide)
  have h1R : sidePoint 1 1 ∈ d.piece 2 := by
    simpa [corner, Fin.ext_iff, Schoenflies.Plane.mk] using h.top_right
  have hD_side : (d.piece 3 ∩ sidePoint 1 '' Icc (0 : ℝ) 1).Subsingleton := by
    intro p hp q hq
    have hp_right : p 0 = 1 := by
      rcases hp.2 with ⟨t, _ht, rfl⟩
      rfl
    have hq_right : q 0 = 1 := by
      rcases hq.2 with ⟨t, _ht, rfl⟩
      rfl
    exact hD ⟨hp.1, hp_right⟩ ⟨hq.1, hq_right⟩
  have hcover : ∀ y ∈ Icc (0 : ℝ) 1,
      sidePoint 1 y ∈ d.piece 0 ∨ sidePoint 1 y ∈ d.piece 2 ∨
        sidePoint 1 y ∈ d.piece 3 := by
    intro y hy
    obtain ⟨i, hi⟩ := d.exists_piece_mem (sidePoint_mem_unitSquare 1 hy)
    fin_cases i
    · exact Or.inl hi
    · change Schoenflies.Plane.mk 1 y ∈ d.piece 1 at hi
      exact (reflected_piece_misses_right h y hi).elim
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
  obtain ⟨b, hb, hcut⟩ := exists_side_cutoff_of_subsingleton_contact 1
    (d.jordan 0) (d.jordan 2) (d.piece_subset 0) (d.piece_subset 2)
    (d.disjoint_interiors (by decide : (0 : Fin 4) ≠ 2)) h0P h0R h1P h1R hD_side hcover
  have hP_interval : ∀ y : ℝ,
      Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ 0 ≤ y ∧ y ≤ b := by
    intro y
    constructor
    · intro hy
      have hy01 : y ∈ Icc (0 : ℝ) 1 := (d.piece_subset 0 hy).2
      exact ⟨hy01.1, (hcut y hy01).1.mp (by simpa only [sidePoint_one] using hy)⟩
    · rintro ⟨hy0, hyb⟩
      simpa only [sidePoint_one] using
        (hcut y ⟨hy0, hyb.trans hb.2.le⟩).1.mpr hyb
  have hR_interval : ∀ y : ℝ,
      Schoenflies.Plane.mk 1 y ∈ d.piece 2 ↔ b ≤ y ∧ y ≤ 1 := by
    intro y
    constructor
    · intro hy
      have hy01 : y ∈ Icc (0 : ℝ) 1 := (d.piece_subset 2 hy).2
      exact ⟨(hcut y hy01).2.mp (by simpa only [sidePoint_one] using hy), hy01.2⟩
    · rintro ⟨hby, hy1⟩
      simpa only [sidePoint_one] using
        (hcut y ⟨hb.1.le.trans hby, hy1⟩).2.mpr hby
  exact ⟨b, hb.1, hb.2, hP_interval, hR_interval,
    right_segment_subset_of_contact_interval hb.2.le hR_interval⟩

/-- Any already specified initial contact parameter agrees with the actual cutoff, so
the singleton piece has precisely the complementary terminal contact interval. -/
theorem right_contact_iff_of_initial_interval (h : Normalized d)
    (hD : (d.piece 3 ∩ {p : Plane | p 0 = 1}).Subsingleton)
    {b : ℝ} (hb : 0 < b)
    (hP_interval : ∀ y : ℝ,
      Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ 0 ≤ y ∧ y ≤ b) :
    ∀ y : ℝ, Schoenflies.Plane.mk 1 y ∈ d.piece 2 ↔ b ≤ y ∧ y ≤ 1 := by
  obtain ⟨l, hl0, _hl1, hP_cut, hR_cut, _hsegment⟩ := exists_right_contact_partition h hD
  have hbl : b ≤ l :=
    ((hP_cut b).mp ((hP_interval b).mpr ⟨hb.le, le_rfl⟩)).2
  have hlb : l ≤ b :=
    ((hP_interval l).mp ((hP_cut l).mpr ⟨hl0.le, le_rfl⟩)).2
  have heq : b = l := le_antisymm hbl hlb
  simpa only [heq] using hR_cut

end Puzzling139335.N5.FourthSide
