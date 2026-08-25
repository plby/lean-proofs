import StackExchange.Puzzling139335.N4TwoOneOne.BoundaryIntervals
import StackExchange.Puzzling139335.N4TwoOneOne.SideGeometry.ArmEndpoints
import StackExchange.Puzzling139335.N4TwoOneOne.TopGap

/-!
# Exact reflected vertical side intervals

The intervals are derived from the actual four-piece cover.  The only extra
contact hypotheses say that the cornerless piece has at most one point on
each vertical side; no interval or arm-length certificate is assumed.
-/

open Set

namespace Puzzling139335.N4TwoOneOne

/-- The two vertical side partitions have the same cutoff. -/
structure VerticalContactIntervals (d : SquareDissection) (l : ℝ) : Prop where
  left_source : ∀ y ∈ Icc (0 : ℝ) 1,
    ((!₂[0, y] : Plane) ∈ d.piece 0 ↔ y ≤ l)
  right_source : ∀ y ∈ Icc (0 : ℝ) 1,
    ((!₂[1, y] : Plane) ∈ d.piece 0 ↔ y ≤ l)
  left_singleton : ∀ y ∈ Icc (0 : ℝ) 1,
    ((!₂[0, y] : Plane) ∈ d.piece 2 ↔ l ≤ y)
  right_singleton : ∀ y ∈ Icc (0 : ℝ) 1,
    ((!₂[1, y] : Plane) ∈ d.piece 1 ↔ l ≤ y)

namespace SourceData

variable {d : SquareDissection} {θ u v : ℝ}

private theorem exists_left_contact_cutoff (h : SourceData d θ u v)
    (hcfg : Configuration d)
    (hD : (d.piece 3 ∩ {p : Plane | p 0 = 0}).Subsingleton) :
    ∃ l ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ((!₂[0, y] : Plane) ∈ d.piece 0 ↔ y ≤ l) ∧
      ((!₂[0, y] : Plane) ∈ d.piece 2 ↔ l ≤ y) := by
  have hD' : (d.piece 3 ∩ BoundaryIntervals.sidePoint 3 '' Icc (0 : ℝ) 1).Subsingleton := by
    rintro p ⟨hp, a, ha, rfl⟩ q ⟨hq, b, hb, rfl⟩
    exact hD ⟨hp, rfl⟩ ⟨hq, rfl⟩
  have h0P : BoundaryIntervals.sidePoint 3 0 ∈ d.piece 0 := by
    change corner 0 ∈ d.piece 0
    exact h.bottom_left
  have h0Q : BoundaryIntervals.sidePoint 3 0 ∉ d.piece 2 := by
    change corner 0 ∉ d.piece 2
    exact hcfg.bottom_corner_unique (Or.inl rfl) 2 (by decide)
  have h1P : BoundaryIntervals.sidePoint 3 1 ∉ d.piece 0 := by
    intro hp
    have hb := h.height_le_half hp
    change (1 : ℝ) ≤ 1 / 2 at hb
    norm_num at hb
  have h1Q : BoundaryIntervals.sidePoint 3 1 ∈ d.piece 2 := by
    change corner 3 ∈ d.piece 2
    exact h.top_left
  have hcover : ∀ y ∈ Icc (0 : ℝ) 1,
      BoundaryIntervals.sidePoint 3 y ∈ d.piece 0 ∨
      BoundaryIntervals.sidePoint 3 y ∈ d.piece 2 ∨
      BoundaryIntervals.sidePoint 3 y ∈ d.piece 3 := by
    intro y hy
    obtain ⟨i, hi⟩ := d.exists_piece_mem (BoundaryIntervals.sidePoint_mem_unitSquare 3 hy)
    fin_cases i
    · exact Or.inl hi
    · exact (h.left_side_not_right y hi).elim
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hi)
  exact BoundaryIntervals.exists_side_cutoff_of_subsingleton_contact 3
    (d.jordan 0) (d.jordan 2) (d.piece_subset 0) (d.piece_subset 2)
    (d.disjoint_interiors (by decide)) h0P h0Q h1P h1Q hD' hcover

private theorem exists_right_contact_cutoff (h : SourceData d θ u v)
    (hcfg : Configuration d)
    (hD : (d.piece 3 ∩ {p : Plane | p 0 = 1}).Subsingleton) :
    ∃ l ∈ Ioo (0 : ℝ) 1, ∀ y ∈ Icc (0 : ℝ) 1,
      ((!₂[1, y] : Plane) ∈ d.piece 0 ↔ y ≤ l) ∧
      ((!₂[1, y] : Plane) ∈ d.piece 1 ↔ l ≤ y) := by
  have hD' : (d.piece 3 ∩ BoundaryIntervals.sidePoint 1 '' Icc (0 : ℝ) 1).Subsingleton := by
    rintro p ⟨hp, a, ha, rfl⟩ q ⟨hq, b, hb, rfl⟩
    exact hD ⟨hp, rfl⟩ ⟨hq, rfl⟩
  have h0P : BoundaryIntervals.sidePoint 1 0 ∈ d.piece 0 := by
    change corner 1 ∈ d.piece 0
    exact h.bottom_right
  have h0Q : BoundaryIntervals.sidePoint 1 0 ∉ d.piece 1 := by
    change corner 1 ∉ d.piece 1
    exact hcfg.bottom_corner_unique (Or.inr rfl) 1 (by decide)
  have h1P : BoundaryIntervals.sidePoint 1 1 ∉ d.piece 0 := by
    intro hp
    have hb := h.height_le_half hp
    change (1 : ℝ) ≤ 1 / 2 at hb
    norm_num at hb
  have h1Q : BoundaryIntervals.sidePoint 1 1 ∈ d.piece 1 := by
    change corner 2 ∈ d.piece 1
    exact h.top_right
  have hcover : ∀ y ∈ Icc (0 : ℝ) 1,
      BoundaryIntervals.sidePoint 1 y ∈ d.piece 0 ∨
      BoundaryIntervals.sidePoint 1 y ∈ d.piece 1 ∨
      BoundaryIntervals.sidePoint 1 y ∈ d.piece 3 := by
    intro y hy
    obtain ⟨i, hi⟩ := d.exists_piece_mem (BoundaryIntervals.sidePoint_mem_unitSquare 1 hy)
    fin_cases i
    · exact Or.inl hi
    · exact Or.inr (Or.inl hi)
    · exact (h.right_side_not_left y hi).elim
    · exact Or.inr (Or.inr hi)
  exact BoundaryIntervals.exists_side_cutoff_of_subsingleton_contact 1
    (d.jordan 0) (d.jordan 1) (d.piece_subset 0) (d.piece_subset 1)
    (d.disjoint_interiors (by decide)) h0P h0Q h1P h1Q hD' hcover

/-- Closedness gives both vertical cutoffs, and reflection forces them to
agree.  The strict source-height bound puts the common cutoff below one half. -/
theorem exists_vertical_contact_intervals (h : SourceData d θ u v)
    (hcfg : Configuration d)
    (hDl : (d.piece 3 ∩ {p : Plane | p 0 = 0}).Subsingleton)
    (hDr : (d.piece 3 ∩ {p : Plane | p 0 = 1}).Subsingleton) :
    ∃ l ∈ Ioo (0 : ℝ) (1 / 2), VerticalContactIntervals d l := by
  obtain ⟨l, hl, hleft⟩ := h.exists_left_contact_cutoff hcfg hDl
  obtain ⟨r, hr, hright⟩ := h.exists_right_contact_cutoff hcfg hDr
  have hlI : l ∈ Icc (0 : ℝ) 1 := ⟨hl.1.le, hl.2.le⟩
  have hrI : r ∈ Icc (0 : ℝ) 1 := ⟨hr.1.le, hr.2.le⟩
  have hrle : r ≤ l := (hright l hlI).2.mp
    ((h.left_side_mem_iff_right_side_mem l).mp ((hleft l hlI).2.mpr le_rfl))
  have hlle : l ≤ r := (hleft r hrI).2.mp
    ((h.left_side_mem_iff_right_side_mem r).mpr ((hright r hrI).2.mpr le_rfl))
  have hrl : r = l := le_antisymm hrle hlle
  subst r
  have hlhalf : l < (1 / 2 : ℝ) := by
    have hp := (hleft l hlI).1.mpr le_rfl
    exact h.height_lt_half hcfg.right_vertical_germ (h.angle_lt_half_pi hcfg) hp
  refine ⟨l, ⟨hl.1, hlhalf⟩, ?_⟩
  exact ⟨fun y hy => (hleft y hy).1, fun y hy => (hright y hy).1,
    fun y hy => (hleft y hy).2, fun y hy => (hright y hy).2⟩

/-- The side partition supplies actual source endpoints, including the full
incoming arm of length `1-l`. -/
theorem exists_vertical_geometry (h : SourceData d θ u v) (hcfg : Configuration d)
    (hDl : (d.piece 3 ∩ {p : Plane | p 0 = 0}).Subsingleton)
    (hDr : (d.piece 3 ∩ {p : Plane | p 0 = 1}).Subsingleton) :
    ∃ l ∈ Ioo (0 : ℝ) (1 / 2), VerticalContactIntervals d l ∧
      (!₂[0, l] : Plane) ∈ d.piece 0 ∧ (!₂[1, l] : Plane) ∈ d.piece 0 ∧
      incomingEnd θ u v (1 - l) ∈ d.piece 0 := by
  obtain ⟨l, hl, hside⟩ := h.exists_vertical_contact_intervals hcfg hDl hDr
  have hlI : l ∈ Icc (0 : ℝ) 1 := ⟨hl.1.le, by linarith [hl.2]⟩
  exact ⟨l, hl, hside, (hside.left_source l hlI).mpr le_rfl,
    (hside.right_source l hlI).mpr le_rfl,
    h.incomingEnd_mem_of_right_side_contact ((hside.right_singleton l hlI).mpr le_rfl)⟩

end SourceData

end Puzzling139335.N4TwoOneOne
