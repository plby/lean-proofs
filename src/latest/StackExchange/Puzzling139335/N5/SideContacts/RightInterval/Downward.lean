import StackExchange.Puzzling139335.RectangularHull.Interlacing

/-! # Right-side contacts cannot leave a gap below a later contact -/

open Set Schoenflies

namespace Puzzling139335.N5.SideContacts

private theorem right_mem_frontier {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Schoenflies.Plane.mk 1 y ∈ frontier unitSquare := by
  rw [unitSquare_eq_closedSquare]
  apply Schoenflies.Plane.mem_frontier_closedSquare_of_fst
  · norm_num [squareCenter]
  · change |y - (1 / 2 : ℝ)| ≤ 1 / 2
    rw [abs_le]
    constructor <;> linarith

private theorem right_segment_subset_frontier {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    segment ℝ (Schoenflies.Plane.mk 1 0) (Schoenflies.Plane.mk 1 c) ⊆
      frontier unitSquare := by
  intro p hp
  rw [Schoenflies.mem_segment_vert, segment_eq_Icc hc0] at hp
  have heq : p = Schoenflies.Plane.mk 1 (p 1) := by
    ext i
    fin_cases i
    · exact hp.1
    · rfl
  rw [heq]
  exact right_mem_frontier hp.2.1 (hp.2.2.trans hc1)

/-- A strict right-side gap belonging to `Q` cannot lie below a later `P`
contact when `P` contains the bottom-right corner and `Q` the top-right one. -/
theorem right_side_gap_impossible {P Q : Set Plane} {b c : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hBR : Schoenflies.Plane.mk 1 0 ∈ P) (hTR : Schoenflies.Plane.mk 1 1 ∈ Q)
    (hcP : Schoenflies.Plane.mk 1 c ∈ P) (hbQ : Schoenflies.Plane.mk 1 b ∈ Q)
    (hb0 : 0 < b) (hbc : b < c) (hc1 : c < 1) : False := by
  have hc0 : 0 < c := hb0.trans hbc
  have hne : Schoenflies.Plane.mk 1 0 ≠ Schoenflies.Plane.mk 1 c := by
    intro heq
    exact (ne_of_lt hc0) (congrArg (fun p : Plane => p 1) heq)
  have hbA : Schoenflies.Plane.mk 1 b ∈
      segment ℝ (Schoenflies.Plane.mk 1 0) (Schoenflies.Plane.mk 1 c) := by
    rw [Schoenflies.mem_segment_vert, segment_eq_Icc hc0.le]
    exact ⟨rfl, hb0.le, hbc.le⟩
  have hbends : Schoenflies.Plane.mk 1 b ∉
      ({Schoenflies.Plane.mk 1 0, Schoenflies.Plane.mk 1 c} : Set Plane) := by
    intro hmem
    rcases mem_insert_iff.mp hmem with heq | heq
    · exact (ne_of_gt hb0) (congrArg (fun p : Plane => p 1) heq)
    · exact (ne_of_lt hbc)
        (congrArg (fun p : Plane => p 1) (mem_singleton_iff.mp heq))
  have hTRnot : Schoenflies.Plane.mk 1 1 ∉
      segment ℝ (Schoenflies.Plane.mk 1 0) (Schoenflies.Plane.mk 1 c) := by
    intro hmem
    rw [Schoenflies.mem_segment_vert, segment_eq_Icc hc0.le] at hmem
    exact (not_le_of_gt hc1) hmem.2.2
  exact RectangularHull.boundary_arc_contacts_impossible hP hQ isJordanRegion_unitSquare
    hPS hQS hdis (isArcBetween_segment hne) (right_segment_subset_frontier hc0.le hc1.le)
    hBR hcP hbQ hTR ⟨hbA, hbends⟩ (right_mem_frontier (by norm_num) (by norm_num)) hTRnot

/-- Covering the right side by the two pieces turns noninterlacing into
downward closure of every contact of the lower piece. -/
theorem right_side_contacts_downward {P Q : Set Plane}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hBR : Schoenflies.Plane.mk 1 0 ∈ P) (hTR : Schoenflies.Plane.mk 1 1 ∈ Q)
    (hTRnotP : Schoenflies.Plane.mk 1 1 ∉ P)
    (hcover : ∀ y ∈ Icc (0 : ℝ) 1,
      Schoenflies.Plane.mk 1 y ∈ P ∨ Schoenflies.Plane.mk 1 y ∈ Q)
    {c : ℝ} (hcP : Schoenflies.Plane.mk 1 c ∈ P) :
    ∀ b ∈ Icc (0 : ℝ) c, Schoenflies.Plane.mk 1 b ∈ P := by
  intro b hb
  rcases eq_or_lt_of_le hb.1 with hb0 | hb0
  · simpa only [← hb0] using hBR
  rcases eq_or_lt_of_le hb.2 with hbc | hbc
  · rw [hbc]
    exact hcP
  have hc1 : c < 1 := lt_of_le_of_ne (hPS hcP).2.2 (by
    intro heq
    exact hTRnotP (heq ▸ hcP))
  by_contra hbP
  have hbQ := (hcover b ⟨hb0.le, (hbc.trans hc1).le⟩).resolve_left hbP
  exact right_side_gap_impossible hP hQ hPS hQS hdis hBR hTR hcP hbQ hb0 hbc hc1

end Puzzling139335.N5.SideContacts
