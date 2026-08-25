import StackExchange.Puzzling139335.RectangularHull.Interlacing

/-!
# A gap between top-side contacts is impossible

The segment from a top-side contact to the top-right corner is an actual
arc of the square boundary.  Another Jordan region cannot meet both its
open part and the complementary boundary when the interiors are disjoint.
-/

open Set Schoenflies

namespace Puzzling139335.N5.TopContacts

/-- The top segment from horizontal coordinate `m` to the top-right corner
lies entirely on the square frontier. -/
theorem top_segment_subset_frontier {m : ℝ} (hm0 : 0 ≤ m) (hm1 : m ≤ 1) :
    segment ℝ (Schoenflies.Plane.mk m 1) (Schoenflies.Plane.mk 1 1) ⊆
      frontier unitSquare := by
  intro p hp
  rw [Schoenflies.mem_segment_horiz, segment_eq_Icc hm1] at hp
  have heq : p = Schoenflies.Plane.mk (p 0) 1 := by
    ext i
    fin_cases i
    · rfl
    · exact hp.1
  rw [heq]
  exact RectangularHull.top_mem_frontier (hm0.trans hp.2.1) hp.2.2

/-- With top contacts ordered `y < m < z < 1`, one Jordan region cannot
contain `m` and the top-right corner while another, with disjoint interior,
contains both `y` and `z`. -/
theorem top_side_gap_impossible {R D : Set Plane} {y m z : ℝ}
    (hR : IsJordanRegion R) (hD : IsJordanRegion D)
    (hRS : R ⊆ unitSquare) (hDS : D ⊆ unitSquare)
    (hdis : Disjoint (interior R) (interior D))
    (hmR : Schoenflies.Plane.mk m 1 ∈ R)
    (hTR : Schoenflies.Plane.mk 1 1 ∈ R)
    (hzD : Schoenflies.Plane.mk z 1 ∈ D)
    (hyD : Schoenflies.Plane.mk y 1 ∈ D)
    (hy0 : 0 ≤ y) (hym : y < m) (hmz : m < z) (hz1 : z < 1) : False := by
  have hm0 : 0 ≤ m := hy0.trans hym.le
  have hm1 : m < 1 := hmz.trans hz1
  have hne : Schoenflies.Plane.mk m 1 ≠ Schoenflies.Plane.mk 1 1 := by
    intro heq
    exact (ne_of_lt hm1) (congrArg (fun p : Plane => p 0) heq)
  have hzA : Schoenflies.Plane.mk z 1 ∈
      segment ℝ (Schoenflies.Plane.mk m 1) (Schoenflies.Plane.mk 1 1) := by
    rw [Schoenflies.mem_segment_horiz, segment_eq_Icc hm1.le]
    exact ⟨rfl, hmz.le, hz1.le⟩
  have hzends : Schoenflies.Plane.mk z 1 ∉
      ({Schoenflies.Plane.mk m 1, Schoenflies.Plane.mk 1 1} : Set Plane) := by
    intro hmem
    rcases mem_insert_iff.mp hmem with heq | heq
    · exact (ne_of_gt hmz) (congrArg (fun p : Plane => p 0) heq)
    · exact (ne_of_lt hz1)
        (congrArg (fun p : Plane => p 0) (mem_singleton_iff.mp heq))
  have hyNot : Schoenflies.Plane.mk y 1 ∉
      segment ℝ (Schoenflies.Plane.mk m 1) (Schoenflies.Plane.mk 1 1) := by
    intro hmem
    rw [Schoenflies.mem_segment_horiz, segment_eq_Icc hm1.le] at hmem
    exact (not_le_of_gt hym) hmem.2.1
  exact RectangularHull.boundary_arc_contacts_impossible
    hR hD isJordanRegion_unitSquare hRS hDS hdis
    (isArcBetween_segment hne) (top_segment_subset_frontier hm0 hm1.le)
    hmR hTR hzD hyD ⟨hzA, hzends⟩
    (RectangularHull.top_mem_frontier hy0 (hym.trans hm1).le) hyNot

end Puzzling139335.N5.TopContacts
