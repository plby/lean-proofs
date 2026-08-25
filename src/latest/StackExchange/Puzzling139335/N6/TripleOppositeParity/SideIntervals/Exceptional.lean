import StackExchange.Puzzling139335.RectangularHull.Interlacing
import StackExchange.Puzzling139335.ReflectionSeparation.Maps
import StackExchange.Puzzling139335.N7Geometry.TripleCornerBounds

/-!
# The exceptional zero-turn placements are impossible

The obstruction uses contacts of the actual Jordan pieces.  It does not
replace a boundary arc of a piece by an edge of its convex hull.
-/

open Set Schoenflies

namespace Puzzling139335.N6.TripleOppositeParity.SideIntervals

open RectangularHull TripleCornerBounds

/-- A Jordan piece joining the ends of the left side separates a strict
point of that side from the opposite top corner for every disjoint piece. -/
theorem left_endpoints_strict_contact_impossible {Q D : Set Plane} {t : ℝ}
    (hQ : IsJordanRegion Q) (hD : IsJordanRegion D)
    (hQS : Q ⊆ unitSquare) (hDS : D ⊆ unitSquare)
    (hdis : Disjoint (interior Q) (interior D))
    (ht0 : 0 < t) (ht1 : t < 1)
    (h00 : Schoenflies.Plane.mk 0 0 ∈ Q)
    (h01 : Schoenflies.Plane.mk 0 1 ∈ Q)
    (h0t : Schoenflies.Plane.mk 0 t ∈ D)
    (h11 : Schoenflies.Plane.mk 1 1 ∈ D) : False := by
  have hne : Schoenflies.Plane.mk 0 0 ≠ Schoenflies.Plane.mk 0 1 := by
    intro heq
    have := congrArg (fun p : Plane => p 1) heq
    norm_num at this
  have hAS : segment ℝ (Schoenflies.Plane.mk 0 0)
      (Schoenflies.Plane.mk 0 1) ⊆ frontier unitSquare := by
    intro p hp
    rw [Schoenflies.mem_segment_vert, segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
      at hp
    have heq : p = Schoenflies.Plane.mk 0 (p 1) := by
      ext i
      fin_cases i
      · exact hp.1
      · rfl
    rw [heq]
    exact left_mem_frontier hp.2.1 hp.2.2
  apply boundary_arc_contacts_impossible hQ hD isJordanRegion_unitSquare
    hQS hDS hdis (Schoenflies.isArcBetween_segment hne) hAS
    h00 h01 h0t h11
  · refine ⟨?_, ?_⟩
    · rw [Schoenflies.mem_segment_vert, segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
      exact ⟨rfl, ht0.le, ht1.le⟩
    · simp only [mem_insert_iff, mem_singleton_iff]
      rintro (h | h)
      · exact (ne_of_gt ht0) (congrArg (fun p : Plane => p 1) h)
      · exact (ne_of_lt ht1) (congrArg (fun p : Plane => p 1) h)
  · exact top_mem_frontier (by norm_num) (by norm_num)
  · intro hmem
    have hx := (Schoenflies.mem_segment_vert.mp hmem).1
    norm_num at hx

/-- A Jordan piece joining the ends of the bottom side separates a strict
point of that side from the opposite top corner for every disjoint piece. -/
theorem bottom_endpoints_strict_contact_impossible {P D : Set Plane} {t : ℝ}
    (hP : IsJordanRegion P) (hD : IsJordanRegion D)
    (hPS : P ⊆ unitSquare) (hDS : D ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior D))
    (ht0 : 0 < t) (ht1 : t < 1)
    (h00 : Schoenflies.Plane.mk 0 0 ∈ P)
    (h10 : Schoenflies.Plane.mk 1 0 ∈ P)
    (ht0D : Schoenflies.Plane.mk t 0 ∈ D)
    (h11 : Schoenflies.Plane.mk 1 1 ∈ D) : False := by
  have hne : Schoenflies.Plane.mk 0 0 ≠ Schoenflies.Plane.mk 1 0 := by
    intro heq
    have := congrArg (fun p : Plane => p 0) heq
    norm_num at this
  apply boundary_arc_contacts_impossible hP hD isJordanRegion_unitSquare
    hPS hDS hdis (Schoenflies.isArcBetween_segment hne)
    (bottom_segment_subset_frontier (by norm_num) (by norm_num) (by norm_num))
    h00 h10 ht0D h11
  · refine ⟨?_, ?_⟩
    · rw [Schoenflies.mem_segment_horiz, segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
      exact ⟨rfl, ht0.le, ht1.le⟩
    · simp only [mem_insert_iff, mem_singleton_iff]
      rintro (h | h)
      · exact (ne_of_gt ht0) (congrArg (fun p : Plane => p 0) h)
      · exact (ne_of_lt ht1) (congrArg (fun p : Plane => p 0) h)
  · exact top_mem_frontier (by norm_num) (by norm_num)
  · intro hmem
    have hy := (Schoenflies.mem_segment_horiz.mp hmem).1
    norm_num at hy

/-- The coordinate-exchanging zero-turn placement is excluded by the
bottom-side obstruction. -/
theorem swappedPlacement_impossible {P D : Set Plane} {h : ℝ}
    (hP : IsJordanRegion P) (hD : IsJordanRegion D)
    (hPS : P ⊆ unitSquare) (hDS : D ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior D))
    (hh0 : 0 < h) (hh1 : h < 1)
    (hplace : D = swappedPlacement h '' P)
    (h0 : (0 : Plane) ∈ P) (h1 : corner 1 ∈ P) (h2 : corner 2 ∈ D) : False := by
  have htD : Schoenflies.Plane.mk (1 - h) 0 ∈ D := by
    rw [hplace]
    refine ⟨0, h0, ?_⟩
    ext i
    fin_cases i <;> simp [swappedPlacement]
  have hzero : Schoenflies.Plane.mk 0 0 = (0 : Plane) := by
    ext i
    fin_cases i <;> rfl
  apply bottom_endpoints_strict_contact_impossible hP hD hPS hDS hdis
    (show 0 < 1 - h by linarith only [hh1])
    (show 1 - h < 1 by linarith only [hh0])
    (by simpa only [hzero] using h0)
    (by simpa [corner, Schoenflies.Plane.mk] using h1)
    htD (by simpa [corner, Schoenflies.Plane.mk] using h2)

/-- The straight zero-turn placement is excluded by the left-side
obstruction for the diagonally reflected source piece. -/
theorem straightPlacement_impossible {P Q D : Set Plane} {h : ℝ}
    (hQ : IsJordanRegion Q) (hD : IsJordanRegion D)
    (hQS : Q ⊆ unitSquare) (hDS : D ⊆ unitSquare)
    (hdis : Disjoint (interior Q) (interior D))
    (hh0 : 0 < h) (hh1 : h < 1)
    (hQeq : Q = ReflectionSeparation.diagonal '' P)
    (hplace : D = straightPlacement h '' P)
    (h0 : (0 : Plane) ∈ P) (h1 : corner 1 ∈ P) (h2 : corner 2 ∈ D) : False := by
  have h00 : Schoenflies.Plane.mk 0 0 ∈ Q := by
    rw [hQeq]
    refine ⟨0, h0, ?_⟩
    ext i
    fin_cases i <;> simp
  have h01 : Schoenflies.Plane.mk 0 1 ∈ Q := by
    rw [hQeq]
    refine ⟨corner 1, h1, ?_⟩
    ext i
    fin_cases i <;> simp [corner]
  have htD : Schoenflies.Plane.mk 0 (1 - h) ∈ D := by
    rw [hplace]
    refine ⟨0, h0, ?_⟩
    ext i
    fin_cases i <;> simp [straightPlacement]
  exact left_endpoints_strict_contact_impossible hQ hD hQS hDS hdis
    (show 0 < 1 - h by linarith only [hh1])
    (show 1 - h < 1 by linarith only [hh0])
    h00 h01 htD (by simpa [corner, Schoenflies.Plane.mk] using h2)

end Puzzling139335.N6.TripleOppositeParity.SideIntervals
