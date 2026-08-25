import StackExchange.Puzzling139335.RectangularHull.Interlacing.Regions
import StackExchange.Puzzling139335.RectangularHull.Interlacing.SquareBoundary
import StackExchange.Puzzling139335.RectangularHull.HeightBarrier.CoordinateBound
import StackExchange.Puzzling139335.RectangularHull.HeightBarrier.SideContact

/-!
# A height barrier forces ownership of the bottom side

A Jordan piece joining both bottom corners has an interior crosscut between
them.  If the piece lies below height `h`, the side of that crosscut next to the
bottom edge also lies below `h`.  Any other Jordan piece touching a strict
bottom point is confined to that side and therefore cannot rise above `h`.
-/

open Set Schoenflies

namespace Puzzling139335.RectangularHull

/-- A Jordan piece containing both bottom corners has an actual crosscut
between them, contained in the piece. -/
theorem exists_bottom_crosscut {P : Set Plane} (hP : IsJordanRegion P)
    (hPS : P ⊆ unitSquare)
    (hBL : Schoenflies.Plane.mk 0 0 ∈ P) (hBR : Schoenflies.Plane.mk 1 0 ∈ P) :
    ∃ X : Set Plane, JordanCrosscut (frontier unitSquare) X
      (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) ∧ X ⊆ P := by
  have hBLS : Schoenflies.Plane.mk 0 0 ∈ frontier unitSquare :=
    bottom_mem_frontier (by norm_num) (by norm_num)
  have hBRS : Schoenflies.Plane.mk 1 0 ∈ frontier unitSquare :=
    bottom_mem_frontier (by norm_num) (by norm_num)
  have hne : Schoenflies.Plane.mk 0 0 ≠ Schoenflies.Plane.mk 1 0 := by
    intro heq
    have := congrArg (fun p : Plane => p 0) heq
    norm_num at this
  obtain ⟨X, hX, hXP, hXi⟩ := hP.exists_arc_between_frontier
    (mem_frontier_of_subset hPS hBL hBLS) (mem_frontier_of_subset hPS hBR hBRS) hne
  refine ⟨X, ⟨isJordanCurve_frontier_unitSquare, hX, hBLS, hBRS, ?_⟩, hXP⟩
  rw [inside_frontier_unitSquare]
  exact hXi.trans (interior_mono hPS)

/-- If `P` spans the bottom corners and stays below height `h`, every disjoint
Jordan region `Q` touching a strict bottom point stays below that height too.
No crosscut, cut pair, or separation property is assumed. -/
theorem bottom_contact_height_bound {P Q : Set Plane} {h r : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hBL : Schoenflies.Plane.mk 0 0 ∈ P) (hBR : Schoenflies.Plane.mk 1 0 ∈ P)
    (hheight : ∀ p ∈ P, p 1 ≤ h)
    (hr0 : 0 < r) (hr1 : r < 1) (hrQ : Schoenflies.Plane.mk r 0 ∈ Q) :
    ∀ p ∈ Q, p 1 ≤ h := by
  obtain ⟨X, hX, hXP⟩ := exists_bottom_crosscut hP hPS hBL hBR
  let A : Set Plane := segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0)
  have hne : Schoenflies.Plane.mk 0 0 ≠ Schoenflies.Plane.mk 1 0 := by
    intro heq
    have := congrArg (fun p : Plane => p 0) heq
    norm_num at this
  have hA : IsArcBetween A (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) :=
    isArcBetween_segment hne
  have hAS : A ⊆ frontier unitSquare :=
    bottom_segment_subset_frontier (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨B, hcut⟩ := isJordanCurve_frontier_unitSquare.exists_cutPair_of_subset_arc hA hAS
  have hrA : Schoenflies.Plane.mk r 0 ∈ A := by
    rw [Schoenflies.mem_segment_horiz, segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)]
    exact ⟨rfl, hr0.le, hr1.le⟩
  have hrB : Schoenflies.Plane.mk r 0 ∉ B := by
    intro hrB
    have hends := hcut.inter_eq ▸ (show Schoenflies.Plane.mk r 0 ∈ A ∩ B from ⟨hrA, hrB⟩)
    rcases mem_insert_iff.mp hends with hleft | hright
    · exact (ne_of_gt hr0) (congrArg (fun p : Plane => p 0) hleft)
    · exact (ne_of_lt hr1)
        (congrArg (fun p : Plane => p 0) (mem_singleton_iff.mp hright))
  have hQX : Disjoint (interior Q) X :=
    (hP.disjoint_interior_left hdis.symm).mono_right hXP
  have hQi : interior Q ⊆ inside (frontier unitSquare) := by
    rw [inside_frontier_unitSquare]
    exact interior_mono hQS
  have hside : interior Q ⊆ inside (A ∪ X) :=
    subset_crosscut_side_of_boundary_contact hX hcut
      hQ.isConnected_interior.isPreconnected hQi hQX
      (hQ.closure_interior.symm ▸ hrQ) hrA hrB
  have hh0 : 0 ≤ h := hheight _ hBL
  have hcap : ∀ p ∈ A ∪ X, p 1 ≤ h := by
    intro p hp
    rcases hp with hp | hp
    · have hp0 := (Schoenflies.mem_segment_horiz.mp hp).1
      simpa only [hp0] using hh0
    · exact hheight p (hXP hp)
  have hQcap : Q ⊆ closure (inside (A ∪ X)) := by
    rw [← hQ.closure_interior]
    exact closure_mono hside
  intro p hp
  exact closure_inside_coord_one_le hcap (hQcap hp)

/-- A second Jordan piece rising above the first piece's height bound cannot
touch the strict bottom side. -/
theorem bottom_contact_above_height_impossible {P Q : Set Plane} {h r : ℝ}
    (hP : IsJordanRegion P) (hQ : IsJordanRegion Q)
    (hPS : P ⊆ unitSquare) (hQS : Q ⊆ unitSquare)
    (hdis : Disjoint (interior P) (interior Q))
    (hBL : Schoenflies.Plane.mk 0 0 ∈ P) (hBR : Schoenflies.Plane.mk 1 0 ∈ P)
    (hheight : ∀ p ∈ P, p 1 ≤ h) (habove : ∃ p ∈ Q, h < p 1)
    (hr0 : 0 < r) (hr1 : r < 1) (hrQ : Schoenflies.Plane.mk r 0 ∈ Q) : False := by
  obtain ⟨p, hp, hph⟩ := habove
  exact (not_le_of_gt hph)
    (bottom_contact_height_bound hP hQ hPS hQS hdis hBL hBR hheight hr0 hr1 hrQ p hp)

/-- If every other dissection piece rises above the spanning piece's height
bound, the spanning piece contains the whole closed bottom side. -/
theorem squareDissection_bottom_side_forced (d : SquareDissection) {i : Fin 4} {h : ℝ}
    (hBL : Schoenflies.Plane.mk 0 0 ∈ d.piece i)
    (hBR : Schoenflies.Plane.mk 1 0 ∈ d.piece i)
    (hheight : ∀ p ∈ d.piece i, p 1 ≤ h)
    (habove : ∀ j, j ≠ i → ∃ p ∈ interior (d.piece j), h < p 1) :
    segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) ⊆ d.piece i := by
  intro p hp
  rw [Schoenflies.mem_segment_horiz, segment_eq_Icc (show (0 : ℝ) ≤ 1 by norm_num)] at hp
  have heq : p = Schoenflies.Plane.mk (p 0) 0 := by
    ext k
    fin_cases k
    · rfl
    · exact hp.1
  rw [heq]
  rcases eq_or_lt_of_le hp.2.1 with h0 | h0
  · simpa only [← h0] using hBL
  rcases eq_or_lt_of_le hp.2.2 with h1 | h1
  · simpa only [h1] using hBR
  have hpS : Schoenflies.Plane.mk (p 0) 0 ∈ unitSquare := by
    exact ⟨hp.2, by norm_num⟩
  obtain ⟨j, hj⟩ := d.exists_piece_mem hpS
  by_cases hji : j = i
  · simpa only [hji] using hj
  obtain ⟨z, hz, hzh⟩ := habove j hji
  exact False.elim (bottom_contact_above_height_impossible (d.jordan i) (d.jordan j)
    (d.piece_subset i) (d.piece_subset j) (d.disjoint_interiors (fun hij => hji hij.symm))
    hBL hBR hheight ⟨z, interior_subset hz, hzh⟩ h0 h1 hj)

end Puzzling139335.RectangularHull
