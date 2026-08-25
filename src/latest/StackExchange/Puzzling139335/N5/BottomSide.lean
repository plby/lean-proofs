import StackExchange.Puzzling139335.N5.BottomSide.Barrier
import StackExchange.Puzzling139335.N5.BottomSide.Coordinates
import StackExchange.Puzzling139335.ReflectionSeparation

/-!
# Complete bottom and left sides of the normalized diagonal pair

If the diagonal pair spans the bottom and left corners, and a third piece
contains the top-right corner, then no gap can remain on either of those
two sides.  A missing bottom point and its reflected left point would have
to belong to the same fourth piece, contradicting boundary interlacing.
-/

open Set

namespace Puzzling139335.N5

private theorem remaining_index_eq {p q r i j : Fin 4}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hip : i ≠ p) (hiq : i ≠ q) (hir : i ≠ r)
    (hjp : j ≠ p) (hjq : j ≠ q) (hjr : j ≠ r) : i = j := by
  classical
  by_contra hij
  have hcard := Finset.card_le_univ ({p, q, r, i, j} : Finset (Fin 4))
  have hpnot : p ∉ ({q, r, i, j} : Finset (Fin 4)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hpq, hpr, hip.symm, hjp.symm⟩
  have hqnot : q ∉ ({r, i, j} : Finset (Fin 4)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hqr, hiq.symm, hjq.symm⟩
  have hrnot : r ∉ ({i, j} : Finset (Fin 4)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hir.symm, hjr.symm⟩
  have hinot : i ∉ ({j} : Finset (Fin 4)) := by
    simpa only [Finset.mem_singleton] using hij
  rw [Finset.card_insert_of_notMem hpnot, Finset.card_insert_of_notMem hqnot,
    Finset.card_insert_of_notMem hrnot, Finset.card_insert_of_notMem hinot,
    Finset.card_singleton] at hcard
  norm_num at hcard

/-- A diagonal pair spanning the bottom and left corners must own the
whole bottom side if a distinct third piece contains the top-right corner.
This conclusion uses no angle, straight-boundary, or local-wedge premise. -/
theorem bottom_segment_subset_of_diagonal_pair (d : SquareDissection)
    {p q r : Fin 4} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hBL : corner 0 ∈ d.piece p) (hBR : corner 1 ∈ d.piece p)
    (hTR : corner 2 ∈ d.piece r)
    (hPQ : ReflectionSeparation.diagonal '' d.piece p = d.piece q) :
    segment ℝ (corner 0) (corner 1) ⊆ d.piece p := by
  classical
  have hbelow := ReflectionSeparation.diagonal_below_of_bottom_right
    (d.jordan p) hPQ (d.disjoint_interiors hpq) hBR
  have habove : d.piece q ⊆ {z | z 0 ≤ z 1} := by
    intro z hz
    rw [← hPQ] at hz
    obtain ⟨w, hw, rfl⟩ := hz
    change w 1 ≤ w 0
    exact hbelow hw
  have hqBL : corner 0 ∈ d.piece q := by
    rw [← hPQ]
    exact ⟨corner 0, hBL, ReflectionSeparation.diagonal_fixed rfl⟩
  have hqTL : corner 3 ∈ d.piece q := by
    rw [← hPQ]
    refine ⟨corner 1, hBR, ?_⟩
    ext k
    fin_cases k <;> norm_num [corner, Fin.ext_iff]
  intro z hz
  by_contra hzP
  have hzopen : z ∈ segment ℝ (corner 0) (corner 1) \ {corner 0, corner 1} := by
    refine ⟨hz, ?_⟩
    intro hends
    rcases mem_insert_iff.mp hends with rfl | hzBR
    · exact hzP hBL
    · obtain rfl := mem_singleton_iff.mp hzBR
      exact hzP hBR
  obtain ⟨hz1, hz0, hzlt⟩ := bottom_open_coordinates hzopen
  have hwopen := diagonal_bottom_open_left hzopen
  have hzQ : z ∉ d.piece q := by
    intro hzq
    have h : z 0 ≤ z 1 := habove hzq
    rw [hz1] at h
    exact (not_le_of_gt hz0) h
  have hwP : ReflectionSeparation.diagonal z ∉ d.piece p := by
    intro hwp
    have h : ReflectionSeparation.diagonal z 1 ≤ ReflectionSeparation.diagonal z 0 :=
      hbelow hwp
    simp only [ReflectionSeparation.diagonal_apply_one,
      ReflectionSeparation.diagonal_apply_zero, hz1] at h
    exact (not_le_of_gt hz0) h
  have hwQ : ReflectionSeparation.diagonal z ∉ d.piece q := by
    intro hwq
    rw [← hPQ] at hwq
    obtain ⟨w, hw, hwz⟩ := hwq
    exact hzP (ReflectionSeparation.diagonal.injective hwz ▸ hw)
  have hzR : z ∉ d.piece r :=
    bottom_open_not_mem_of_top_right d hpr hBL hBR hTR hzopen
  have hwR : ReflectionSeparation.diagonal z ∉ d.piece r :=
    left_open_not_mem_of_top_right d hqr hqBL hqTL hTR hwopen
  have hzS : z ∈ unitSquare := ⟨⟨hz0.le, hzlt.le⟩, by simp [hz1]⟩
  have hwS : ReflectionSeparation.diagonal z ∈ unitSquare :=
    ReflectionSeparation.diagonal_mem_unitSquare.mpr hzS
  obtain ⟨i, hzi⟩ := d.exists_piece_mem hzS
  obtain ⟨j, hwj⟩ := d.exists_piece_mem hwS
  have hip : i ≠ p := fun h => hzP (h ▸ hzi)
  have hiq : i ≠ q := fun h => hzQ (h ▸ hzi)
  have hir : i ≠ r := fun h => hzR (h ▸ hzi)
  have hjp : j ≠ p := fun h => hwP (h ▸ hwj)
  have hjq : j ≠ q := fun h => hwQ (h ▸ hwj)
  have hjr : j ≠ r := fun h => hwR (h ▸ hwj)
  have hij := remaining_index_eq hpq hpr hqr hip hiq hir hjp hjq hjr
  have hwi : ReflectionSeparation.diagonal z ∈ d.piece i := hij.symm ▸ hwj
  have hwfront : ReflectionSeparation.diagonal z ∈ frontier unitSquare := by
    have hwcoord : ReflectionSeparation.diagonal z = Schoenflies.Plane.mk 0 (z 0) := by
      ext k
      fin_cases k
      · exact hz1
      · rfl
    rw [hwcoord]
    exact RectangularHull.left_mem_frontier hz0.le hzlt.le
  have hwnot : ReflectionSeparation.diagonal z ∉ segment ℝ (corner 0) (corner 1) := by
    intro hw
    have h := (bottom_segment_coordinates.mp hw).1
    exact (ne_of_gt hz0) h
  exact bottom_boundary_contacts_impossible d hip.symm hBL hBR hzi hwi
    hzopen hwfront hwnot

/-- Both sides spanned by the normalized diagonal pair are entirely owned
by that pair.  The left-side assertion is the reflected bottom-side result. -/
theorem bottom_left_segments_subset_of_diagonal_pair (d : SquareDissection)
    {p q r : Fin 4} (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (hBL : corner 0 ∈ d.piece p) (hBR : corner 1 ∈ d.piece p)
    (hTR : corner 2 ∈ d.piece r)
    (hPQ : ReflectionSeparation.diagonal '' d.piece p = d.piece q) :
    segment ℝ (corner 0) (corner 1) ⊆ d.piece p ∧
      segment ℝ (corner 0) (corner 3) ⊆ d.piece q := by
  have hbottom := bottom_segment_subset_of_diagonal_pair d hpq hpr hqr hBL hBR hTR hPQ
  refine ⟨hbottom, ?_⟩
  intro z hz
  rw [← hPQ]
  exact ⟨ReflectionSeparation.diagonal z,
    hbottom (diagonal_mem_bottom_segment_iff.mpr hz),
    ReflectionSeparation.diagonal_involutive z⟩

end Puzzling139335.N5
