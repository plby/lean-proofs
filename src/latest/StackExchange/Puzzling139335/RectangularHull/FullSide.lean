import StackExchange.Puzzling139335.RectangularHull.HeightBarrier
import StackExchange.Puzzling139335.BandMass.HalfBands

/-!
# An outer half-height piece owns its whole square side

Quarter-mass saturation forces every other piece to have an interior point
above the midline, including the protected-center piece itself. The actual
Jordan height barrier then gives the entire bottom side to the lower piece.
-/

open Set

namespace Puzzling139335.RectangularHull

theorem center_not_in_interior_lower_half {P : Set Plane}
    (hP : P ⊆ horizontalBand 0 (1 / 2)) : squareCenter ∉ interior P := by
  intro h
  have hm := (mem_interior_horizontalBand_iff 0 (1 / 2) squareCenter).mp
    (interior_mono hP h)
  norm_num [squareCenter] at hm

theorem center_not_in_interior_upper_half {P : Set Plane}
    (hP : P ⊆ horizontalBand (1 / 2) 1) : squareCenter ∉ interior P := by
  intro h
  have hm := (mem_interior_horizontalBand_iff (1 / 2) 1 squareCenter).mp
    (interior_mono hP h)
  norm_num [squareCenter] at hm

/-- A bottom-corner piece lying below height at most one half contains the
entire actual bottom side in a protected-center dissection. -/
theorem lower_outer_piece_contains_bottom_side (d : SquareDissection)
    (hc : d.HasProtectedCenter) {i : Fin 4} {h : ℝ} (hh : h ≤ 1 / 2)
    (hBL : Schoenflies.Plane.mk 0 0 ∈ d.piece i)
    (hBR : Schoenflies.Plane.mk 1 0 ∈ d.piece i)
    (hheight : ∀ p ∈ d.piece i, p 1 ≤ h) :
    segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) ⊆ d.piece i := by
  obtain ⟨c, hcenter⟩ := hc
  have hiLower : d.piece i ⊆ horizontalBand 0 (1 / 2) := by
    intro p hp
    have hpS := d.piece_subset i hp
    exact ⟨hpS.1, hpS.2.1, (hheight p hp).trans hh⟩
  have hci : c ≠ i := by
    intro hci
    subst c
    exact center_not_in_interior_lower_half hiLower hcenter
  apply squareDissection_bottom_side_forced d hBL hBR hheight
  intro j hji
  by_cases hjc : j = c
  · subst j
    obtain ⟨p, hp, hpy⟩ := (d.center_piece_crosses_midline hcenter).2
    exact ⟨p, hp, hh.trans_lt hpy⟩
  · obtain ⟨p, hp, hpy⟩ := d.exists_interior_above_of_lower_piece hcenter hci
      (fun heq => hjc heq.symm) hji.symm hiLower
    exact ⟨p, hp, hh.trans_lt hpy⟩

/-- A rectangular lower hull supplies exactly the corner memberships and
height hypothesis needed by the full-side theorem. -/
theorem lower_outer_hull_contains_bottom_side (d : SquareDissection)
    (hc : d.HasProtectedCenter) {i : Fin 4} {h : ℝ} (hh : h ≤ 1 / 2)
    (hBL : Schoenflies.Plane.mk 0 0 ∈ d.piece i)
    (hBR : Schoenflies.Plane.mk 1 0 ∈ d.piece i)
    (hsub : d.piece i ⊆ horizontalBand 0 h) :
    segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) ⊆ d.piece i :=
  lower_outer_piece_contains_bottom_side d hc hh hBL hBR (fun _ hp => (hsub hp).2.2)

end Puzzling139335.RectangularHull
