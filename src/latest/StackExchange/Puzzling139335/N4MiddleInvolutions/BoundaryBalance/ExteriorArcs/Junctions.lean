import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.ExteriorArcs.Geometry
import StackExchange.Puzzling139335.N4MiddleInvolutions.BoundaryBalance.ExteriorArcs.Uniqueness

/-! The terminal side contacts of the outer pieces are extended triple junctions. -/

open Set

namespace Puzzling139335.N4MiddleInvolutions.BoundaryBalance

variable {d : SquareDissection}

/-- Two distinct tile owners and the exterior give an extended triple junction. -/
theorem mem_junctions_of_exterior_two_tiles {p : Plane} {i j : Fin 4}
    (hij : i ≠ j) (hext : p ∈ closedSquareExterior)
    (hi : p ∈ d.piece i) (hj : p ∈ d.piece j) :
    p ∈ tripleContactSet d.extendedPiece := by
  refine ⟨.inl i, .inl j, .inr (), ?_, by simp, by simp, hi, hj, hext⟩
  exact fun h => hij (Sum.inl.inj h)

/-- A point on either vertical side, at a height in the unit interval,
belongs to the square frontier. -/
theorem side_point_mem_frontier_unitSquare {x y : ℝ}
    (hx : x = 0 ∨ x = 1) (hy : y ∈ Icc (0 : ℝ) 1) :
    Schoenflies.Plane.mk x y ∈ frontier unitSquare := by
  rw [unitSquare_eq_closedSquare]
  apply Schoenflies.Plane.mem_frontier_closedSquare_of_fst
  · change |x - (1 / 2 : ℝ)| = 1 / 2
    rcases hx with rfl | rfl <;> norm_num
  · change |y - (1 / 2 : ℝ)| ≤ 1 / 2
    rw [abs_le]
    constructor <;> linarith only [hy.1, hy.2]

/-- Both terminal contacts on a vertical side are triple junctions after
adjoining the exterior.  If the gap degenerates, the two outer pieces
already meet at the same midpoint; otherwise closedness supplies a middle
piece at each gap endpoint. -/
theorem side_terminal_mem_junctions
    (h : N4OuterPair.Configuration d) {x c : ℝ}
    (hx : x = 0 ∨ x = 1) (hc : c ∈ Ioc (0 : ℝ) (1 / 2))
    (hcontact : ∀ y : ℝ,
      Schoenflies.Plane.mk x y ∈ d.piece 0 ↔ y ∈ Icc (0 : ℝ) c) :
    Schoenflies.Plane.mk x c ∈ tripleContactSet d.extendedPiece ∧
      Schoenflies.Plane.mk x (1 - c) ∈ tripleContactSet d.extendedPiece := by
  have hlower : Schoenflies.Plane.mk x c ∈ d.piece 0 :=
    (hcontact c).mpr ⟨hc.1.le, le_rfl⟩
  have hupper : Schoenflies.Plane.mk x (1 - c) ∈ d.piece 1 :=
    (h.upper_side_contact_iff hcontact (1 - c)).mpr
      ⟨le_rfl, by linarith only [hc.1]⟩
  have hlowerExt : Schoenflies.Plane.mk x c ∈ closedSquareExterior := by
    have hf := side_point_mem_frontier_unitSquare hx
      (show c ∈ Icc (0 : ℝ) 1 from ⟨hc.1.le, by linarith only [hc.2]⟩)
    rw [← unitSquare_inter_closedSquareExterior] at hf
    exact hf.2
  have hupperExt : Schoenflies.Plane.mk x (1 - c) ∈ closedSquareExterior := by
    have hf := side_point_mem_frontier_unitSquare hx
      (show 1 - c ∈ Icc (0 : ℝ) 1 from
        ⟨by linarith only [hc.2], by linarith only [hc.1]⟩)
    rw [← unitSquare_inter_closedSquareExterior] at hf
    exact hf.2
  by_cases hcHalf : c < 1 / 2
  · have hgap := h.closed_side_gap_covered hx hc.1.le hcHalf hcontact
    have horder : c ≤ 1 - c := by linarith only [hcHalf]
    constructor
    · rcases hgap c ⟨le_rfl, horder⟩ with hmiddle | hmiddle
      · exact mem_junctions_of_exterior_two_tiles (by decide) hlowerExt hlower hmiddle
      · exact mem_junctions_of_exterior_two_tiles (by decide) hlowerExt hlower hmiddle
    · rcases hgap (1 - c) ⟨horder, le_rfl⟩ with hmiddle | hmiddle
      · exact mem_junctions_of_exterior_two_tiles (by decide) hupperExt hupper hmiddle
      · exact mem_junctions_of_exterior_two_tiles (by decide) hupperExt hupper hmiddle
  · have hsame : 1 - c = c := by linarith only [hc.2, hcHalf]
    rw [hsame] at hupper ⊢
    have hjunction := mem_junctions_of_exterior_two_tiles
      (by decide : (0 : Fin 4) ≠ 1) hlowerExt hlower hupper
    exact ⟨hjunction, hjunction⟩

end Puzzling139335.N4MiddleInvolutions.BoundaryBalance
