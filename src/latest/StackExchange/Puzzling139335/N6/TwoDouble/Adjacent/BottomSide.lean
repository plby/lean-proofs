import StackExchange.Puzzling139335.RectangularHull.HeightBarrier
import StackExchange.Puzzling139335.ReflectionSeparation
import Mathlib.Topology.Order.Compact

/-!
# The actual bottom side in the adjacent-double-corner configuration

The reflected bottom-corner piece lies below the anti-diagonal and omits
the top-left corner. Compactness gives a height bound strictly below one.
All other pieces contain top corners, so the Jordan height barrier forces
the entire actual bottom side into the first piece.
-/

open Set

namespace Puzzling139335.N6.TwoDouble.Adjacent

/-- A strict height attained by a Jordan region is also exceeded at an
interior point. This uses regular closedness, not boundary area. -/
theorem exists_interior_above_of_mem {P : Set Plane} (hP : IsJordanRegion P)
    {p : Plane} (hp : p ∈ P) {h : ℝ} (hph : h < p 1) :
    ∃ q ∈ interior P, h < q 1 := by
  by_contra! hnot
  have hsub : interior P ⊆ {q : Plane | q 1 ≤ h} := fun q hq => hnot q hq
  have hclosed : IsClosed {q : Plane | q 1 ≤ h} :=
    isClosed_le (by fun_prop) continuous_const
  have hcl := closure_minimal hsub hclosed
  rw [hP.closure_interior] at hcl
  exact not_le_of_gt hph (hcl hp)

/-- The reflected first piece has a uniform height bound strictly below
the top side. The protected center is used only to exclude its opposite
pair of square corners. -/
theorem exists_bottom_piece_height_bound (d : SquareDissection)
    (hc : d.HasProtectedCenter)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hanti : ReflectionSeparation.antiDiagonal '' d.piece 0 = d.piece 1) :
    ∃ h : ℝ, h < 1 ∧ ∀ p ∈ d.piece 0, p 1 ≤ h := by
  have hbelow := ReflectionSeparation.antiDiagonal_below_of_bottom_left
    (d.jordan 0) hanti (d.disjoint_interiors (by decide : (0 : Fin 4) ≠ 1)) hBL
  have hnotTL : corner 3 ∉ d.piece 0 :=
    d.opposite_corner_not_mem hc 0 1 hBR
  obtain ⟨p, hp, hmax⟩ := (d.jordan 0).isCompact.exists_isMaxOn ⟨_, hBL⟩
    (f := fun q : Plane => q 1) (by fun_prop)
  refine ⟨p 1, ?_, fun q hq => hmax hq⟩
  have hpS := d.piece_subset 0 hp
  have hsum : p 0 + p 1 ≤ 1 := hbelow hp
  by_contra hnot
  have hy : p 1 = 1 := le_antisymm hpS.2.2 (not_lt.mp hnot)
  have hx : p 0 = 0 := le_antisymm (by linarith only [hsum, hy]) hpS.1.1
  have heq : p = corner 3 := by
    ext k
    fin_cases k <;> simp [corner, hx, hy, Fin.ext_iff]
  exact hnotTL (heq ▸ hp)

/-- The reflection carries the first piece's bottom-left corner to the
second piece's top-right corner. -/
theorem top_right_mem_reflected_piece (d : SquareDissection)
    (hBL : corner 0 ∈ d.piece 0)
    (hanti : ReflectionSeparation.antiDiagonal '' d.piece 0 = d.piece 1) :
    corner 2 ∈ d.piece 1 := by
  have hcorner : ReflectionSeparation.antiDiagonal (corner 0) = corner 2 := by
    ext k
    fin_cases k <;> simp [corner, Fin.ext_iff]
  rw [← hanti, ← hcorner]
  exact mem_image_of_mem _ hBL

/-- In the normalized adjacent-double-corner configuration the first
piece contains the whole closed bottom segment, including its endpoints. -/
theorem bottom_side_subset (d : SquareDissection) (hc : d.HasProtectedCenter)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hanti : ReflectionSeparation.antiDiagonal '' d.piece 0 = d.piece 1)
    (hTL2 : corner 3 ∈ d.piece 2) (hTL3 : corner 3 ∈ d.piece 3) :
    segment ℝ (corner 0) (corner 1) ⊆ d.piece 0 := by
  obtain ⟨h, hh, hheight⟩ := exists_bottom_piece_height_bound d hc hBL hBR hanti
  have hTR1 := top_right_mem_reflected_piece d hBL hanti
  change segment ℝ (Schoenflies.Plane.mk 0 0) (Schoenflies.Plane.mk 1 0) ⊆ d.piece 0
  apply RectangularHull.squareDissection_bottom_side_forced d hBL hBR hheight
  intro j hj
  have htop : ∃ p ∈ d.piece j, p 1 = 1 := by
    fin_cases j
    · exact False.elim (hj rfl)
    · exact ⟨corner 2, hTR1, by norm_num [corner, Fin.ext_iff]⟩
    · exact ⟨corner 3, hTL2, by norm_num [corner, Fin.ext_iff]⟩
    · exact ⟨corner 3, hTL3, by norm_num [corner, Fin.ext_iff]⟩
  obtain ⟨p, hp, hp1⟩ := htop
  exact exists_interior_above_of_mem (d.jordan j) hp (hp1.symm ▸ hh)

end Puzzling139335.N6.TwoDouble.Adjacent
