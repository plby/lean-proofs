import StackExchange.Puzzling139335.N5.Normalized
import StackExchange.Puzzling139335.N5.SideExclusion.Normalized
import StackExchange.Puzzling139335.DoubleCorner.DiagonalSegment

/-!
# Actual contact points used by the strict singleton frame

The shared diagonal supplies a positive actual point independently of the
later description of the whole contact interval.  The interval bound is
used only to bound an actual source point lying on that diagonal.
-/

open Set

namespace Puzzling139335.N5

/-- Under a protected-center hypothesis neither member of the diagonal
pair contains the center, even as a boundary point. -/
theorem Normalized.center_not_mem_bottom_pair {d : SquareDissection}
    (h : Normalized d) (hc : d.HasProtectedCenter) :
    squareCenter ∉ d.piece 0 ∧ squareCenter ∉ d.piece 1 := by
  obtain ⟨i, hi⟩ := hc
  have hi0 : i ≠ 0 := by
    intro heq
    exact h.center_not_mem_pair.1 (heq ▸ hi)
  have hi1 : i ≠ 1 := by
    intro heq
    exact h.center_not_mem_pair.2 (heq ▸ hi)
  exact ⟨d.not_mem_other_piece hi0 hi, d.not_mem_other_piece hi1 hi⟩

/-- The two normalized bottom pieces contain an actual positive diagonal
point. This uses their full double-corner germs, not a hull chord. -/
theorem Normalized.exists_positive_diagonal_point {d : SquareDissection}
    (h : Normalized d) :
    ∃ a : ℝ, 0 < a ∧ (!₂[a, a] : Plane) ∈ d.piece 0 := by
  have hother : ∀ l : Fin 4, l ≠ 0 → l ≠ 1 → corner 0 ∉ d.piece l := by
    intro l hl0 hl1
    fin_cases l
    · exact False.elim (hl0 rfl)
    · exact False.elim (hl1 rfl)
    · exact h.remaining_not_mem_corner (Or.inl rfl) (by decide : (0 : Fin 4) ≠ 2)
    · exact h.remaining_not_mem_corner (Or.inr rfl) (by decide : (0 : Fin 4) ≠ 2)
  have hfix : ReflectionSeparation.diagonal (corner 0) = corner 0 :=
    ReflectionSeparation.diagonal_fixed rfl
  obtain ⟨a, ha, _, hseg⟩ := d.double_corner_diagonal_segment
    (by decide : (0 : Fin 4) ≠ 1) h.bottom_left h.left_bottom hother
    ReflectionSeparation.diagonal h.diagonal_image hfix
  have hend := (hseg (right_mem_segment ℝ (corner 0)
    (SquareSymmetry.cornerFlip 0 !₂[a, a]))).1
  refine ⟨a, ha, ?_⟩
  simpa [SquareSymmetry.cornerFlip_apply, SquareSymmetry.cornerFlipPoint,
    corner, Fin.ext_iff] using hend

namespace StrictFrame

/-- A bound on the actual diagonal contact interval bounds each actual
diagonal member. No convexity of the tile is required. -/
theorem diagonal_member_lt_half_of_contact_interval
    {P : Set Plane} {a : ℝ} (ha : a < (1 / 2 : ℝ))
    (hcontact : ∀ t : ℝ, Schoenflies.Plane.mk t t ∈ P ↔ 0 ≤ t ∧ t ≤ a)
    {C : Plane} (hC : C ∈ P) (hdiag : C 0 = C 1) : C 0 < (1 / 2 : ℝ) := by
  have hCeq : C = Schoenflies.Plane.mk (C 0) (C 0) := by
    apply PlaneIsometries.plane_ext
    · rfl
    · exact hdiag.symm
  have hm : Schoenflies.Plane.mk (C 0) (C 0) ∈ P := hCeq ▸ hC
  exact ((hcontact (C 0)).mp hm).2.trans_lt ha

end StrictFrame

end Puzzling139335.N5
