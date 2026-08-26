import ErdosProblems.Erdos73.TileGapRegions

/-! Reserved gaps meet tile arms only at the correct owning ports. -/

namespace Erdos73.BrickTileArray
noncomputable section
open scoped Classical

open SimpleGraph Finset

variable {c r C R : ℕ} (A : BrickTileArray c r C R)

theorem horizontalGap_arm_endpoint {i : Fin r} {j j' : Fin (2 * c)}
    (hj : j.val + 1 = j'.val) (w : ElementaryWallVertex c r) (a : Fin 3)
    {x : ElementaryWallVertex C R} (hx : x ∈ A.horizontalGap i j j')
    (hwa : x ∈ (A.arm w a).vertexSet) :
    w.val.1 = i ∧ ((w.val.2 = j ∧ a = 1 ∧ x = (A.arm w 1).target) ∨
      (w.val.2 = j' ∧ a = 0 ∧ x = (A.arm w 0).target)) := by
  have hg := A.mem_horizontalGap.mp hx
  have hb := A.arm_box w a hwa
  have hr : A.row w.val.1 = A.row i := by omega
  have hwrow := A.row_strictMono.injective hr
  have hl : j ≤ w.val.2 := A.column_strictMono.le_iff_le.mp (by omega)
  have hu : w.val.2 ≤ j' := A.column_strictMono.le_iff_le.mp (by omega)
  have hcases : w.val.2 = j ∨ w.val.2 = j' := by
    change j.val ≤ w.val.2.val at hl
    change w.val.2.val ≤ j'.val at hu
    by_cases he : w.val.2.val = j.val
    · exact Or.inl (Fin.ext he)
    · exact Or.inr (Fin.ext (by omega))
  refine ⟨hwrow, ?_⟩
  rcases hcases with hwcol | hwcol
  · have hcol := congrArg A.column hwcol
    have hp := A.arm_one_target_coordinates w
    have he : x = (A.arm w 1).target :=
      Subtype.ext (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
    have ha : a = 1 := by
      by_contra hn
      exact A.arm_target_not_mem_other w (Ne.symm hn) (he ▸ hwa)
    exact Or.inl ⟨hwcol, ha, he⟩
  · have hcol := congrArg A.column hwcol
    have hp := A.arm_zero_target_coordinates w
    have he : x = (A.arm w 0).target :=
      Subtype.ext (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
    have ha : a = 0 := by
      by_contra hn
      exact A.arm_target_not_mem_other w (Ne.symm hn) (he ▸ hwa)
    exact Or.inr ⟨hwcol, ha, he⟩

theorem verticalGap_arm_endpoint {i i' : Fin r} {j : Fin (2 * c)}
    (hi : i.val + 1 = i'.val) (hpar : (j.val + i.val) % 2 = 1)
    (w : ElementaryWallVertex c r) (a : Fin 3)
    {x : ElementaryWallVertex C R} (hx : x ∈ A.verticalGap i i' j)
    (hwa : x ∈ (A.arm w a).vertexSet) :
    w.val.2 = j ∧ (w.val.1 = i ∨ w.val.1 = i') ∧ a = 2 ∧ x = (A.arm w 2).target := by
  have hg := A.mem_verticalGap.mp hx
  have hb := A.arm_box w a hwa
  have hc : A.column w.val.2 = A.column j := by omega
  have hwcol := A.column_strictMono.injective hc
  have hl : i ≤ w.val.1 := A.row_strictMono.le_iff_le.mp (by omega)
  have hu : w.val.1 ≤ i' := A.row_strictMono.le_iff_le.mp (by omega)
  have hcases : w.val.1 = i ∨ w.val.1 = i' := by
    change i.val ≤ w.val.1.val at hl
    change w.val.1.val ≤ i'.val at hu
    by_cases he : w.val.1.val = i.val
    · exact Or.inl (Fin.ext he)
    · exact Or.inr (Fin.ext (by omega))
  have hpoint : x = (A.arm w 2).target := by
    rcases hcases with hwrow | hwrow
    · have hr := congrArg A.row hwrow
      have hdown : (w.val.2.val + w.val.1.val) % 2 = 1 := by
        simpa only [hwcol, hwrow] using hpar
      have hp := A.arm_two_target_coordinates w
      simp only [if_pos hdown] at hp
      obtain ⟨z, hz, hzr, hzc⟩ := A.arm_coordinates w a hwa
      have hzb : z.1.val = 8 := by have hzi := z.1.isLt; omega
      have hbot := wallTileArmRawSupport_bottom_bounds _ _ z hz hzb
      exact Subtype.ext (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
    · have hr := congrArg A.row hwrow
      have hup : (w.val.2.val + w.val.1.val) % 2 ≠ 1 := by
        have hwr := congrArg Fin.val hwrow
        have hwc := congrArg Fin.val hwcol
        omega
      have hp := A.arm_two_target_coordinates w
      simp only [if_neg hup, Nat.add_zero] at hp
      have hfinal : x.val.1.val = 12 * A.row i' := by omega
      have hlast := hg.2.2.2.2 hfinal
      exact Subtype.ext (Prod.ext (Fin.ext (by omega)) (Fin.ext (by omega)))
  have ha : a = 2 := by
    by_contra hn
    exact A.arm_target_not_mem_other w (Ne.symm hn) (hpoint ▸ hwa)
  exact ⟨hwcol, hcases, ha, hpoint⟩

end
end Erdos73.BrickTileArray
