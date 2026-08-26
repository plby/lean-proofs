import ErdosProblems.Erdos633b.CornerColumnTotals
import ErdosProblems.Erdos633b.ReptilingOrdering

/-! Relabeling the reference triangle transports actual corner-incidence
fibers by an explicit bijection, preserving the geometric tiling. -/

namespace Erdos633b.Tiling

noncomputable def cornerCountReindexEquiv {T : Triangle} {n : ℕ} (d : Tiling T n)
    (e : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    {v : (d.reindexTile e).CornerPiece i // v.val.2 = j} ≃
      {v : d.CornerPiece i // v.val.2 = e.symm j} where
  toFun v := ⟨⟨(v.val.val.1, e.symm v.val.val.2), v.val.property⟩,
    congrArg e.symm v.property⟩
  invFun v := ⟨⟨(v.val.val.1, e v.val.val.2), by
    change d.place v.val.val.1 (d.tile.points (e.symm (e v.val.val.2))) = T.points i
    simpa only [Equiv.symm_apply_apply] using v.val.property⟩, by
      change e v.val.val.2 = j
      rw [v.property, Equiv.apply_symm_apply]⟩
  left_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl (e.apply_symm_apply v.val.val.2)
  right_inv v := by
    apply Subtype.ext
    apply Subtype.ext
    exact Prod.ext rfl (e.symm_apply_apply v.val.val.2)

theorem cornerAngleCount_reindexTile {T : Triangle} {n : ℕ} (d : Tiling T n)
    (e : Equiv.Perm (Fin 3)) (i j : Fin 3) :
    (d.reindexTile e).cornerAngleCount i j = d.cornerAngleCount i (e.symm j) := by
  classical
  have hc := Fintype.card_congr (d.cornerCountReindexEquiv e i j)
  simpa only [cornerAngleCount, Fintype.card_subtype] using hc

theorem cornerColumnCount_reindexTile {T : Triangle} {n : ℕ} (d : Tiling T n)
    (e : Equiv.Perm (Fin 3)) (j : Fin 3) :
    (d.reindexTile e).cornerColumnCount j = d.cornerColumnCount (e.symm j) := by
  simp only [cornerColumnCount, d.cornerAngleCount_reindexTile]

theorem exists_reindex_zero_last_corner_column {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h : ¬ ∃ e : Equiv.Perm (Fin 3), ∀ i, T.angle i = d.tile.angle (e i)) :
    ∃ e : Equiv.Perm (Fin 3), (d.reindexTile e).cornerColumnCount 2 = 0 := by
  obtain ⟨j, hj⟩ := d.exists_zero_corner_column_of_not_permuted h
  refine ⟨Equiv.swap 2 j, ?_⟩
  simpa only [d.cornerColumnCount_reindexTile, Equiv.symm_swap, Equiv.swap_apply_left] using hj

end Erdos633b.Tiling
