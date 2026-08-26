import ErdosProblems.Erdos633b.CaseSeven

/-! The six explicit non-reptiling angle shapes. These predicates contain
only angle equalities and vertex permutations, with no tiling assumptions. -/

namespace Erdos633b

def GroupOneShape (S T : Triangle) : Prop :=
  3 * S.angle 0 + 2 * S.angle 1 = Real.pi ∧
    ((T.angle 0 = S.angle 0 ∧ T.angle 1 = 2 * S.angle 0 ∧ T.angle 2 = 2 * S.angle 1) ∨
     (T.angle 0 = 2 * S.angle 0 ∧ T.angle 1 = S.angle 1 ∧ T.angle 2 = S.angle 0 + S.angle 1))

def GroupTwoShape (S T : Triangle) : Prop :=
  S.angle 2 = 2 * Real.pi / 3 ∧
    ((T.angle 0 = S.angle 0 ∧ T.angle 1 = 2 * S.angle 0 ∧ T.angle 2 = 3 * S.angle 1) ∨
     (T.angle 0 = S.angle 0 ∧ T.angle 1 = 2 * S.angle 1 ∧ T.angle 2 = 2 * S.angle 0 + S.angle 1) ∨
     (T.angle 0 = S.angle 0 ∧ T.angle 1 = S.angle 0 + S.angle 1 ∧
       T.angle 2 = S.angle 0 + 2 * S.angle 1) ∨
     (T.angle 0 = 2 * S.angle 0 ∧ T.angle 1 = 2 * S.angle 1 ∧ T.angle 2 = S.angle 0 + S.angle 1))

def SixAngleShapes (S T : Triangle) : Prop :=
  ∃ e f : Equiv.Perm (Fin 3),
    GroupOneShape (S.reindex e) (T.reindex f) ∨ GroupTwoShape (S.reindex e) (T.reindex f)

def ReptilingAngles (S T : Triangle) : Prop :=
  ∃ e : Equiv.Perm (Fin 3), ∀ i, T.angle i = S.angle (e i)

theorem sixAngleShapes_of_reindex_tile (S T : Triangle) (e : Equiv.Perm (Fin 3))
    (h : SixAngleShapes (S.reindex e) T) : SixAngleShapes S T := by
  obtain ⟨f, g, h⟩ := h
  refine ⟨e.trans f, g, ?_⟩
  simpa only [Affine.Simplex.reindex_trans] using h

theorem sixAngleShapes_of_reindex_outer (S T : Triangle) (e : Equiv.Perm (Fin 3))
    (h : SixAngleShapes S (T.reindex e)) : SixAngleShapes S T := by
  obtain ⟨f, g, h⟩ := h
  refine ⟨f, e.trans g, ?_⟩
  simpa only [Affine.Simplex.reindex_trans] using h

theorem reptilingAngles_of_reindex_tile (S T : Triangle) (e : Equiv.Perm (Fin 3))
    (h : ReptilingAngles (S.reindex e) T) : ReptilingAngles S T := by
  obtain ⟨f, hf⟩ := h
  refine ⟨f.trans e.symm, ?_⟩
  intro i
  simpa only [Triangle.angle_reindex, Equiv.trans_apply] using hf i

theorem reptilingAngles_of_reindex_outer (S T : Triangle) (e : Equiv.Perm (Fin 3))
    (h : ReptilingAngles S (T.reindex e)) : ReptilingAngles S T := by
  obtain ⟨f, hf⟩ := h
  refine ⟨e.trans f, ?_⟩
  intro i
  simpa only [Triangle.angle_reindex, Equiv.trans_apply, Equiv.symm_apply_apply] using hf (e i)

end Erdos633b
