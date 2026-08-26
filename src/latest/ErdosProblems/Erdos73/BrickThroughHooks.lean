import ErdosProblems.Erdos73.BrickHookRegions

/-! Disjoint staircase paths for order-preserving attachments on opposite sides. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {c r : ℕ}

def brickThroughHook (goRight : Bool) (a b j : ℕ) : Finset (ElementaryWallVertex c r) :=
  univ.filter (fun w =>
    (w.val.1.val = a ∧ (if goRight then w.val.2.val ≤ 2 * j + 1 else 2 * j ≤ w.val.2.val)) ∨
    (w.val.1.val = b ∧ (if goRight then 2 * j ≤ w.val.2.val else w.val.2.val ≤ 2 * j + 1)) ∨
    (a ≤ w.val.1.val ∧ w.val.1.val ≤ b ∧ 2 * j ≤ w.val.2.val ∧ w.val.2.val ≤ 2 * j + 1))

theorem mem_brickThroughHook {goRight : Bool} {a b j : ℕ} {w : ElementaryWallVertex c r} :
    w ∈ brickThroughHook goRight a b j ↔
      (w.val.1.val = a ∧ (if goRight then w.val.2.val ≤ 2 * j + 1 else 2 * j ≤ w.val.2.val)) ∨
      (w.val.1.val = b ∧ (if goRight then 2 * j ≤ w.val.2.val else w.val.2.val ≤ 2 * j + 1)) ∨
      (a ≤ w.val.1.val ∧ w.val.1.val ≤ b ∧ 2 * j ≤ w.val.2.val ∧ w.val.2.val ≤ 2 * j + 1) := by
  simp only [brickThroughHook, mem_filter, mem_univ, true_and]

theorem brickThroughHook_disjoint {goRight : Bool} {a b j a' b' j' : ℕ}
    (hab : a ≤ b) (hab' : a' ≤ b') (ha : a < a') (hb : b < b')
    (hj : if goRight then j' < j else j < j') :
    Disjoint (brickThroughHook (c := c) (r := r) goRight a b j)
      (brickThroughHook goRight a' b' j') := by
  apply Finset.disjoint_left.mpr
  intro w hw hw'
  rw [mem_brickThroughHook] at hw hw'
  cases goRight <;> simp only [Bool.false_eq_true, ↓reduceIte] at hw hw' hj <;> omega

theorem exists_brick_through_hook_path (goRight : Bool) (u v : ElementaryWallVertex c r)
    (huv : u.val.1.val ≤ v.val.1.val) (j : ℕ) (hj : 0 < j) (hjc : j + 1 < c)
    (hu : if goRight then u.val.2.val ≤ 2 * j + 1 else 2 * j ≤ u.val.2.val)
    (hv : if goRight then 2 * j ≤ v.val.2.val else v.val.2.val ≤ 2 * j + 1) :
    ∃ P : GraphPath (elementaryWall c r), P.source = u ∧ P.target = v ∧
      P.vertexSet ⊆ brickThroughHook goRight u.val.1.val v.val.1.val j := by
  obtain ⟨C, hCs, hCt, hC⟩ := exists_brick_column_path
    u.val.1.val v.val.1.val j huv v.val.1.isLt hj hjc
  have hCscol := (hC C.source C.source_mem_vertexSet).2.2
  have hCtcol := (hC C.target C.target_mem_vertexSet).2.2
  have huc := u.val.2.isLt
  have hvc := v.val.2.isLt
  have hCsc := C.source.val.2.isLt
  have hCtc := C.target.val.2.isLt
  have hLu : (if goRight then 0 else 2 * j) ≤ u.val.2.val ∧
      u.val.2.val ≤ (if goRight then 2 * j + 1 else 2 * c) := by
    cases goRight <;> simp only [Bool.false_eq_true, ↓reduceIte] at hu ⊢ <;> omega
  have hLC : (if goRight then 0 else 2 * j) ≤ C.source.val.2.val ∧
      C.source.val.2.val ≤ (if goRight then 2 * j + 1 else 2 * c) := by
    cases goRight <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hRC : (if goRight then 2 * j else 0) ≤ C.target.val.2.val ∧
      C.target.val.2.val ≤ (if goRight then 2 * c else 2 * j + 1) := by
    cases goRight <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  have hRv : (if goRight then 2 * j else 0) ≤ v.val.2.val ∧
      v.val.2.val ≤ (if goRight then 2 * c else 2 * j + 1) := by
    cases goRight <;> simp only [Bool.false_eq_true, ↓reduceIte] at hv ⊢ <;> omega
  obtain ⟨L, hLs, hLt, hL⟩ := exists_brick_horizontal_path_bounded u C.source
    (Fin.ext hCs.symm) (if goRight then 0 else 2 * j) (if goRight then 2 * j + 1 else 2 * c)
    hLu hLC
  obtain ⟨R, hRs, hRt, hR⟩ := exists_brick_horizontal_path_bounded C.target v
    (Fin.ext hCt) (if goRight then 2 * j else 0) (if goRight then 2 * c else 2 * j + 1)
    hRC hRv
  let P := L.append3WithEqToPath C R hLt hRs.symm
  refine ⟨P, hLs, hRt, ?_⟩
  intro w hw
  have hh := L.append3WithEqToPath_vertexSet_subset C R hLt hRs.symm hw
  rcases mem_union.mp hh with hh | hh
  · rcases mem_union.mp hh with hh | hh
    · apply mem_brickThroughHook.mpr
      refine Or.inl ⟨congrArg Fin.val (hL w hh).1, ?_⟩
      have hb := (hL w hh).2
      cases goRight <;> simp_all only [Bool.false_eq_true, ↓reduceIte]
    · exact mem_brickThroughHook.mpr (Or.inr (Or.inr (hC w hh)))
  · apply mem_brickThroughHook.mpr
    refine Or.inr (Or.inl ⟨(congrArg Fin.val (hR w hh).1).trans hCt, ?_⟩)
    have hb := (hR w hh).2
    cases goRight <;> simp_all only [Bool.false_eq_true, ↓reduceIte]

theorem GraphSubdivisionModel.exists_through_hook_path {V : Type*} {G : SimpleGraph V}
    (S : GraphSubdivisionModel (elementaryWall c r) G) (goRight : Bool)
    (u v : ElementaryWallVertex c r) (huv : u.val.1.val ≤ v.val.1.val)
    (j : ℕ) (hj : 0 < j) (hjc : j + 1 < c)
    (hu : if goRight then u.val.2.val ≤ 2 * j + 1 else 2 * j ≤ u.val.2.val)
    (hv : if goRight then 2 * j ≤ v.val.2.val else v.val.2.val ≤ 2 * j + 1) :
    ∃ P : GraphPath G, P.source = S.branchVertex u ∧ P.target = S.branchVertex v ∧
      P.vertexSet ⊆ S.supportOver (brickThroughHook goRight u.val.1.val v.val.1.val j) := by
  obtain ⟨Q, hs, ht, hQ⟩ := exists_brick_through_hook_path goRight u v huv j hj hjc hu hv
  obtain ⟨P, hPs, hPt, hP⟩ := S.exists_path_with_walkSupport Q.walk Q.isPath
  refine ⟨P, hPs.trans (congrArg S.branchVertex hs), hPt.trans (congrArg S.branchVertex ht), ?_⟩
  rw [hP]
  apply (S.walkSupport_subset_supportOver Q.walk).trans (S.supportOver_mono ?_)
  simpa only [GraphPath.vertexSet, Finset.subset_iff, List.mem_toFinset] using hQ

end
end Erdos73
