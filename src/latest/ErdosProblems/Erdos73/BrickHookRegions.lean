import ErdosProblems.Erdos73.BrickColumnPaths

/-! Coordinate hooks and their separation for series and nested endpoint pairs. -/

namespace Erdos73
noncomputable section
open scoped Classical

open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {c r : ℕ}

def brickLeftHook (a b j : ℕ) : Finset (ElementaryWallVertex c r) :=
  univ.filter (fun w => ((w.val.1.val = a ∨ w.val.1.val = b) ∧ w.val.2.val ≤ 2 * j + 1) ∨
    (a ≤ w.val.1.val ∧ w.val.1.val ≤ b ∧ 2 * j ≤ w.val.2.val ∧ w.val.2.val ≤ 2 * j + 1))

theorem mem_brickLeftHook {a b j : ℕ} {w : ElementaryWallVertex c r} :
    w ∈ brickLeftHook a b j ↔
      ((w.val.1.val = a ∨ w.val.1.val = b) ∧ w.val.2.val ≤ 2 * j + 1) ∨
      (a ≤ w.val.1.val ∧ w.val.1.val ≤ b ∧ 2 * j ≤ w.val.2.val ∧ w.val.2.val ≤ 2 * j + 1) := by
  simp only [brickLeftHook, mem_filter, mem_univ, true_and]

theorem brickLeftHook_row_bounds {a b j : ℕ} (hab : a ≤ b)
    {w : ElementaryWallVertex c r} (hw : w ∈ brickLeftHook a b j) :
    a ≤ w.val.1.val ∧ w.val.1.val ≤ b := by
  rw [mem_brickLeftHook] at hw
  omega

theorem brickLeftHook_disjoint_series {a b j a' b' j' : ℕ}
    (hab : a ≤ b) (hab' : a' ≤ b') (hsep : b < a') :
    Disjoint (brickLeftHook (c := c) (r := r) a b j) (brickLeftHook a' b' j') := by
  apply Finset.disjoint_left.mpr
  intro w hw hw'
  have hh := brickLeftHook_row_bounds hab hw
  have hh' := brickLeftHook_row_bounds hab' hw'
  omega

theorem brickLeftHook_disjoint_nested {a b j a' b' j' : ℕ}
    (ha : a < a') (hab' : a' ≤ b') (hb : b' < b) (hj : j' < j) :
    Disjoint (brickLeftHook (c := c) (r := r) a b j) (brickLeftHook a' b' j') := by
  apply Finset.disjoint_left.mpr
  intro w hw hw'
  rw [mem_brickLeftHook] at hw hw'
  omega

theorem exists_brick_left_hook_path (u v : ElementaryWallVertex c r)
    (huv : u.val.1.val ≤ v.val.1.val) (j : ℕ) (hj : 0 < j) (hjc : j + 1 < c)
    (hu : u.val.2.val ≤ 2 * j + 1) (hv : v.val.2.val ≤ 2 * j + 1) :
    ∃ P : GraphPath (elementaryWall c r), P.source = u ∧ P.target = v ∧
      P.vertexSet ⊆ brickLeftHook u.val.1.val v.val.1.val j := by
  obtain ⟨C, hCs, hCt, hC⟩ := exists_brick_column_path
    u.val.1.val v.val.1.val j huv v.val.1.isLt hj hjc
  have hCscol := (hC C.source C.source_mem_vertexSet).2.2.2
  have hCtcol := (hC C.target C.target_mem_vertexSet).2.2.2
  obtain ⟨L, hLs, hLt, hL⟩ := exists_brick_horizontal_path_bounded u C.source
    (Fin.ext hCs.symm) 0 (2 * j + 1) ⟨Nat.zero_le _, hu⟩ ⟨Nat.zero_le _, hCscol⟩
  obtain ⟨R, hRs, hRt, hR⟩ := exists_brick_horizontal_path_bounded C.target v
    (Fin.ext hCt) 0 (2 * j + 1) ⟨Nat.zero_le _, hCtcol⟩ ⟨Nat.zero_le _, hv⟩
  let P := L.append3WithEqToPath C R hLt hRs.symm
  refine ⟨P, hLs, hRt, ?_⟩
  intro w hw
  have hh := L.append3WithEqToPath_vertexSet_subset C R hLt hRs.symm hw
  rcases mem_union.mp hh with hh | hh
  · rcases mem_union.mp hh with hh | hh
    · exact mem_brickLeftHook.mpr (Or.inl
        ⟨Or.inl (congrArg Fin.val (hL w hh).1), (hL w hh).2.2⟩)
    · exact mem_brickLeftHook.mpr (Or.inr (hC w hh))
  · exact mem_brickLeftHook.mpr (Or.inl
      ⟨Or.inr ((congrArg Fin.val (hR w hh).1).trans hCt), (hR w hh).2.2⟩)

theorem GraphSubdivisionModel.exists_left_hook_path {V : Type*} {G : SimpleGraph V}
    (S : GraphSubdivisionModel (elementaryWall c r) G) (u v : ElementaryWallVertex c r)
    (huv : u.val.1.val ≤ v.val.1.val) (j : ℕ) (hj : 0 < j) (hjc : j + 1 < c)
    (hu : u.val.2.val ≤ 2 * j + 1) (hv : v.val.2.val ≤ 2 * j + 1) :
    ∃ P : GraphPath G, P.source = S.branchVertex u ∧ P.target = S.branchVertex v ∧
      P.vertexSet ⊆ S.supportOver (brickLeftHook u.val.1.val v.val.1.val j) := by
  obtain ⟨Q, hs, ht, hQ⟩ := exists_brick_left_hook_path u v huv j hj hjc hu hv
  obtain ⟨P, hPs, hPt, hP⟩ := S.exists_path_with_walkSupport Q.walk Q.isPath
  refine ⟨P, hPs.trans (congrArg S.branchVertex hs), hPt.trans (congrArg S.branchVertex ht), ?_⟩
  rw [hP]
  apply (S.walkSupport_subset_supportOver Q.walk).trans (S.supportOver_mono ?_)
  simpa only [GraphPath.vertexSet, Finset.subset_iff, List.mem_toFinset] using hQ

end
end Erdos73
