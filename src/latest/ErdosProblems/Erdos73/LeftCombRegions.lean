import ErdosProblems.Erdos73.BrickHookRegions
import ErdosProblems.Erdos73.RootedPathUnion

/-! Disjoint connected comb regions joining arbitrary nested blocks of boundary ports. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {c r : ℕ}

def brickLeftComb (rows : Finset ℕ) (a b j : ℕ) : Finset (ElementaryWallVertex c r) :=
  univ.filter (fun w => (w.val.1.val ∈ rows ∧ w.val.2.val ≤ 2 * j + 1) ∨
    (a ≤ w.val.1.val ∧ w.val.1.val ≤ b ∧ 2 * j ≤ w.val.2.val ∧ w.val.2.val ≤ 2 * j + 1))

theorem mem_brickLeftComb {rows : Finset ℕ} {a b j : ℕ} {w : ElementaryWallVertex c r} :
    w ∈ brickLeftComb rows a b j ↔ (w.val.1.val ∈ rows ∧ w.val.2.val ≤ 2 * j + 1) ∨
      (a ≤ w.val.1.val ∧ w.val.1.val ≤ b ∧ 2 * j ≤ w.val.2.val ∧ w.val.2.val ≤ 2 * j + 1) := by
  simp only [brickLeftComb, mem_filter, mem_univ, true_and]

theorem brickLeftComb_bounds {rows : Finset ℕ} {a b j : ℕ}
    (hrows : ∀ i ∈ rows, a ≤ i ∧ i ≤ b) {w : ElementaryWallVertex c r}
    (hw : w ∈ brickLeftComb rows a b j) :
    a ≤ w.val.1.val ∧ w.val.1.val ≤ b ∧ w.val.2.val ≤ 2 * j + 1 := by
  rcases mem_brickLeftComb.mp hw with hh | hh
  · exact ⟨(hrows _ hh.1).1, (hrows _ hh.1).2, hh.2⟩
  · exact ⟨hh.1, hh.2.1, hh.2.2.2⟩

theorem brickLeftComb_disjoint_series {rows rows' : Finset ℕ} {a b j a' b' j' : ℕ}
    (hrows : ∀ i ∈ rows, a ≤ i ∧ i ≤ b) (hrows' : ∀ i ∈ rows', a' ≤ i ∧ i ≤ b')
    (hsep : b < a') :
    Disjoint (brickLeftComb (c := c) (r := r) rows a b j) (brickLeftComb rows' a' b' j') := by
  apply Finset.disjoint_left.mpr
  intro w hw hw'
  have hh := brickLeftComb_bounds hrows hw
  have hh' := brickLeftComb_bounds hrows' hw'
  omega

theorem brickLeftComb_disjoint_nested {rows rows' : Finset ℕ} {a b j a' b' j' : ℕ}
    (hrows' : ∀ i ∈ rows', a' ≤ i ∧ i ≤ b') (hj : j' < j)
    (havoid : ∀ i ∈ rows, ¬ (a' ≤ i ∧ i ≤ b')) :
    Disjoint (brickLeftComb (c := c) (r := r) rows a b j) (brickLeftComb rows' a' b' j') := by
  apply Finset.disjoint_left.mpr
  intro w hw hw'
  have hh' := brickLeftComb_bounds hrows' hw'
  rcases mem_brickLeftComb.mp hw with hh | hh
  · exact havoid _ hh.1 ⟨hh'.1, hh'.2.1⟩
  · omega

theorem brickLeftHook_subset_comb {rows : Finset ℕ} {a b s j : ℕ}
    (ha : a ∈ rows) (hs : s ∈ rows) (hsb : s ≤ b) :
    brickLeftHook (c := c) (r := r) a s j ⊆ brickLeftComb rows a b j := by
  intro w hw
  rcases mem_brickLeftHook.mp hw with ⟨hr, hc⟩ | hh
  · apply mem_brickLeftComb.mpr
    apply Or.inl
    refine ⟨?_, hc⟩
    rcases hr with hr | hr
    · exact hr ▸ ha
    · exact hr ▸ hs
  · exact mem_brickLeftComb.mpr (Or.inr ⟨hh.1, hh.2.1.trans hsb, hh.2.2⟩)

theorem exists_connected_leftComb_region {I : Type*} [Fintype I]
    (root : ElementaryWallVertex c r) (ports : I → ElementaryWallVertex c r)
    (rows : Finset ℕ) (b j : ℕ) (hj : 0 < j) (hjc : j + 1 < c)
    (hroot : root.val.1.val ∈ rows) (hrootcol : root.val.2.val ≤ 2 * j + 1)
    (hrows : ∀ i, (ports i).val.1.val ∈ rows)
    (horder : ∀ i, root.val.1.val ≤ (ports i).val.1.val)
    (hbound : ∀ i, (ports i).val.1.val ≤ b)
    (hcols : ∀ i, (ports i).val.2.val ≤ 2 * j + 1) :
    ∃ T : Finset (ElementaryWallVertex c r), root ∈ T ∧ (∀ i, ports i ∈ T) ∧
      T ⊆ brickLeftComb rows root.val.1.val b j ∧
      ((elementaryWall c r).induce (T : Set (ElementaryWallVertex c r))).Connected := by
  have hex (i : I) := exists_brick_left_hook_path root (ports i) (horder i) j hj hjc hrootcol (hcols i)
  choose P hPs hPt hP using hex
  let T := insert root (univ.biUnion (fun i => (P i).vertexSet))
  refine ⟨T, mem_insert_self _ _, ?_, ?_, ?_⟩
  · intro i
    exact mem_insert_of_mem (mem_biUnion.mpr ⟨i, mem_univ _, hPt i ▸ (P i).target_mem_vertexSet⟩)
  · intro w hw
    rcases mem_insert.mp hw with rfl | hw
    · exact mem_brickLeftComb.mpr (Or.inl ⟨hroot, hrootcol⟩)
    · obtain ⟨i, _, hwi⟩ := mem_biUnion.mp hw
      apply brickLeftHook_subset_comb hroot (hrows i) (hbound i)
      apply hP i
      simpa only [GraphPath.vertexSet, List.mem_toFinset] using hwi
  · exact connected_induce_rooted_pathUnion univ P root (fun i _ => hPs i)

end
end Erdos73
