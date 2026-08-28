import ErdosProblems.Erdos577.FullLeafCoreScore

/-! An actual strong chain exchanges the two marked vertices and the two centers. -/

namespace Erdos577.FullLeafCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
variable {c : TriangleChain G} {p : Paw G} {s a : Finset V} {y : V}

theorem Configuration.swapped_chain (h : Configuration c p s a y) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k) :
    ∃ (e : TriangleChain G) (p' : Paw G),
      Configuration e p' (insert p.leaf (s.erase y)) a p.leaf ∧ e.Strong ∧
      p'.leaf = y ∧ p'.center = p.vertices 2 ∧ p'.vertices 2 = p.center ∧
      p'.vertices 3 = p.vertices 3 ∧ p'.triangle = p.triangle ∧
      e.edgeScore = c.edgeScore ∧ e.completeScore = c.completeScore ∧
      e.blocks = c.blocks.erase s ∪ {insert p.leaf (s.erase y)} ∧
      contacts G (insert (p'.vertices 3) a) (insert p.leaf (s.erase y)) =
        contacts G (insert (p.vertices 3) a) s := by
  have hyout : y ∉ p.support := fun hh ↦ disjoint_left.mp (h.paw_disjoint h.first) hh h.exposed
  let p' := JointClaims.secondPaw p y hyout h.attached
  obtain ⟨e, he, ht, hT, hedge, hcomplete, hblocks⟩ :=
    FullRow.exists_full_leaf_swap h.feasible p h.paw h.first h.full y h.exposed
  have hp' : p'.support = e.remainder := by
    rw [JointClaims.secondPaw_support]
    change insert y p.triangle = insert e.terminal e.triangle
    rw [ht, hT]
  have hs' : insert p.leaf (s.erase y) ∈ e.blocks := by
    rw [hblocks]
    exact mem_union_right _ (mem_singleton_self _)
  have ha' : a ∈ e.blocks := by
    rw [hblocks]
    exact mem_union_left _ (mem_erase.mpr ⟨h.different, h.core⟩)
  have hxa : p.leaf ∉ a := fun hh ↦ disjoint_left.mp (h.paw_disjoint h.core)
    (p.support_eq ▸ mem_insert_self _ _) hh
  have has' : a ≠ insert p.leaf (s.erase y) := by
    intro hh
    exact hxa (hh.symm ▸ mem_insert_self _ _)
  have hyfirst : y ∈ insert p.leaf s := mem_insert_of_mem h.exposed
  have hcl := h.first_five_clique
  have hrow := degreeIn_clique G hcl.isClique hyfirst
  have hfull' : degreeIn G p'.leaf (insert p.leaf (s.erase y)) = 4 := by
    change degreeIn G y (insert p.leaf (s.erase y)) = 4
    have hyl : y ≠ p.leaf := fun hh ↦ h.leaf_out (hh ▸ h.exposed)
    rw [← erase_insert_of_ne hyl.symm, degreeIn_erase_self G y hyfirst, hrow, hcl.card_eq]
  have hbound := e.terminal_degree_le_one hcard hn
  rw [ht, hT] at hbound
  have hpos : 0 < degreeIn G y p.triangle := card_pos.mpr
    ⟨p.vertices 2, mem_filter.mpr ⟨by simp [Paw.triangle], h.attached.symm⟩⟩
  have hstrong : e.Strong := by
    refine ⟨he, ?_⟩
    change degreeIn G e.terminal e.triangle = 1
    rw [ht, hT]
    omega
  have hconfig : Configuration e p' (insert p.leaf (s.erase y)) a p.leaf := by
    refine ⟨he, hp', hs', ha', has', hfull', mem_insert_self _ _, ?_, ?_⟩
    · exact p.pendant.symm
    · simpa only [p', JointClaims.secondPaw_triangle] using h.dense
  exact ⟨e, p', hconfig, hstrong, rfl, rfl, rfl, rfl,
    JointClaims.secondPaw_triangle p y hyout h.attached, hedge, hcomplete, hblocks,
    h.objective_swap hcard hn⟩

end Erdos577.FullLeafCore
