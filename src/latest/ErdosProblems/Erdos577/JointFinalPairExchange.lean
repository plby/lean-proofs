import ErdosProblems.Erdos577.JointFinalZero

/-! The core-pair triangle and complementary block form an actual local exchange. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def Core.pairPaw {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G} {a : Finset V}
    (h : Core c p q d a) : Paw G :=
  Paw.ofVertices p.leaf p.center (d 2) (d 3) p.pendant.ne
    (fun he ↦ disjoint_left.mp (h.paw_disjoint h.config.2.2.1)
      (p.support_eq ▸ mem_insert_self _ _) (he.symm ▸ h.mem 2))
    (fun he ↦ disjoint_left.mp (h.paw_disjoint h.config.2.2.1)
      (p.support_eq ▸ mem_insert_self _ _) (he.symm ▸ h.mem 3))
    h.center_first.ne h.center_second.ne (d.injective.ne (by decide))
    p.pendant h.center_first h.center_second h.pair_edge

lemma Core.pairPaw_support {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G}
    {a : Finset V} (h : Core c p q d a) :
    h.pairPaw.support = insert p.leaf {p.center, d 2, d 3} := h.pairPaw.support_eq

def Core.pairLocal {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G}
    {a : Finset V} (h : Core c p q d a) : LocalChain G (c.remainder ∪ a) where
  terminal := p.leaf
  triangle := {p.center, d 2, d 3}
  block := (p.triangle ∪ a) \ {p.center, d 2, d 3}
  triangle_clique := h.pairPaw.triangle_clique
  terminal_not_mem := h.pairPaw.leaf_not_mem_triangle
  quad := h.primary
  disjoint := by
    apply disjoint_insert_left.mpr
    refine ⟨?_, sdiff_disjoint.symm⟩
    intro hh
    rcases mem_union.mp (mem_sdiff.mp hh).1 with hh | hh
    · exact p.leaf_not_mem_triangle hh
    · exact disjoint_left.mp (h.paw_disjoint h.config.2.2.1)
        (p.support_eq ▸ mem_insert_self _ _) hh
  cover := by
    have hsub : ({p.center, d 2, d 3} : Finset V) ⊆ p.triangle ∪ a :=
      insert_subset (mem_union_left _ p.center_mem_triangle)
        (insert_subset (mem_union_right _ (h.mem 2))
          (singleton_subset_iff.mpr (mem_union_right _ (h.mem 3))))
    rw [insert_union, union_sdiff_of_subset hsub, ← insert_union, ← p.support_eq, h.config.1]

theorem Core.primary_le_original {c : TriangleChain G} (hc : c.Feasible)
    {p : Paw G} {q d : Quadrilateral G} {a : Finset V} (h : Core c p q d a) :
    edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) ≤ edgeCount G a :=
  hc.local_edges_le h.config.2.2.1 h.pairLocal

theorem Core.exists_equal_pair_chain {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a : Finset V} (h : Core c p q d a)
    (he : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) = edgeCount G a) :
    ∃ e : TriangleChain G, e.Strong ∧ h.pairPaw.support = e.remainder ∧
      e.edgeScore = c.edgeScore ∧ e.completeScore = c.completeScore ∧
      ∀ j ∈ c.blocks, j ≠ a → j ∈ e.blocks := by
  let e := c.replaceBlock a h.config.2.2.1 h.pairLocal
  have hfeasible : e.Feasible := hc.replaceBlock_feasible h.config.2.2.1 h.pairLocal he
  have hstrong : e.Strong := JointBridge.strong_of_center_neighbor hfeasible hcard hn
    h.pairPaw rfl p.pendant.symm
  have hscores := c.replaceBlock_scores_eq h.config.2.2.1 h.pairLocal he
  refine ⟨e, hstrong, h.pairPaw_support, hscores.1, hscores.2, ?_⟩
  intro j hj hja
  exact mem_union_left _ (mem_erase.mpr ⟨hja, hj⟩)

end Erdos577.JointFinal
