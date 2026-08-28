import ErdosProblems.Erdos577.WeightedTwelveCore

/-! The dense-pair triangle and complete complement form an actual score-preserving exchange. -/

namespace Erdos577.WeightedTwelve

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def DensePair.pairLocal {p : Paw G} {d : Quadrilateral G} (h : DensePair p d) :
    LocalChain G (p.support ∪ d.support) where
  terminal := p.leaf
  triangle := {p.center, d 2, d 3}
  block := (p.triangle ∪ d.support) \ {p.center, d 2, d 3}
  triangle_clique := h.pairPaw.triangle_clique
  terminal_not_mem := h.pairPaw.leaf_not_mem_triangle
  quad := QuadOn.of_clique h.primary.card_eq h.primary.isClique
  disjoint := by
    apply disjoint_insert_left.mpr
    refine ⟨?_, sdiff_disjoint.symm⟩
    intro hh
    rcases mem_union.mp (mem_sdiff.mp hh).1 with hh | hh
    · exact p.leaf_not_mem_triangle hh
    · exact disjoint_left.mp h.disjoint (p.support_eq ▸ mem_insert_self _ _) hh
  cover := by
    have hsub : ({p.center, d 2, d 3} : Finset V) ⊆ p.triangle ∪ d.support :=
      insert_subset (mem_union_left _ p.center_mem_triangle)
        (insert_subset (mem_union_right _ ((d.mem_support _).mpr ⟨2, rfl⟩))
          (singleton_subset_iff.mpr (mem_union_right _ ((d.mem_support _).mpr ⟨3, rfl⟩))))
    rw [insert_union, union_sdiff_of_subset hsub, ← insert_union, ← p.support_eq]

variable [Fintype V]

theorem DensePair.exists_pair_chain {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) (d : Quadrilateral G)
    (hd : d.support ∈ c.blocks) (h : DensePair p d) :
    ∃ e : TriangleChain G, e.Strong ∧ e.terminal = p.leaf ∧ e.triangle = h.pairPaw.triangle ∧
      h.pairPaw.support = e.remainder ∧ e.edgeScore = c.edgeScore ∧
      e.completeScore = c.completeScore ∧
      e.blocks = c.blocks.erase d.support ∪ {h.pairLocal.block} ∧
      ∀ j ∈ c.blocks, j ≠ d.support → j ∈ e.blocks := by
  let l : LocalChain G (c.remainder ∪ d.support) := h.pairLocal.withSupport (by rw [hp])
  have heq : edgeCount G l.block = edgeCount G d.support := by
    change edgeCount G ((p.triangle ∪ d.support) \ {p.center, d 2, d 3}) = _
    rw [edgeCount_clique h.primary.isClique, edgeCount_clique h.complete.isClique,
      h.primary.card_eq, h.complete.card_eq]
  let e := c.replaceBlock d.support hd l
  have hfeasible : e.Feasible := hc.replaceBlock_feasible hd l heq
  have hstrong : e.Strong := JointBridge.strong_of_center_neighbor hfeasible hcard hn
    h.pairPaw rfl p.pendant.symm
  have hscores := c.replaceBlock_scores_eq hd l heq
  refine ⟨e, hstrong, rfl, rfl, h.pairPaw_support, hscores.1, hscores.2, rfl, ?_⟩
  intro j hj hja
  exact mem_union_left _ (mem_erase.mpr ⟨hja, hj⟩)

end Erdos577.WeightedTwelve
