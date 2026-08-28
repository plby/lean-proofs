import ErdosProblems.Erdos577.PawInduced
import ErdosProblems.Erdos577.TerminalReplacements

/-! Present a given paw as the remainder, and exchange its leaf with a block vertex. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

def Paw.replaceLeafLocalChain (p : Paw G) (q : Quadrilateral G)
    (hd : Disjoint p.support q.support) (u : V) (hu : u ∈ q.support)
    (hq : QuadOn G (insert p.leaf (q.support.erase u))) :
    LocalChain G (p.support ∪ q.support) where
  terminal := u
  triangle := p.triangle
  block := insert p.leaf (q.support.erase u)
  triangle_clique := p.triangle_clique
  terminal_not_mem := by
    intro ht
    exact disjoint_left.mp hd (p.support_eq ▸ mem_insert_of_mem ht) hu
  quad := hq
  disjoint := by
    apply disjoint_left.mpr
    intro w hw hnew
    rcases mem_insert.mp hnew with rfl | hnew
    · rcases mem_insert.mp hw with he | ht
      · exact disjoint_left.mp hd (p.support_eq ▸ mem_insert_self _ _) (he.symm ▸ hu)
      · exact p.leaf_not_mem_triangle ht
    · rcases mem_insert.mp hw with rfl | ht
      · exact (mem_erase.mp hnew).1 rfl
      · exact disjoint_left.mp hd (p.support_eq ▸ mem_insert_of_mem ht) (mem_erase.mp hnew).2
  cover := by
    rw [p.support_eq]
    ext w
    have hm : w = u → w ∈ q.support := fun he ↦ he.symm ▸ hu
    simp only [mem_union, mem_insert, mem_erase]
    tauto

namespace TriangleChain

variable [Fintype V]

def presentPaw (c : TriangleChain G) (p : Paw G) (hp : p.support = c.remainder) : TriangleChain G :=
  ofPartition p.triangle_clique p.leaf_not_mem_triangle {
    blocks := c.blocks
    disjoint := c.property.blocks_disjoint
    cover := by rw [← p.support_eq, hp]; exact c.complementPartition.cover
    quad := c.property.blocks_quad }

variable [DecidableRel G.Adj]

lemma Feasible.presentPaw_feasible {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder) : (c.presentPaw p hp).Feasible := by
  constructor
  · exact hc.edge_max
  · exact hc.complete_max

lemma Feasible.presentPaw_strong {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) : (c.presentPaw p hp).Strong := by
  refine ⟨hc.presentPaw_feasible p hp, ?_⟩
  exact p.leaf_triangle_degree_eq_one (by rw [hp]; exact c.no_quad_remainder hcard hn)

end TriangleChain

end Erdos577
