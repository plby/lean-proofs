import ErdosProblems.Erdos577.PathClassification

/-! An improved block exposes a path at the upper score, with all local restrictions proved. -/

namespace Erdos577.TriangleChain

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def pathPartition (c : TriangleChain G) {b : Finset V} (hb : b ∈ c.blocks)
    (p : FourPath G) (hp : p.support ⊆ c.remainder ∪ b)
    (hq : QuadOn G ((c.remainder ∪ b) \ p.support)) :
    BlockPartition G (univ \ p.support) :=
  c.complementPartition.replaceRemainder b hb p.support hp hq

lemma pathPartition_keeps (c : TriangleChain G) {b : Finset V} (hb : b ∈ c.blocks)
    (p : FourPath G) (hp : p.support ⊆ c.remainder ∪ b)
    (hq : QuadOn G ((c.remainder ∪ b) \ p.support))
    {a : Finset V} (ha : a ∈ c.blocks) (hne : a ≠ b) :
    a ∈ (c.pathPartition hb p hp hq).blocks :=
  mem_union_left _ (mem_erase.mpr ⟨hne, ha⟩)

variable [DecidableRel G.Adj]

lemma pathPartition_score_add (c : TriangleChain G) {b : Finset V} (hb : b ∈ c.blocks)
    (p : FourPath G) (hp : p.support ⊆ c.remainder ∪ b)
    (hq : QuadOn G ((c.remainder ∪ b) \ p.support)) :
    (c.pathPartition hb p hp hq).weightSum (edgeCount G) + edgeCount G b =
      c.edgeScore + edgeCount G ((c.remainder ∪ b) \ p.support) :=
  c.complementPartition.weightSum_replaceRemainder_add b hb p.support hp hq (edgeCount G)

lemma Feasible.improved_path_score {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) {b : Finset V} (hb : b ∈ c.blocks)
    (p : FourPath G) (hp : p.support ⊆ c.remainder ∪ b)
    (hq : QuadOn G ((c.remainder ∪ b) \ p.support))
    (hgain : edgeCount G b < edgeCount G ((c.remainder ∪ b) \ p.support)) :
    edgeCount G ((c.remainder ∪ b) \ p.support) = edgeCount G b + 1 ∧
      (c.pathPartition hb p hp hq).weightSum (edgeCount G) = c.edgeScore + 1 := by
  have hid := c.pathPartition_score_add hb p hp hq
  have hbound := (hc.path_score_bound hcard hdeg hn p (c.pathPartition hb p hp hq)).1
  omega

lemma Feasible.classification_at_path_upper_score {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) (p : FourPath G) (parts : BlockPartition G (univ \ p.support))
    (hscore : parts.weightSum (edgeCount G) = c.edgeScore + 1)
    {b : Finset V} (hb : b ∈ parts.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hheavy : 9 ≤ contacts G p.support q.support) :
    G.IsNClique 4 q.support ∧ PathBlock.Classified p q ∧
      TriangleReduction G (p.support ∪ q.support) 5 := by
  have hd : Disjoint p.support q.support := by
    rw [hq]
    apply disjoint_left.mpr
    intro v hv hvb
    exact (mem_sdiff.mp (parts.block_subset hb hvb)).2 hv
  have hnlocal : ¬LocalFactor G (p.support ∪ q.support) := by
    rw [hq]
    exact fun h ↦ hn (parts.hasPacking_of_local_factor hcard hb h)
  have hopt : ¬PathReduction G (p.support ∪ q.support) (edgeCount G q.support + 1) := by
    rw [hq]
    exact hc.no_path_improvement hcard hdeg hn p parts hscore hb
  rcases path_block_classification p q hd hheavy hnlocal hopt with ht | hclass
  · rw [hq] at ht
    exact False.elim (hc.no_triangle_tie_at_path_upper_score p parts hscore hb ht)
  · exact hclass

/-- The full local restrictions beside every other old block after one strict path gain. -/
lemma Feasible.improved_path_transfer {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) {b : Finset V} (hb : b ∈ c.blocks)
    (p : FourPath G) (hp : p.support ⊆ c.remainder ∪ b)
    (hq : QuadOn G ((c.remainder ∪ b) \ p.support))
    (hgain : edgeCount G b < edgeCount G ((c.remainder ∪ b) \ p.support))
    {a : Finset V} (ha : a ∈ c.blocks) (hne : a ≠ b) :
    ¬LocalFactor G (p.support ∪ a) ∧
      ¬TriangleReduction G (p.support ∪ a) (edgeCount G a) ∧
      ¬PathReduction G (p.support ∪ a) (edgeCount G a + 1) ∧
      ∀ q : Quadrilateral G, q.support = a → 9 ≤ contacts G p.support q.support →
        G.IsNClique 4 q.support ∧ PathBlock.Classified p q ∧
          TriangleReduction G (p.support ∪ q.support) 5 := by
  let parts := c.pathPartition hb p hp hq
  have hscore := (hc.improved_path_score hcard hdeg hn hb p hp hq hgain).2
  have ha' : a ∈ parts.blocks := c.pathPartition_keeps hb p hp hq ha hne
  refine ⟨?_, hc.no_triangle_tie_at_path_upper_score p parts hscore ha',
    hc.no_path_improvement hcard hdeg hn p parts hscore ha', ?_⟩
  · exact fun h ↦ hn (parts.hasPacking_of_local_factor hcard ha' h)
  · intro q hqa hheavy
    exact hc.classification_at_path_upper_score hcard hdeg hn p parts hscore ha' q hqa hheavy

end Erdos577.TriangleChain
