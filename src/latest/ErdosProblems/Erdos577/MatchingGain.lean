import ErdosProblems.Erdos577.MatchingExchange

/-! Positive matching remainders and the exclusion of a two-edge local gain. -/

namespace Erdos577

open Finset

variable {V W : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableRel G.Adj] in
lemma TwoEdges.image_support [DecidableEq W] {H : SimpleGraph W}
    (p : TwoEdges G) (f : G.Copy H) : (p.image f).support = p.support.image f := by
  rw [TwoEdges.support, TwoEdges.support, tupleSupport, tupleSupport, image_image]
  rfl

/-- A two-edge remainder and a quadrilateral partition the local set, with
an explicit lower bound on the quadrilateral's induced-edge count. -/
def TwoEdgeReduction (G : SimpleGraph V) [DecidableRel G.Adj]
    (s : Finset V) (minEdges : ℕ) : Prop :=
  ∃ p : TwoEdges G, p.support ⊆ s ∧ QuadOn G (s \ p.support) ∧
    minEdges ≤ edgeCount G (s \ p.support)

lemma TwoEdgeReduction.image [DecidableEq W] {H : SimpleGraph W} [DecidableRel H.Adj]
    {s : Finset V} {minEdges : ℕ} (h : TwoEdgeReduction G s minEdges) (f : G.Copy H) :
    TwoEdgeReduction H (s.image f) minEdges := by
  obtain ⟨p, hp, hq, he⟩ := h
  have hinj : Function.Injective (f : V → W) := f.injective
  have hdiff : (s \ p.support).image f = s.image f \ (p.image f).support := by
    rw [p.image_support, image_sdiff s p.support hinj]
  refine ⟨p.image f, ?_, ?_, ?_⟩
  · rw [p.image_support]
    exact image_subset_image hp
  · have h := hq.image f
    rw [hdiff] at h
    exact h
  · have h := he.trans (edgeCount_image_le f (s \ p.support))
    rw [hdiff] at h
    exact h

lemma TriangleChain.Feasible.no_two_edge_gain [Fintype V]
    {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v)
    (hn : ¬HasPacking G k) {b : Finset V} (hb : b ∈ c.blocks) :
    ¬TwoEdgeReduction G (c.remainder ∪ b) (edgeCount G b + 2) := by
  rintro ⟨p, hp, hq, he⟩
  let parts := c.complementPartition.replaceRemainder b hb p.support hp hq
  have hbound := hc.matching_score_bound hcard hdeg hn p parts
  have hid := c.complementPartition.weightSum_replaceRemainder_add
    b hb p.support hp hq (edgeCount G)
  change parts.weightSum (edgeCount G) + edgeCount G b =
    c.edgeScore + edgeCount G ((c.remainder ∪ b) \ p.support) at hid
  omega

end Erdos577
