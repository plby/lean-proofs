import ErdosProblems.Erdos577.WeightedTwelveCoreExchange

/-! The actual configuration produced from pattern12, with all dense-core premises proved. -/

namespace Erdos577.WeightedTwelve

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure Configuration (c : TriangleChain G) (p : Paw G) (q d : Quadrilateral G) : Prop where
  paw : p.support = c.remainder
  first : q.support ∈ c.blocks
  core : d.support ∈ c.blocks
  different : d.support ≠ q.support
  pattern : WeightedPawBlock.Pattern12 p q
  pair : DensePair p d
  leaf_zero : degreeIn G p.leaf d.support = 0
  cross_zero : ∀ u ∈ q.support, degreeIn G u d.support = 0

theorem exists_configuration {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (q : Quadrilateral G) (hq : q.support = s) (h : WeightedPawBlock.Pattern12 p q) :
    ∃ d : Quadrilateral G, Configuration c p q d := by
  obtain ⟨a, ha, has, hweight⟩ := exists_heavy_block hc hcard hdeg hn p hp hs q hq h
  obtain ⟨hx, _, hT, hcl⟩ := heavy_block_dense hc hcard hdeg hn p hp hs ha has q hq h hweight
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  obtain ⟨d, hd, hpair⟩ := exists_dense_pair p hcl hFA hT
  refine ⟨d, ⟨hp, ?_, ?_, ?_, h, hpair, ?_, ?_⟩⟩
  · rwa [hq]
  · rwa [hd]
  · rwa [hd, hq]
  · rwa [hd]
  · rw [hd]
    exact first_core_zero hc hcard hn p hp hs ha has q hq h hT hcl

lemma Configuration.paw_disjoint {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G}
    (h : Configuration c p q d) {s : Finset V} (hs : s ∈ c.blocks) : Disjoint p.support s := by
  rw [h.paw]
  exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)

lemma Configuration.arms_card {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G}
    (h : Configuration c p q d) : (JointFinal.arms p q d).card = 4 :=
  JointBridge.arms_card p (q 3) (d 2) (d 3) h.pair.disjoint (h.paw_disjoint h.first)
    (c.property.blocks_disjoint h.core h.first h.different) ((q.mem_support _).mpr ⟨3, rfl⟩)
    ((d.mem_support _).mpr ⟨2, rfl⟩) ((d.mem_support _).mpr ⟨3, rfl⟩)
    (d.injective.ne (by decide))

lemma Configuration.arms_contacts {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G}
    (h : Configuration c p q d) (s : Finset V) : contacts G (JointFinal.arms p q d) s =
    degreeIn G p.leaf s + degreeIn G (q 3) s + degreeIn G (d 2) s + degreeIn G (d 3) s := by
  obtain ⟨hxy, hx1, hx2, hy1, hy2, h12⟩ := JointCore.four_distinct h.arms_card
  rw [JointFinal.arms, contacts, sum_insert (by simp [hxy, hx1, hx2]),
    sum_insert (by simp [hy1, hy2]), sum_insert (by simp [h12]), sum_singleton]
  omega

end Erdos577.WeightedTwelve
