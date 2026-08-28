import ErdosProblems.Erdos577.RawCoreCompletion

/-! An arbitrary exposed first-block vertex and one dense distinguished pair. -/

namespace Erdos577.DenseObstruction

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure PairConfig (c : TriangleChain G) (p : Paw G) (d : Quadrilateral G)
    (s : Finset V) (z : V) : Prop where
  paw : p.support = c.remainder
  first : s ∈ c.blocks
  core : d.support ∈ c.blocks
  different : d.support ≠ s
  exposed : z ∈ s
  pair : WeightedTwelve.DensePair p d
  first_quad : QuadOn G (insert p.leaf (s.erase z))
  first_score : edgeCount G (insert p.leaf (s.erase z)) = edgeCount G s
  second_quad : QuadOn G (insert (p.vertices 2) (s.erase z))

lemma PairConfig.paw_disjoint {c : TriangleChain G} {p : Paw G} {d : Quadrilateral G}
    {s : Finset V} {z : V} (h : PairConfig c p d s z) {a : Finset V} (ha : a ∈ c.blocks) :
    Disjoint p.support a := by
  rw [h.paw]
  exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)

lemma PairConfig.arms_card {c : TriangleChain G} {p : Paw G} {d : Quadrilateral G}
    {s : Finset V} {z : V} (h : PairConfig c p d s z) :
    (JointBridge.arms p z (d 2) (d 3)).card = 4 :=
  JointBridge.arms_card p z (d 2) (d 3) h.pair.disjoint (h.paw_disjoint h.first)
    (c.property.blocks_disjoint h.core h.first h.different) h.exposed
    ((d.mem_support _).mpr ⟨2, rfl⟩) ((d.mem_support _).mpr ⟨3, rfl⟩)
    (d.injective.ne (by decide))

lemma PairConfig.arms_contacts {c : TriangleChain G} {p : Paw G} {d : Quadrilateral G}
    {s : Finset V} {z : V} (h : PairConfig c p d s z) (a : Finset V) :
    contacts G (JointBridge.arms p z (d 2) (d 3)) a =
      degreeIn G p.leaf a + degreeIn G z a + degreeIn G (d 2) a + degreeIn G (d 3) a := by
  obtain ⟨hxz, hx1, hx2, hz1, hz2, h12⟩ := JointCore.four_distinct h.arms_card
  rw [JointBridge.arms, contacts, sum_insert (by simp [hxz, hx1, hx2]),
    sum_insert (by simp [hz1, hz2]), sum_insert (by simp [h12]), sum_singleton]
  omega

theorem PairConfig.leaf_zero {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {d : Quadrilateral G} {s : Finset V} {z : V} (h : PairConfig c p d s z) :
    degreeIn G p.leaf d.support = 0 := by
  have hbound := (c.presentPaw p h.paw).terminal_core_degree_le_one_of_dense_clique
    hcard hn h.core h.pair.complete h.pair.dense
  change degreeIn G p.leaf (p.triangle ∪ d.support) ≤ 1 at hbound
  have hT : Disjoint p.triangle d.support :=
    h.pair.disjoint.mono_left (p.support_eq ▸ subset_insert _ _)
  have hdegree := p.leaf_triangle_degree_eq_one
    (by rw [h.paw]; exact c.no_quad_remainder hcard hn)
  rw [degreeIn_union G p.leaf hT, hdegree] at hbound
  omega

theorem PairConfig.exposed_chain {c : TriangleChain G} (hc : c.Feasible)
    {p : Paw G} {d : Quadrilateral G} {s : Finset V} {z : V} (h : PairConfig c p d s z) :
    ∃ e : TriangleChain G, e.Feasible ∧ e.terminal = z ∧ e.triangle = p.triangle ∧
      e.edgeScore = c.edgeScore ∧ e.completeScore = c.completeScore ∧
      ∀ a ∈ c.blocks, a ≠ s → a ∈ e.blocks :=
  TwoExposed.one_route hc p h.paw h.first z h.exposed h.first_quad h.first_score

end Erdos577.DenseObstruction
