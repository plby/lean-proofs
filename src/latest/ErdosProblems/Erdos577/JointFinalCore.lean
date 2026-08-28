import ErdosProblems.Erdos577.JointMaximalDenseCore

/-! Proven core data for the final local argument.
The optional pattern28 normalization is not required. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure Core (c : TriangleChain G) (p : Paw G) (q d : Quadrilateral G) (a : Finset V) : Prop where
  maximal : JointClaims.MaximalCore c p q a
  labels : d.support = a
  center_first : G.Adj p.center (d 2)
  center_second : G.Adj p.center (d 3)
  pair_edge : G.Adj (d 2) (d 3)
  leaf_zero : degreeIn G p.leaf a = 0
  last_zero : degreeIn G (q 3) a = 0
  third_replacement : ∀ v ∈ a, QuadOn G (insert (p.vertices 3) (a.erase v))
  primary : QuadOn G ((p.triangle ∪ a) \ {p.center, d 2, d 3})
  primary_edges : 5 ≤ edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3})
  secondary_first : QuadOn G ((p.triangle ∪ a) \ {d 2, p.center, p.vertices 2})
  secondary_second : QuadOn G ((p.triangle ∪ a) \ {d 3, p.center, p.vertices 2})
  tertiary : QuadOn G ((p.triangle ∪ a) \ {d 2, d 3, p.vertices 2})
  outside_factor : ∀ u, u ∉ p.triangle ∪ a → 2 ≤ degreeIn G u (p.triangle ∪ a) →
    LocalFactor G (insert u (p.triangle ∪ a))
  first_zero : degreeIn G (d 2) q.support = 0
  second_zero : degreeIn G (d 3) q.support = 0
  inside_three : contacts G {p.leaf, d 2, d 3} (p.support ∪ q.support ∪ a) ≤ 17
  inside_four : contacts G {p.leaf, d 2, d 3, q 3} (p.support ∪ q.support ∪ a) ≤ 22
  high : 11 ≤ contacts G p.triangle a →
    G.IsNClique 4 ((p.triangle ∪ a) \ {p.center, d 2, d 3})
  low : contacts G p.triangle a ≤ 10 → ∃ tag : Fin 8, JointCore.RefinedSourcePattern tag p d

theorem exists_core {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (q : Quadrilateral G) {a : Finset V} (hmax : JointClaims.MaximalCore c p q a) :
    ∃ d : Quadrilateral G, Core c p q d a := by
  obtain ⟨hx, hy, d, hd, _, hr1, hr2, hz, hrep, hprimary, hpe, hs1, hs2, ht, hfactor,
      hz1, hz2, h17, h22, hhigh, hlow⟩ :=
    JointClaims.maximal_dense_seven_vertex_core hc hcard hdeg hn p q hmax
  refine ⟨d, hmax, hd, hr1, hr2, hz, hx, hy, hrep, hprimary, hpe, hs1, hs2, ht,
    hfactor, hz1, hz2, h17, h22, hhigh, ?_⟩
  intro hh
  obtain ⟨tag, hpat, _⟩ := hlow hh
  exact ⟨tag, hpat⟩

lemma Core.config {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G} {a : Finset V}
    (h : Core c p q d a) : JointClaims.CaseTwoCore c p q a := h.maximal.1

lemma Core.mem {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G} {a : Finset V}
    (h : Core c p q d a) (i : Fin 4) : d i ∈ a :=
  h.labels ▸ (d.mem_support _).mpr ⟨i, rfl⟩

lemma Core.paw_disjoint {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G} {a : Finset V}
    (h : Core c p q d a) {s : Finset V} (hs : s ∈ c.blocks) : Disjoint p.support s := by
  rw [h.config.1]
  exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)

lemma Core.core_disjoint {c : TriangleChain G} {p : Paw G} {q d : Quadrilateral G} {a : Finset V}
    (h : Core c p q d a) {s : Finset V} (hs : s ∈ c.blocks) (has : a ≠ s) :
    Disjoint (p.triangle ∪ a) s :=
  disjoint_union_left.mpr ⟨(h.paw_disjoint hs).mono_left (p.support_eq ▸ subset_insert _ _),
    c.property.blocks_disjoint h.config.2.2.1 hs has⟩

end Erdos577.JointFinal
