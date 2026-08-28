import ErdosProblems.Erdos577.JointThreeDiagonal

/-! All local loss restrictions, constructed from the proved core and the actual chains. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

structure FinalRows (v : Quadrilateral G) (x y z w : V) : Prop extends PairRows v x y z w where
  distinct : ({x, y, z, w} : Finset V).card = 4
  pair_edge : G.Adj z w
  no_high_x : ¬(G.Adj x (v 0) ∧ G.Adj x (v 2))
  no_high_y : ¬(G.Adj y (v 0) ∧ G.Adj y (v 2))
  gain : ∀ u, u = x ∨ u = y → ∀ t b : Finset V,
    G.IsNClique 3 t → QuadOn G b → Disjoint t b →
    t ∪ b = insert u ({z, w} ∪ v.support) → edgeCount G b ≤ edgeCount G v.support
  factor : ¬LocalFactor G ({x, y, z, w} ∪ v.support)
  low : ∀ u, u = x ∨ u = y → ∀ q : Quadrilateral G, q.support = v.support →
    PawBlock.OnlyFirst q →
    (∀ i : Fin 4, G.Adj u (q i) ↔ (9 : ℕ).testBit i.val = true) →
    ∀ s t, (s = z ∧ t = w ∨ s = w ∧ t = z) →
    (∀ i : Fin 4, i ≠ 3 → G.Adj s (q i)) → 1 ≤ degreeIn G t {q 1, q 2} → False

omit [DecidableEq V] in
lemma pair_order_trans {a b c d e f : V}
    (h : a = c ∧ b = d ∨ a = d ∧ b = c)
    (h' : c = e ∧ d = f ∨ c = f ∧ d = e) :
    a = e ∧ b = f ∨ a = f ∧ b = e := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h'
  · rcases h' with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl ⟨rfl, rfl⟩

lemma FinalRows.terminal_data {v : Quadrilateral G} {x y z w : V} (h : FinalRows v x y z w)
    (u : V) (hu : u = x ∨ u = y) :
    u ≠ z ∧ u ≠ w ∧ u ∉ v.support ∧ degreeIn G u v.support ≤ 2 := by
  obtain ⟨_, hxz, hxw, hyz, hyw, _⟩ := JointCore.four_distinct h.distinct
  rcases hu with rfl | rfl
  · exact ⟨hxz, hxw, h.x_out, h.x_bound⟩
  · exact ⟨hyz, hyw, h.y_out, h.y_bound⟩

variable [Fintype V]

theorem Core.final_rows {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hloss : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) < edgeCount G a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (hnine : 9 ≤ contacts G (arms p q d) j) (hpos : 1 ≤ degreeIn G p.leaf j)
    (v : Quadrilateral G) (hv : v.support = j) (z w : V)
    (hpair : z = d 2 ∧ w = d 3 ∨ z = d 3 ∧ w = d 2)
    (hthree : ∀ i : Fin 4, i ≠ 3 → G.Adj z (v i)) : FinalRows v p.leaf (q 3) z w := by
  have hrows := h.pair_rows hc hcard hdeg hn hj hjq hja hnine hpos v hv z w hpair hthree
  have hb := h.opposite_pair_bounds hc hcard hdeg hn hj hjq hja hnine hpos v hv z w hpair hthree
  have hpairSet : ({z, w} : Finset V) = {d 2, d 3} := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · rfl
    · exact pair_comm _ _
  have hset : ({p.leaf, q 3, z, w} : Finset V) = arms p q d := by
    change insert p.leaf (insert (q 3) {z, w}) = insert p.leaf (insert (q 3) {d 2, d 3})
    rw [hpairSet]
  refine { toPairRows := hrows
           distinct := ?_
           pair_edge := ?_
           no_high_x := ?_
           no_high_y := ?_
           gain := ?_
           factor := ?_
           low := ?_ }
  · rw [hset]
    exact h.arms_card
  · rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h.pair_edge
    · exact h.pair_edge.symm
  · exact (degree_pair_le_one_iff p.leaf (v 0) (v 2) (v.injective.ne (by decide))).mp hb.1
  · exact (degree_pair_le_one_iff (q 3) (v 0) (v 2) (v.injective.ne (by decide))).mp hb.2.2.1
  · intro u hu t b ht hquad htb hcover
    rw [hpairSet, hv] at hcover
    rw [hv]
    exact h.loss_triangle_edges_le hc hcard hn hloss hj hjq hja u hu ht hquad htb hcover
  · rw [hset, hv]
    exact h.arms_no_factor hc hcard hn hj hjq hja
  · intro u hu v' hv' hdiag hrow s t hst hs ht
    exact h.loss_low_pattern_false hc hcard hdeg hn hloss hj hjq hja u hu v' (hv'.trans hv)
      hdiag hrow s t (pair_order_trans hst hpair) hs ht

end Erdos577.JointFinal
