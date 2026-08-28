import ErdosProblems.Erdos577.JointLossGainGeometry

/-! Neither actual terminal permits a triangle and a denser block on the distinguished seven-set. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Core.loss_triangle_edges_le {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hloss : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) < edgeCount G a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (u : V) (hu : u = p.leaf ∨ u = q 3)
    {t b : Finset V} (ht : G.IsNClique 3 t) (hb : QuadOn G b) (htb : Disjoint t b)
    (hcover : t ∪ b = insert u ({d 2, d 3} ∪ j)) :
    edgeCount G b ≤ edgeCount G j := by
  obtain ⟨hp, hs, ha, has, hcase, _, _⟩ := h.config
  have hA : edgeCount G d.support = 6 := by
    rw [h.labels]
    exact (h.loss_scores hloss).1
  have haux : G.IsNClique 4 (insert (d 0) p.triangle) := by
    have he : insert (d 0) p.triangle = {p.center, p.vertices 2, p.vertices 3, d 0} := by
      change insert (d 0) {p.center, p.vertices 2, p.vertices 3} = _
      rw [insert_comm (d 0) p.center, insert_comm (d 0) (p.vertices 2),
        pair_comm (d 0) (p.vertices 3)]
    rw [he]
    exact (h.loss_rows hloss).auxiliary_clique
  have hdj : d.support ≠ j := by rw [h.labels]; exact hja.symm
  rcases hu with rfl | rfl
  · exact pair_triangle_edges_le (hc.presentPaw_feasible p hp) d
      (by rw [h.labels]; exact ha) hj hdj hA haux ht hb htb hcover
  · obtain ⟨e, he, hterm, htri, _, _, _, _, hkeep⟩ := JointClaims.exists_exposed_chain hc
      hcard hn p hp hs q rfl (h.paw_disjoint hs) (Or.inr hcase)
    exact pair_triangle_edges_le he.toFeasible d (by rw [h.labels]; exact hkeep a ha has)
      (hkeep j hj hjq) hdj hA (by rwa [htri]) ht hb htb (by rwa [hterm])

theorem Core.losing_complement {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hloss : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) < edgeCount G a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a) :
    edgeCount G a = 6 ∧ edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) = 5 ∧
      contacts G p.triangle a ≤ 10 ∧ LossRows p d ∧
      (∀ u, u = p.leaf ∨ u = q 3 → ∀ t b : Finset V,
        G.IsNClique 3 t → QuadOn G b → Disjoint t b →
        t ∪ b = insert u ({d 2, d 3} ∪ j) → edgeCount G b ≤ edgeCount G j) ∧
      ¬LocalFactor G (arms p q d ∪ j) ∧
      (∀ u, u = p.leaf ∨ u = q 3 → ∀ v : Quadrilateral G, v.support = j →
        PawBlock.OnlyFirst v →
        (∀ i : Fin 4, G.Adj u (v i) ↔ (9 : ℕ).testBit i.val = true) →
        ∀ z1 z2, (z1 = d 2 ∧ z2 = d 3 ∨ z1 = d 3 ∧ z2 = d 2) →
        (∀ i : Fin 4, i ≠ 3 → G.Adj z1 (v i)) →
        1 ≤ degreeIn G z2 {v 1, v 2} → False) := by
  obtain ⟨hA, hD, hT, _⟩ := h.loss_scores hloss
  refine ⟨hA, hD, hT, h.loss_rows hloss, ?_, h.arms_no_factor hc hcard hn hj hjq hja, ?_⟩
  · intro u hu t b ht hb htb hcover
    exact h.loss_triangle_edges_le hc hcard hn hloss hj hjq hja u hu ht hb htb hcover
  · intro u hu v hv hdiag hrow z1 z2 hpair hz1 hz2
    exact h.loss_low_pattern_false hc hcard hdeg hn hloss hj hjq hja u hu v hv hdiag hrow
      z1 z2 hpair hz1 hz2

end Erdos577.JointFinal
