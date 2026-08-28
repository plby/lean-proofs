import ErdosProblems.Erdos577.JointLossRows
import ErdosProblems.Erdos577.TwoCoreObstruction
import ErdosProblems.Erdos577.TwoCoreCompleteObstruction

/-! The low diagonal pattern is excluded for either terminal and either core-pair order. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Core.loss_old_low_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hloss : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) < edgeCount G a)
    (hj : j ∈ c.blocks) (hja : j ≠ a) (v : Quadrilateral G) (hv : v.support = j)
    (hdiag : PawBlock.OnlyFirst v)
    (hrow : ∀ i : Fin 4, G.Adj p.leaf (v i) ↔ (9 : ℕ).testBit i.val = true)
    (z1 z2 : V) (hpair : z1 = d 2 ∧ z2 = d 3 ∨ z1 = d 3 ∧ z2 = d 2)
    (hz1 : ∀ i : Fin 4, i ≠ 3 → G.Adj z1 (v i))
    (hz2 : 1 ≤ degreeIn G z2 {v 1, v 2}) : False := by
  have hrows := h.loss_rows hloss
  have hfull : degreeIn G (p.vertices 3) a = 4 := by
    rw [← h.labels]
    exact hrows.third_full
  have hbound : contacts G {p.center, p.vertices 2} a ≤ 6 := by
    rw [← h.labels]
    exact hrows.pair_bound
  have hdata : z1 ∈ a ∧ z2 ∈ a ∧ z1 ≠ z2 ∧ G.Adj p.center z1 ∧
      G.Adj p.center z2 ∧
      QuadOn G ((p.triangle ∪ a) \ {z1, z2, p.center}) := by
    have hset : ({z1, z2, p.center} : Finset V) = {p.center, d 2, d 3} := by
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
        ext u <;> simp only [mem_insert, mem_singleton] <;> tauto
    rw [hset]
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨h.mem 2, h.mem 3, d.injective.ne (by decide),
        h.center_first, h.center_second, h.primary⟩
    · exact ⟨h.mem 3, h.mem 2, d.injective.ne (by decide),
        h.center_second, h.center_first, h.primary⟩
  exact TwoCore.two_vertex_core_obstruction hc hcard hdeg hn p h.config.1 h.config.2.2.1
    z1 z2 hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2.1 hdata.2.2.2.2.1
    hfull hbound h.outside_factor hdata.2.2.2.2.2 hj hja.symm v hv hdiag hrow hz1 hz2

theorem Core.loss_exposed_low_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hloss : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) < edgeCount G a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (v : Quadrilateral G) (hv : v.support = j) (hdiag : PawBlock.OnlyFirst v)
    (hrow : ∀ i : Fin 4, G.Adj (q 3) (v i) ↔ (9 : ℕ).testBit i.val = true)
    (z1 z2 : V) (hpair : z1 = d 2 ∧ z2 = d 3 ∨ z1 = d 3 ∧ z2 = d 2)
    (hz1 : ∀ i : Fin 4, i ≠ 3 → G.Adj z1 (v i))
    (hz2 : 1 ≤ degreeIn G z2 {v 1, v 2}) : False := by
  obtain ⟨hp, hs, ha, has, hcase, _, _⟩ := h.config
  have hFQ := h.paw_disjoint hs
  let p' := JointClaims.exposedPaw p q hFQ (Or.inr hcase)
  obtain ⟨e, he, _, _, hp', _, _, _, hkeep⟩ :=
    JointClaims.exists_exposed_chain hc hcard hn p hp hs q rfl hFQ (Or.inr hcase)
  have htri : p'.triangle = p.triangle :=
    JointClaims.exposedPaw_triangle p q hFQ (Or.inr hcase)
  have hfull : degreeIn G (p'.vertices 3) a = 4 := by
    change degreeIn G (p.vertices 3) a = 4
    rw [← h.labels]
    exact (h.loss_rows hloss).third_full
  have hcore : ∀ u, u ∉ p'.triangle ∪ a → 2 ≤ degreeIn G u (p'.triangle ∪ a) →
      LocalFactor G (insert u (p'.triangle ∪ a)) := by
    rw [htri]
    exact h.outside_factor
  have hzmem : z1 ∈ a ∧ z2 ∈ a ∧ z1 ≠ z2 := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨h.mem 2, h.mem 3, d.injective.ne (by decide)⟩
    · exact ⟨h.mem 3, h.mem 2, d.injective.ne (by decide)⟩
  rcases (h.loss_rows hloss).2 with h28 | h31
  · have hr : degreeIn G (p'.vertices 2) a = 4 := by
      change degreeIn G (p.vertices 1) a = 4
      rw [← h.labels, h28.1.degree p d 1 15]
      decide +kernel
    have hb : degreeIn G p'.center a ≤ 2 := by
      change degreeIn G (p.vertices 2) a ≤ 2
      rw [← h.labels]
      exact h28.2.2.1
    exact TwoCore.complete_core_obstruction he.1 hcard hdeg hn p' hp' (hkeep a ha has)
      (h.loss_scores hloss).2.2.2 z1 z2 hzmem.1 hzmem.2.1 hzmem.2.2 hr hfull hb hcore
      (hkeep j hj hjq) hja.symm v hv hdiag hrow hz1 hz2
  · have hb2 : G.Adj (p.vertices 2) (d 2) := (h31.2 2).mpr (by decide)
    have hb3 : G.Adj (p.vertices 2) (d 3) := (h31.2 3).mpr (by decide)
    have hadj : G.Adj p'.center z1 ∧ G.Adj p'.center z2 := by
      change G.Adj (p.vertices 2) z1 ∧ G.Adj (p.vertices 2) z2
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hb2, hb3⟩
      · exact ⟨hb3, hb2⟩
    have hbound : contacts G {p'.center, p'.vertices 2} a ≤ 6 := by
      change contacts G {p.vertices 2, p.center} a ≤ 6
      rw [pair_comm, ← h.labels]
      exact (h.loss_rows hloss).pair_bound
    have hcomp : QuadOn G ((p'.triangle ∪ a) \ {z1, z2, p'.center}) := by
      rw [htri]
      change QuadOn G ((p.triangle ∪ a) \ {z1, z2, p.vertices 2})
      rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h.tertiary
      · rw [insert_comm]
        exact h.tertiary
    exact TwoCore.two_vertex_core_obstruction he.1 hcard hdeg hn p' hp'
      (hkeep a ha has) z1 z2 hzmem.1 hzmem.2.1 hzmem.2.2 hadj.1 hadj.2 hfull hbound
      hcore hcomp (hkeep j hj hjq) hja.symm v hv hdiag hrow hz1 hz2

theorem Core.loss_low_pattern_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hloss : edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) < edgeCount G a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (u : V) (hu : u = p.leaf ∨ u = q 3) (v : Quadrilateral G) (hv : v.support = j)
    (hdiag : PawBlock.OnlyFirst v)
    (hrow : ∀ i : Fin 4, G.Adj u (v i) ↔ (9 : ℕ).testBit i.val = true)
    (z1 z2 : V) (hpair : z1 = d 2 ∧ z2 = d 3 ∨ z1 = d 3 ∧ z2 = d 2)
    (hz1 : ∀ i : Fin 4, i ≠ 3 → G.Adj z1 (v i))
    (hz2 : 1 ≤ degreeIn G z2 {v 1, v 2}) : False := by
  rcases hu with rfl | rfl
  · exact h.loss_old_low_false hc hcard hdeg hn hloss hj hja v hv hdiag hrow z1 z2 hpair hz1 hz2
  · exact h.loss_exposed_low_false hc hcard hdeg hn hloss hj hjq hja v hv hdiag hrow
      z1 z2 hpair hz1 hz2

end Erdos577.JointFinal
