import ErdosProblems.Erdos577.JointPairHighRows

/-! The direct-core corollary in both actual terminal chains rules out the absent low diagonal. -/

namespace Erdos577.JointFinal

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem Core.high_pair_direct_false {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (v : Quadrilateral G) (hv : v.support = j) (hdiag : ¬G.Adj (v 1) (v 3))
    (u : V) (hu : u = p.leaf ∨ u = q 3) (z w : V)
    (hpair : z = d 2 ∧ w = d 3 ∨ z = d 3 ∧ w = d 2)
    (hz1 : G.Adj z (v 1)) (hz2 : G.Adj z (v 2)) (hw2 : G.Adj w (v 2))
    (hu0 : G.Adj u (v 0)) (hu2 : G.Adj u (v 2)) : False := by
  obtain ⟨hp, hs, ha, has, hcase, _, _⟩ := h.config
  have hdata : z ∈ a ∧ w ∈ a ∧ z ≠ w ∧ G.Adj p.center z := by
    rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨h.mem 2, h.mem 3, d.injective.ne (by decide), h.center_first⟩
    · exact ⟨h.mem 3, h.mem 2, d.injective.ne (by decide), h.center_second⟩
  have hrep := h.third_replacement z hdata.1
  have hav : a ≠ v.support := by rw [hv]; exact hja.symm
  rcases hu with rfl | rfl
  · exact JointFirst.terminal_high_pair_forbidden (hc.presentPaw_strong hcard hn p hp)
      hcard hdeg hn p rfl ha v (by rwa [hv]) hav hdiag h.outside_factor
      hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2 hrep hz1 hz2 hw2 ⟨hu0, hu2⟩
  · obtain ⟨e, he, hterm, htri, _, _, _, _, hkeep⟩ := JointClaims.exists_exposed_chain hc
      hcard hn p hp hs q rfl (h.paw_disjoint hs) (Or.inr hcase)
    have hh := JointFirst.terminal_high_pair_forbidden he hcard hdeg hn p htri
      (hkeep a ha has) v (by rw [hv]; exact hkeep j hj hjq) hav hdiag h.outside_factor
      hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2 hrep hz1 hz2 hw2
    rw [hterm] at hh
    exact hh ⟨hu0, hu2⟩

theorem Core.leaf_high_forces_diagonal {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    {p : Paw G} {q d : Quadrilateral G} {a j : Finset V} (h : Core c p q d a)
    (hj : j ∈ c.blocks) (hjq : j ≠ q.support) (hja : j ≠ a)
    (v : Quadrilateral G) (hv : v.support = j) (z w : V)
    (hpair : z = d 2 ∧ w = d 3 ∨ z = d 3 ∧ w = d 2)
    (hrows : PairRows v p.leaf (q 3) z w)
    (u : V) (hu : u = p.leaf ∨ u = q 3)
    (hu0 : G.Adj u (v 0)) (hu2 : G.Adj u (v 2)) : G.Adj (v 1) (v 3) := by
  by_contra hdiag
  rcases hrows.common_high_of_leaf_high u hu hu0 hu2 with hw0 | hw2
  · let v' := (v.rotate 2).reverse
    have hv' : v'.support = j := by
      simp only [v', Quadrilateral.reverse_support, Quadrilateral.rotate_support, hv]
    exact h.high_pair_direct_false hc hcard hdeg hn hj hjq hja v' hv' hdiag u hu z w hpair
      (hrows.three 1 (by decide)) (hrows.three 0 (by decide)) hw0 hu2 hu0
  · exact h.high_pair_direct_false hc hcard hdeg hn hj hjq hja v hv hdiag u hu z w hpair
      (hrows.three 1 (by decide)) (hrows.three 2 (by decide)) hw2 hu0 hu2

end Erdos577.JointFinal
