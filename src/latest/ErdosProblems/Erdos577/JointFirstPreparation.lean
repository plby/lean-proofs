import ErdosProblems.Erdos577.JointFirstHeavy
import ErdosProblems.Erdos577.JointFirstRowBounds
import ErdosProblems.Erdos577.JointFirstDirect
import ErdosProblems.Erdos577.JointFirstGainLeaves

/-! The original dense CaseI hypotheses give the actual heavy block and every row restriction. -/

namespace Erdos577.JointFirst

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem exists_restricted_heavy_block {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : JointClaims.CaseOne p q)
    (houter : 7 ≤ degreeIn G p.center a + degreeIn G (p.vertices 3) a)
    (hweighted : 13 ≤ degreeIn G (p.vertices 3) a + contacts G p.triangle a) :
    ∃ z1 ∈ a, ∃ z2 ∈ a, z1 ≠ z2 ∧
      G.Adj p.center z1 ∧ G.Adj p.center z2 ∧ G.Adj z1 z2 ∧
      (∀ v ∈ a, QuadOn G (insert (p.vertices 3) (a.erase v))) ∧
      QuadOn G ((p.triangle ∪ a) \ {p.center, z1, z2}) ∧
      5 ≤ edgeCount G ((p.triangle ∪ a) \ {p.center, z1, z2}) ∧
      (∀ u, u ∉ p.triangle ∪ a → 2 ≤ degreeIn G u (p.triangle ∪ a) →
        LocalFactor G (insert u (p.triangle ∪ a))) ∧
      ∃ j : Quadrilateral G, j.support ∈ c.blocks ∧ j.support ≠ s ∧ j.support ≠ a ∧
        9 ≤ contacts G (arms p q z1 z2) j.support ∧
        (∀ x ∈ arms p q z1 z2, ∀ y ∈ arms p q z1 z2, ∀ z ∈ arms p q z1 z2,
          x ≠ y → x ≠ z → y ≠ z → ¬CommonReplacement G x y z j.support) ∧
        (∀ z ∈ arms p q z1 z2, degreeIn G z j.support ≤ 3) ∧
        degreeIn G p.leaf j.support ≤ 2 ∧ degreeIn G (q 1) j.support ≤ 2 := by
  obtain ⟨_, _, d, hd, hne, hr1, hr2, hz, hrep, hprimary, hpe, hsec1, hsec2,
      _, hcore, _, _, h17, _⟩ := JointClaims.dense_seven_vertex_core hc hcard hdeg hn p hp
    hs ha has q hq (Or.inl hcase) houter hweighted
  have h1 : d 2 ∈ a := hd ▸ (d.mem_support _).mpr ⟨2, rfl⟩
  have h2 : d 3 ∈ a := hd ▸ (d.mem_support _).mpr ⟨3, rfl⟩
  obtain ⟨b, hb, hbs, hba, hnine⟩ := exists_heavy_arms hc hcard hdeg hn p hp hs ha has q hq
    hcase houter hweighted (d 2) (d 3) h1 h2 hne h17
  obtain ⟨j, hj⟩ := c.property.blocks_quad b hb
  obtain ⟨hcommon, _, hrows, hx, hv⟩ := arms_row_restrictions hc hcard hn p hp hs ha hb
    has hbs hba.symm q hq hcase h1 h2 hne hr1 hr2 hprimary hsec1 hsec2 hnine
  rw [← hj] at hb hbs hba hnine hcommon hrows hx hv
  exact ⟨d 2, h1, d 3, h2, hne, hr1, hr2, hz, hrep, hprimary, hpe, hcore,
    j, hb, hbs, hba, hnine, hcommon, hrows, hx, hv⟩

end Erdos577.JointFirst
