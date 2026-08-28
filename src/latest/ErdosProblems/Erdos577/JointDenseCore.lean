import ErdosProblems.Erdos577.JointCoreSelection
import ErdosProblems.Erdos577.JointCoreZeroRows
import ErdosProblems.Erdos577.JointCoreInside
import ErdosProblems.Erdos577.JointHeavyLeaves

/-! TeX9.49: the complete dense seven-vertex core, for both starting cases. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem dense_seven_vertex_core {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : CaseOne p q ∨ CaseTwo p q)
    (houter : 7 ≤ degreeIn G p.center a + degreeIn G (p.vertices 3) a)
    (hweighted : 13 ≤ degreeIn G (p.vertices 3) a + contacts G p.triangle a) :
    degreeIn G p.leaf a = 0 ∧ degreeIn G (q 3) a = 0 ∧
    ∃ d : Quadrilateral G, d.support = a ∧ d 2 ≠ d 3 ∧
      G.Adj p.center (d 2) ∧ G.Adj p.center (d 3) ∧ G.Adj (d 2) (d 3) ∧
      (∀ v ∈ a, QuadOn G (insert (p.vertices 3) (a.erase v))) ∧
      QuadOn G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) ∧
      5 ≤ edgeCount G ((p.triangle ∪ a) \ {p.center, d 2, d 3}) ∧
      QuadOn G ((p.triangle ∪ a) \ {d 2, p.center, p.vertices 2}) ∧
      QuadOn G ((p.triangle ∪ a) \ {d 3, p.center, p.vertices 2}) ∧
      QuadOn G ((p.triangle ∪ a) \ {d 2, d 3, p.vertices 2}) ∧
      (∀ u, u ∉ p.triangle ∪ a → 2 ≤ degreeIn G u (p.triangle ∪ a) →
        LocalFactor G (insert u (p.triangle ∪ a))) ∧
      degreeIn G (d 2) s = 0 ∧ degreeIn G (d 3) s = 0 ∧
      contacts G {p.leaf, d 2, d 3} (p.support ∪ q.support ∪ a) ≤ 17 ∧
      contacts G {p.leaf, d 2, d 3, q 3} (p.support ∪ q.support ∪ a) ≤ 22 ∧
      (11 ≤ contacts G p.triangle a →
        G.IsNClique 4 ((p.triangle ∪ a) \ {p.center, d 2, d 3})) ∧
      (contacts G p.triangle a ≤ 10 → ∃ tag : Fin 8, JointCore.SourcePattern tag p d) := by
  have hweight : 13 ≤ sixWeight p q a := by
    rw [sixWeight, p.contacts_support]
    omega
  obtain ⟨hx, hu, _⟩ := heavy_leaves_zero hc hcard hdeg hn p hp hs ha has q hq hcase hweight
  obtain ⟨d, hd, hr1, hr2, hz, hprimary, he, hs1, hs2, ht, hrep, hhigh, hlow⟩ :=
    JointCore.selected_pair hc p hp ha houter hweighted
  have hm (i : Fin 4) : d i ∈ a := hd ▸ (d.mem_support _).mpr ⟨i, rfl⟩
  have hzero1 := JointCore.selected_vertex_first_row_zero hc hcard hn p hp hs ha has q hq hcase
    houter hweighted (d 2) (hm 2) hr1 hs1
  have hzero2 := JointCore.selected_vertex_first_row_zero hc hcard hn p hp hs ha has q hq hcase
    houter hweighted (d 3) (hm 3) hr2 hs2
  obtain ⟨h17, h22⟩ := JointCore.core_inside_sums hc hcard hn p hp hs ha has q hq hcase hx hu
    (d 2) (d 3) (hm 2) (hm 3) hzero1 hzero2
  exact ⟨hx, hu, d, hd, d.injective.ne (by decide : (2 : Fin 4) ≠ 3), hr1, hr2, hz, hrep,
    hprimary, he, hs1, hs2, ht, JointCore.core_outside_factor hc p hp ha houter hweighted,
    hzero1, hzero2, h17, h22, hhigh, hlow⟩

end Erdos577.JointClaims
