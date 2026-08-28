import ErdosProblems.Erdos577.JointMaximalCore
import ErdosProblems.Erdos577.JointCoreRefinedSelection

/-! TeX9.55: the maximal core with refined labels and all previously required core properties. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem maximal_dense_seven_vertex_core {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (q : Quadrilateral G) {a : Finset V} (hmax : MaximalCore c p q a) :
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
      degreeIn G (d 2) q.support = 0 ∧ degreeIn G (d 3) q.support = 0 ∧
      contacts G {p.leaf, d 2, d 3} (p.support ∪ q.support ∪ a) ≤ 17 ∧
      contacts G {p.leaf, d 2, d 3, q 3} (p.support ∪ q.support ∪ a) ≤ 22 ∧
      (11 ≤ contacts G p.triangle a →
        G.IsNClique 4 ((p.triangle ∪ a) \ {p.center, d 2, d 3})) ∧
      (contacts G p.triangle a ≤ 10 → ∃ tag : Fin 8, JointCore.RefinedSourcePattern tag p d ∧
        (tag = 1 → degreeIn G (p.vertices 2) a = 2 →
          (∀ j : Fin 4, G.Adj (p.vertices 2) (d j) ↔ j = 0 ∨ j = 1) ∧
          G.IsNClique 4 ((p.triangle ∪ a) \ {p.center, d 2, d 3}))) := by
  have hseven := maximal_core_seven_bound hc hcard hdeg hn p q hmax
  obtain ⟨hp, hs, ha, has, hcase, houter, hweighted⟩ := hmax.1
  have hweight : 13 ≤ sixWeight p q a := by
    rw [sixWeight, p.contacts_support]
    omega
  obtain ⟨hx, hu, _⟩ := heavy_leaves_zero hc hcard hdeg hn p hp hs ha has q rfl
    (Or.inr hcase) hweight
  obtain ⟨d, hd, hr1, hr2, hz, hprimary, he, hs1, hs2, ht, hrep, hhigh, hlow⟩ :=
    JointCore.refined_selected_pair hc p hp ha houter hweighted hseven
  have hm (i : Fin 4) : d i ∈ a := hd ▸ (d.mem_support _).mpr ⟨i, rfl⟩
  have hzero1 := JointCore.selected_vertex_first_row_zero hc hcard hn p hp hs ha has q rfl
    (Or.inr hcase) houter hweighted (d 2) (hm 2) hr1 hs1
  have hzero2 := JointCore.selected_vertex_first_row_zero hc hcard hn p hp hs ha has q rfl
    (Or.inr hcase) houter hweighted (d 3) (hm 3) hr2 hs2
  obtain ⟨h17, h22⟩ := JointCore.core_inside_sums hc hcard hn p hp hs ha has q rfl
    (Or.inr hcase) hx hu (d 2) (d 3) (hm 2) (hm 3) hzero1 hzero2
  exact ⟨hx, hu, d, hd, d.injective.ne (by decide : (2 : Fin 4) ≠ 3), hr1, hr2, hz, hrep,
    hprimary, he, hs1, hs2, ht, JointCore.core_outside_factor hc p hp ha houter hweighted,
    hzero1, hzero2, h17, h22, hhigh, hlow⟩

end Erdos577.JointClaims
