import ErdosProblems.Erdos577.JointCoreInsideRows

/-! The source inside sums are at most17 and22, with exact row supports. -/

namespace Erdos577.JointCore

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma contacts_insert_upper (v : V) (s t : Finset V) :
    contacts G (insert v s) t ≤ degreeIn G v t + contacts G s t := by
  by_cases h : v ∈ s
  · rw [insert_eq_of_mem h]
    omega
  · simp only [contacts, sum_insert h, le_refl]

lemma inside_sums_of_rows (x z1 z2 u : V) (s : Finset V)
    (hx : degreeIn G x s ≤ 5) (h1 : degreeIn G z1 s ≤ 6)
    (h2 : degreeIn G z2 s ≤ 6) (hu : degreeIn G u s ≤ 5) :
    contacts G {x, z1, z2} s ≤ 17 ∧ contacts G {x, z1, z2, u} s ≤ 22 := by
  have h01 := contacts_insert_upper (G := G) x {z1, z2} s
  have h12 := contacts_insert_upper (G := G) z1 {z2} s
  rw [contacts_singleton_left] at h12
  have h03 := contacts_insert_upper (G := G) x {z1, z2, u} s
  have h13 := contacts_insert_upper (G := G) z1 {z2, u} s
  have h23 := contacts_insert_upper (G := G) z2 {u} s
  rw [contacts_singleton_left] at h23
  constructor <;> omega

variable [Fintype V]

theorem core_inside_sums {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s)
    (hcase : JointClaims.CaseOne p q ∨ JointClaims.CaseTwo p q)
    (hx : degreeIn G p.leaf a = 0) (hu : degreeIn G (q 3) a = 0)
    (z1 z2 : V) (h1 : z1 ∈ a) (h2 : z2 ∈ a)
    (h1zero : degreeIn G z1 s = 0) (h2zero : degreeIn G z2 s = 0) :
    contacts G {p.leaf, z1, z2} (p.support ∪ q.support ∪ a) ≤ 17 ∧
    contacts G {p.leaf, z1, z2, q 3} (p.support ∪ q.support ∪ a) ≤ 22 := by
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hFA : Disjoint p.support a := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hQA : Disjoint q.support a := by rw [hq]; exact c.property.blocks_disjoint hs ha has.symm
  have hno : ¬QuadOn G p.support := by rw [hp]; exact c.no_quad_remainder hcard hn
  have hsize : a.card = 4 := (c.property.blocks_quad a ha).card
  have hxrow := leaf_inside_bound p q hFQ hFA hQA hno hx
  have h1row := core_inside_bound p q hsize hFQ hFA hQA hx z1 h1 (hq.symm ▸ h1zero)
  have h2row := core_inside_bound p q hsize hFQ hFA hQA hx z2 h2 (hq.symm ▸ h2zero)
  have hurow := last_inside_bound hc hcard hn p hp hs ha has q hq hcase hu
  exact inside_sums_of_rows p.leaf z1 z2 (q 3) _ hxrow h1row h2row hurow

end Erdos577.JointCore
