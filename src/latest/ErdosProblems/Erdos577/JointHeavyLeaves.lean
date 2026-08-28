import ErdosProblems.Erdos577.JointLeafSmall
import ErdosProblems.Erdos577.JointLeafLarge

/-! TeX9.48: both exposed leaves miss every block satisfying the six-row threshold. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem heavy_leaves_zero {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : CaseOne p q ∨ CaseTwo p q)
    (hweight : 13 ≤ sixWeight p q a) :
    degreeIn G p.leaf a = 0 ∧ degreeIn G (q 3) a = 0 ∧
      13 ≤ degreeIn G (p.vertices 3) a + contacts G p.triangle a := by
  have hlarge : 3 ≤ degreeIn G (p.vertices 3) a := by
    by_contra! hh
    exact small_third_false hc hcard hdeg hn p hp hs ha has q hq hcase hweight (by omega)
  have hzero : degreeIn G p.leaf a + degreeIn G (q 3) a = 0 := by
    by_contra hnonzero
    exact large_third_positive_false hc hcard hdeg hn p hp hs ha has q hq hcase hweight hlarge
      (Nat.pos_of_ne_zero hnonzero)
  have hx : degreeIn G p.leaf a = 0 := by omega
  have ht : degreeIn G (q 3) a = 0 := by omega
  rw [sixWeight, p.contacts_support, hx, ht] at hweight
  exact ⟨hx, ht, by omega⟩

end Erdos577.JointClaims
