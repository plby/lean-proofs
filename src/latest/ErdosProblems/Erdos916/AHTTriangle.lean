/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos916.CoreAHT

/-!
# The triangle obstruction in the AHT argument

The first lemma in Section 6 of Aboulker--Havet--Trotignon proves that an
almost-wheel-free three-connected graph is triangle-free.  The final,
purely path-theoretic step of that argument is recorded here: if a triangle
vertex has a third neighbour lying on a path between the other two triangle
vertices, and the path avoids the first vertex, then closing that path by the
opposite triangle edge gives a wheel.

This formulation is independent of any connectivity convention.  A later
fan or Menger lemma only has to construct the displayed path.
-/

namespace Erdos916

open SimpleGraph

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A path between two neighbours of `x`, passing through a third neighbour
of `x` and avoiding `x`, becomes the rim of a wheel after adding the edge
between its endpoints. -/
theorem hasWheelWitness_of_adjacent_neighbors_path
    {x a b c : V}
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hxc : G.Adj x c)
    (hab : G.Adj a b)
    (hac : a ≠ c) (hbc : b ≠ c)
    (p : G.Walk a b) (hp : p.IsPath)
    (hc : c ∈ p.support) (hx : x ∉ p.support) :
    HasWheelWitness G := by
  have hab_not_mem : s(a, b) ∉ p.edges := by
    intro he
    have hp_eq := hp.eq_adj_toWalk_of_mem_edges he
    have hc' : c ∈ (p.adj_of_mem_edges he).toWalk.support := by
      simpa only [hp_eq] using hc
    simp at hc'
    exact hc'.elim hac.symm hbc.symm
  let q : G.Walk b b := .cons hab.symm p
  have hq : q.IsCycle := by
    exact SimpleGraph.Path.cons_isCycle ⟨p, hp⟩ hab.symm
      (by simpa only [Sym2.eq_swap] using hab_not_mem)
  refine ⟨b, q, x, hq, ?_, ?_⟩
  · simp [q, hxb.ne, hx]
  · have ha : a ∈ G.neighborFinset x ∩ q.support.toFinset := by
      simp [q, hxa, p.start_mem_support]
    have hb : b ∈ G.neighborFinset x ∩ q.support.toFinset := by
      simp [q, hxb]
    have hc' : c ∈ G.neighborFinset x ∩ q.support.toFinset := by
      simp [q, hxc, hc]
    have hthree := Finset.two_lt_card_iff.mpr
      ⟨a, b, c, ha, hb, hc', hab.ne, hac, hbc⟩
    omega

/-- In particular, a triangle and a path through a third neighbour of one
triangle vertex give a wheel.  This is the exact path-building conclusion
used in the proof of AHT Lemma 6.1. -/
theorem hasWheelWitness_of_triangle_thirdNeighbor_path
    {x a b c : V}
    (hxa : G.Adj x a) (hxb : G.Adj x b) (hab : G.Adj a b)
    (hxc : G.Adj x c) (hac : a ≠ c) (hbc : b ≠ c)
    (p : G.Walk a b) (hp : p.IsPath)
    (hc : c ∈ p.support) (hx : x ∉ p.support) :
    HasWheelWitness G :=
  hasWheelWitness_of_adjacent_neighbors_path hxa hxb hxc hab hac hbc p hp hc hx

end Erdos916
