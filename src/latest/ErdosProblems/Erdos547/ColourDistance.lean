import ErdosProblems.Erdos547.TreeCopyDistance
import Mathlib.Combinatorics.SimpleGraph.Coloring.Constructions

/-!
# Distance parity in any proper two-colouring
-/

namespace Erdos547

open SimpleGraph

theorem dist_even_iff_colour_eq {U : Type*} (T : SimpleGraph U)
    (hT : T.Preconnected) (col : T.Coloring (Fin 2)) (u v : U) :
    T.dist u v % 2 = 0 ↔ col u = col v := by
  let cb : T.Coloring Bool := {
    toFun := fun x ↦ finTwoEquiv (col x)
    map_rel' := fun h he ↦ col.valid h (finTwoEquiv.injective he)
  }
  obtain ⟨p, hp⟩ := (hT u v).exists_walk_length_eq_dist
  calc
    T.dist u v % 2 = 0 ↔ Even p.length := by rw [hp, Nat.even_iff]
    _ ↔ (cb u ↔ cb v) := cb.even_length_iff_congr p
    _ ↔ cb u = cb v := Bool.eq_iff_iff.symm
    _ ↔ col u = col v := finTwoEquiv.injective.eq_iff

theorem inner_attachment_distance_lower {U : Type*} (T : SimpleGraph U)
    (hT : T.IsTree) (S : Set U) (hS : (T.induce S).IsTree)
    (a b : U) (x y : S) (hax : T.Adj a x.val) (hby : T.Adj b y.val)
    (hab : 6 ≤ T.dist a b) : 4 ≤ (T.induce S).dist x y := by
  have ha : T.dist a x.val = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hax
  have hb : T.dist y.val b = 1 := SimpleGraph.dist_eq_one_iff_adj.mpr hby.symm
  have hfirst := hT.connected.dist_triangle (u := a) (v := x.val) (w := b)
  have hsecond := hT.connected.dist_triangle (u := x.val) (v := y.val) (w := b)
  have hdist := tree_copy_dist_eq hS hT.isAcyclic (SimpleGraph.Copy.induce T S) x y
  change T.dist x.val y.val = (T.induce S).dist x y at hdist
  omega

end Erdos547

#print axioms Erdos547.dist_even_iff_colour_eq
#print axioms Erdos547.inner_attachment_distance_lower
