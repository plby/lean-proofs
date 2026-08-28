import ErdosProblems.Erdos577.DensePairObstruction

/-! Dense-core bounds for every first block reached by a leaf row of degree at least three. -/

namespace Erdos577.LargeLeaf

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem dense_core_bounds {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (hlarge : 3 ≤ degreeIn G p.leaf s) {a : Finset V} (ha : a ∈ c.blocks) (has : a ≠ s)
    (hT : 11 ≤ contacts G p.triangle a) :
    G.IsNClique 4 a ∧ degreeIn G p.leaf a = 0 ∧
      ∀ u ∈ s, degreeIn G u (p.triangle ∪ a) ≤ 1 := by
  have hcl := ((hc.presentPaw_feasible p hp).all_triangle_universal_replacements ha hT).1
  have hTA : Disjoint p.triangle a := (c.presentPaw p hp).triangle_disjoint_block ha
  have hleaf := (c.presentPaw p hp).terminal_core_degree_le_one_of_dense_clique
    hcard hn ha hcl hT
  change degreeIn G p.leaf (p.triangle ∪ a) ≤ 1 at hleaf
  have hleafT := p.leaf_triangle_degree_eq_one
    (by rw [hp]; exact c.no_quad_remainder hcard hn)
  rw [degreeIn_union G p.leaf hTA, hleafT] at hleaf
  refine ⟨hcl, by omega, ?_⟩
  intro u hu
  have hTS : Disjoint p.triangle s := (c.presentPaw p hp).triangle_disjoint_block hs
  have hout : u ∉ p.triangle ∪ a := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact disjoint_left.mp hTS hh hu
    · exact disjoint_left.mp (c.property.blocks_disjoint hs ha has.symm) hu hh
  by_contra htwo
  have hf := dense_triangle_clique_factor p.triangle_clique hcl hTA hT hout (by omega)
  have hrep := (hc.presentPaw_feasible p hp).terminal_universal_replace hs hlarge hu
  exact hn ((c.presentPaw p hp).hasPacking_of_core_replacement hcard hs ha has.symm hu hf hrep)

end Erdos577.LargeLeaf
