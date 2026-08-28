import ErdosProblems.Erdos577.JointLeafFactors
import ErdosProblems.Erdos577.PathMiddleReplacements

/-! Common-neighbor selections on a four-block and the remaining two-cycle contradiction. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma common_replacement_of_five {a : Finset V} (ha : a.card = 4) (x y z : V)
    (hfive : 5 ≤ degreeIn G x a + degreeIn G y a)
    (hrep : ∀ u ∈ a, QuadOn G (insert z (a.erase u))) : CommonReplacement G x y z a := by
  have hbound : (a.filter (G.Adj x) ∪ a.filter (G.Adj y)).card ≤ 4 :=
    (card_le_card (union_subset (filter_subset _ _) (filter_subset _ _))).trans_eq ha
  obtain ⟨u, hu, hxu, hyu⟩ := common_neighbor_of_union_bound x y a 4 hbound (by omega)
  exact ⟨u, hu, hxu, hyu, hrep u hu⟩

lemma clique_common_replacement_of_seven {a : Finset V} (ha : G.IsNClique 4 a)
    (x y z : V) (hz : z ∉ a) (hseven : 7 ≤ degreeIn G x a + degreeIn G y a)
    (hzdegree : 2 ≤ degreeIn G z a) : CommonReplacement G x y z a := by
  obtain ⟨q, hq⟩ := QuadOn.of_clique ha.card_eq ha.isClique
  have hcommon := FullRow.common_set_card q x y (by rw [hq]; exact hseven)
  rw [hq] at hcommon
  have hsub : a.filter (G.Adj x) ∩ a.filter (G.Adj y) ⊆ a :=
    inter_subset_left.trans (filter_subset _ _)
  obtain ⟨u, hu, hrep⟩ := clique_replace_in_three_candidates ha z hz hzdegree _ hsub hcommon
  obtain ⟨huX, huY⟩ := mem_inter.mp hu
  exact ⟨u, hsub hu, (mem_filter.mp huX).2, (mem_filter.mp huY).2, hrep⟩

lemma clique_replace_nonadjacent {a : Finset V} (ha : G.IsNClique 4 a)
    (z u : V) (hz : z ∉ a) (hu : u ∈ a) (hdegree : 2 ≤ degreeIn G z a)
    (hn : ¬G.Adj z u) : QuadOn G (insert z (a.erase u)) := by
  have hh := degreeIn_erase_add G z u hu
  rw [if_neg hn] at hh
  exact (clique_replace_iff_two_contacts ha hz hu).mpr (by omega)

lemma third_neighbor_noncontacts (p : Paw G) (u : V)
    (hcol : degreeIn G u p.triangle ≤ 1) (hthird : G.Adj (p.vertices 3) u) :
    ¬G.Adj p.center u ∧ ¬G.Adj (p.vertices 2) u := by
  have hu := (FullRow.unique_row_of_bound p.triangle u (p.vertices 3)
    (by simp [Paw.triangle]) hthird.symm hcol).2
  constructor
  · intro hh
    exact p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 3)
      ((hu p.center p.center_mem_triangle).mp hh.symm)
  · intro hh
    exact p.vertices.injective.ne (by decide : (2 : Fin 4) ≠ 3)
      ((hu (p.vertices 2) (by simp [Paw.triangle])).mp hh.symm)

variable [Fintype V]

omit [DecidableRel G.Adj] in
theorem third_common_false {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {a : Finset V} (ha : a ∈ c.blocks)
    (hcommon : CommonReplacement G p.leaf (p.vertices 3) (p.vertices 2) a) : False := by
  obtain ⟨q, hq⟩ := c.property.blocks_quad a ha
  have hd : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hf := third_common_factor p q hd (by rw [hq]; exact hcommon)
  rw [hp, hq] at hf
  exact c.no_local_factor hcard hn ha hf

end Erdos577.JointClaims
