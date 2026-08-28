import ErdosProblems.Erdos577.TwoCoreAbsentContacts
import ErdosProblems.Erdos577.PathRowCounts

/-! The individual rows in the inside estimate for Wang's two-vertex core obstruction. -/

namespace Erdos577.TwoCore

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma pair_internal_degree (p : Paw G) (hn : ¬QuadOn G p.support) :
    degreeIn G p.center p.support + degreeIn G (p.vertices 2) p.support = 5 := by
  have hcenter := degreeIn_clique G p.triangle_clique.isClique p.center_mem_triangle
  have h2mem : p.vertices 2 ∈ p.triangle := by simp [Paw.triangle]
  have htwo := degreeIn_clique G p.triangle_clique.isClique h2mem
  rw [p.triangle_clique.card_eq] at hcenter htwo
  have hnot : ¬G.Adj (p.vertices 2) p.leaf :=
    fun hh ↦ (p.nonadjacent_of_no_quad hn).1 hh.symm
  have hpend : G.Adj p.center p.leaf := p.pendant.symm
  rw [p.support_eq, degreeIn_insert G p.center p.leaf p.leaf_not_mem_triangle,
    degreeIn_insert G (p.vertices 2) p.leaf p.leaf_not_mem_triangle,
    if_pos hpend, if_neg hnot, hcenter, htwo]

lemma first_block_pair_bound (p : Paw G) (q : Quadrilateral G)
    (h0 : ¬G.Adj p.center (q 0)) (h1 : ¬G.Adj p.center (q 1))
    (h3 : ¬G.Adj p.center (q 3))
    (hb1 : ¬G.Adj (p.vertices 2) (q 1)) (hb3 : ¬G.Adj (p.vertices 2) (q 3)) :
    degreeIn G p.center q.support + degreeIn G (p.vertices 2) q.support ≤
      1 + degreeIn G (p.vertices 2) {q 0, q 2} := by
  have hsum (u : V) : degreeIn G u q.support =
      (if G.Adj u (q 0) then 1 else 0) + (if G.Adj u (q 1) then 1 else 0) +
      ((if G.Adj u (q 2) then 1 else 0) + (if G.Adj u (q 3) then 1 else 0)) := by
    rw [Quadrilateral.support, degreeIn_image G u univ q q.injective]
    simp only [Fin.sum_univ_four]
    omega
  have hne : q 0 ∉ ({q 2} : Finset V) :=
    fun hh ↦ q.injective.ne (by decide : (0 : Fin 4) ≠ 2) (mem_singleton.mp hh)
  have hpair : degreeIn G (p.vertices 2) {q 0, q 2} =
      (if G.Adj (p.vertices 2) (q 0) then 1 else 0) +
        (if G.Adj (p.vertices 2) (q 2) then 1 else 0) := by
    rw [degreeIn_insert G (p.vertices 2) (q 0) hne, degreeIn_singleton]
  rw [hsum p.center, hsum (p.vertices 2), hpair,
    if_neg h0, if_neg h1, if_neg h3, if_neg hb1, if_neg hb3]
  split_ifs <;> omega

lemma last_core_coupled_of_block_bound (p : Paw G) (q : Quadrilateral G) {b : Finset V} {n : ℕ}
    (hd : Disjoint p.support b) (hB : degreeIn G (q 3) b ≤ n)
    (hr : ¬G.Adj p.center (q 3)) (h2 : ¬G.Adj (p.vertices 2) (q 3))
    (hcoupled : degreeIn G (p.vertices 2) {q 0, q 2} = 2 → ¬G.Adj (p.vertices 3) (q 3)) :
    degreeIn G (p.vertices 2) {q 0, q 2} + degreeIn G (q 3) (p.triangle ∪ b) ≤ n + 2 := by
  have hnotr : ¬G.Adj (q 3) (p.vertices 1) := fun hh ↦ hr hh.symm
  have hnot2 : ¬G.Adj (q 3) (p.vertices 2) := fun hh ↦ h2 hh.symm
  have hT : degreeIn G (q 3) p.triangle =
      if G.Adj (q 3) (p.vertices 3) then 1 else 0 := by
    by_cases hh : G.Adj (q 3) (p.vertices 3)
    · simp [degreeIn, Paw.triangle, filter_insert, filter_singleton, hnotr, hnot2, hh]
    · simp [degreeIn, Paw.triangle, filter_insert, filter_singleton, hnotr, hnot2, hh]
  have hpair := degreeIn_le_card G (p.vertices 2) {q 0, q 2}
  have hpaircard : ({q 0, q 2} : Finset V).card = 2 :=
    card_pair_eq_two_iff.mpr (q.injective.ne (by decide : (0 : Fin 4) ≠ 2))
  rw [hpaircard] at hpair
  have htri : p.triangle ⊆ p.support := p.support_eq ▸ subset_insert _ _
  rw [degreeIn_union G (q 3) (hd.mono_left htri), hT]
  by_cases ht : degreeIn G (p.vertices 2) {q 0, q 2} = 2
  · have hn3 : ¬G.Adj (q 3) (p.vertices 3) := fun hh ↦ hcoupled ht hh.symm
    rw [if_neg hn3]
    omega
  · split_ifs <;> omega

lemma last_core_coupled (p : Paw G) (q : Quadrilateral G) {b : Finset V}
    (hb : b.card = 4) (hd : Disjoint p.support b) (z : V) (hz : z ∈ b)
    (hr : ¬G.Adj p.center (q 3)) (h2 : ¬G.Adj (p.vertices 2) (q 3))
    (hz3 : ¬G.Adj z (q 3))
    (hcoupled : degreeIn G (p.vertices 2) {q 0, q 2} = 2 → ¬G.Adj (p.vertices 3) (q 3)) :
    degreeIn G (p.vertices 2) {q 0, q 2} + degreeIn G (q 3) (p.triangle ∪ b) ≤ 5 := by
  have hnotz : ¬G.Adj (q 3) z := fun hh ↦ hz3 hh.symm
  have hB := degreeIn_le_card G (q 3) (b.erase z)
  have herase := degreeIn_erase_add G (q 3) z hz
  rw [if_neg hnotz, add_zero] at herase
  rw [card_erase_of_mem hz, hb, herase] at hB
  exact last_core_coupled_of_block_bound p q hd (n := 3) hB hr h2 hcoupled

variable [Fintype V]

theorem leaf_core_degree_zero {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder) {b : Finset V} (hb : b ∈ c.blocks)
    (hcore : ∀ u, u ∉ p.triangle ∪ b → 2 ≤ degreeIn G u (p.triangle ∪ b) →
      LocalFactor G (insert u (p.triangle ∪ b))) : degreeIn G p.leaf b = 0 := by
  have hT : degreeIn G p.leaf p.triangle = 1 :=
    p.leaf_triangle_degree_eq_one (by rw [hp]; exact c.no_quad_remainder hcard hn)
  have htri : p.triangle ⊆ p.support := p.support_eq ▸ subset_insert _ _
  have hd : Disjoint p.triangle b := by
    apply Disjoint.mono_left htri
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hb)
  have hx : p.leaf ∉ p.triangle ∪ b := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact p.leaf_not_mem_triangle hh
    · exact (c.presentPaw p hp).terminal_not_mem_block hb hh
  by_contra hnonzero
  have htwo : 2 ≤ degreeIn G p.leaf (p.triangle ∪ b) := by
    rw [degreeIn_union G p.leaf hd, hT]
    omega
  apply c.no_local_factor hcard hn hb
  rw [← hp, p.support_eq, insert_union]
  exact hcore p.leaf hx htwo

theorem leaf_inside_degree {c : TriangleChain G} {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b s : Finset V} (hb : b ∈ c.blocks) (hs : s ∈ c.blocks) (hbs : b ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hB : degreeIn G p.leaf b = 0)
    (hrow : ∀ i : Fin 4, G.Adj p.leaf (q i) ↔ (9 : ℕ).testBit i.val = true) :
    degreeIn G p.leaf (p.support ∪ (b ∪ q.support)) = 3 := by
  have hT : degreeIn G p.leaf p.triangle = 1 :=
    p.leaf_triangle_degree_eq_one (by rw [hp]; exact c.no_quad_remainder hcard hn)
  have hF : degreeIn G p.leaf p.support = 1 := by
    rw [p.support_eq, degreeIn_insert G p.leaf p.leaf p.leaf_not_mem_triangle,
      if_neg G.irrefl, zero_add, hT]
  have hQ : degreeIn G p.leaf q.support = 2 := by
    rw [q.degree_eq_mask p.leaf 9 hrow]
    decide +kernel
  have hdis : Disjoint p.support (b ∪ q.support) := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (union_subset
      (c.blockPartition.block_subset hb) (c.blockPartition.block_subset hs))
  have hBQ : Disjoint b q.support := by
    rw [hq]
    exact c.property.blocks_disjoint hb hs hbs
  rw [degreeIn_union G p.leaf hdis, degreeIn_union G p.leaf hBQ, hF, hB, hQ]

end Erdos577.TwoCore
