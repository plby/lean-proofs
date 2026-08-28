import ErdosProblems.Erdos577.JointCoreLocal
import ErdosProblems.Erdos577.JointSetupRows
import ErdosProblems.Erdos577.CliqueLabels

/-! Every first-block vertex has at most one neighbor in the dense seven-core. -/

namespace Erdos577.JointCore

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem first_core_column {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s)
    (hcase : JointClaims.CaseOne p q ∨ JointClaims.CaseTwo p q)
    (houter : 7 ≤ degreeIn G p.center a + degreeIn G (p.vertices 3) a)
    (hweighted : 13 ≤ degreeIn G (p.vertices 3) a + contacts G p.triangle a)
    (u : V) (hu : u ∈ s) : degreeIn G u (p.triangle ∪ a) ≤ 1 := by
  let d := c.presentPaw p hp
  have hthree : 3 ≤ degreeIn G p.leaf s := hq ▸ JointClaims.leaf_lower p q hcase
  have hrep := (hc.presentPaw_feasible p hp).terminal_universal_replace hs hthree hu
  let d' := d.replaceBlock s hs (d.swapTerminal hs hu hrep)
  have ha' : a ∈ d'.blocks := mem_union_left _ (mem_erase.mpr ⟨has, ha⟩)
  have hout : u ∉ p.triangle ∪ a := by
    intro h
    rcases mem_union.mp h with h | h
    · have hpv : u ∈ p.support := p.support_eq ▸ mem_insert_of_mem h
      exact (mem_sdiff.mp (c.complementPartition.block_subset hs hu)).2 (hp ▸ hpv)
    · exact disjoint_left.mp (c.property.blocks_disjoint hs ha has.symm) hu h
  by_contra! hh
  apply d'.no_local_factor hcard hn ha'
  change LocalFactor G (insert u p.triangle ∪ a)
  rw [insert_union]
  exact core_outside_factor hc p hp ha houter hweighted u hout (by omega)

theorem noncentral_replacement_of_missed {c : TriangleChain G} (hc : c.Feasible)
    (p : Paw G) (hp : p.support = c.remainder) {s : Finset V} (hs : s ∈ c.blocks)
    (q : Quadrilateral G) (hq : q.support = s)
    (hcase : JointClaims.CaseOne p q ∨ JointClaims.CaseTwo p q)
    (u : V) (hu : u ∈ q.support) (hmiss : ¬G.Adj (p.vertices 2) u) :
    QuadOn G (insert (p.vertices 2) (q.support.erase u)) := by
  rcases hcase with hcase | hcase
  · have hcl : G.IsNClique 4 q.support := hq.symm ▸
      (hc.presentPaw_feasible p hp).clique_of_terminal_degree_four hs (hq ▸ hcase.1)
    have hFQ : Disjoint p.support q.support := by
      rw [hp, hq]
      exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
    have hbout : p.vertices 2 ∉ q.support := fun hh ↦ disjoint_left.mp hFQ
      ((mem_tupleSupport p.vertices _).mpr ⟨2, rfl⟩) hh
    have hsub : ({q 2, q 3} : Finset V) ⊆ q.support.filter (G.Adj (p.vertices 2)) := by
      apply insert_subset (mem_filter.mpr ⟨(q.mem_support _).mpr ⟨2, rfl⟩, hcase.2.2.1⟩)
      exact singleton_subset_iff.mpr (mem_filter.mpr ⟨(q.mem_support _).mpr ⟨3, rfl⟩, hcase.2.2.2⟩)
    have htwo := card_le_card hsub
    have h23 : q 2 ≠ q 3 := q.injective.ne (by decide : (2 : Fin 4) ≠ 3)
    rw [card_pair_eq_two_iff.mpr h23] at htwo
    change 2 ≤ degreeIn G (p.vertices 2) q.support at htwo
    have he := degreeIn_erase_add G (p.vertices 2) u hu
    rw [if_neg hmiss, add_zero] at he
    exact (clique_replace_iff_two_contacts hcl hbout hu).mpr (by omega)
  · exact JointClaims.case_two_universal hc p hp hs q hq hcase u hu

end Erdos577.JointCore
