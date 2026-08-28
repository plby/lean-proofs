import ErdosProblems.Erdos577.JointBridgeRoute

/-! A universally replaceable bridge block has at most one contact per column into the core. -/

namespace Erdos577.JointBridge

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem block_core_degree_le_one {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a b : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (hb : b ∈ c.blocks)
    (has : a ≠ s) (hbs : b ≠ s) (hba : b ≠ a)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : JointClaims.CaseTwo p q)
    (hthree : 3 ≤ degreeIn G (q 3) b)
    (hcore : ∀ v, v ∉ p.triangle ∪ a → 2 ≤ degreeIn G v (p.triangle ∪ a) →
      LocalFactor G (insert v (p.triangle ∪ a))) (u : V) (hu : u ∈ b) :
    degreeIn G u (p.triangle ∪ a) ≤ 1 := by
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hFB : Disjoint p.support b := by
    rw [hp]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hb)
  have hout : u ∉ p.triangle ∪ a := by
    intro hh
    rcases mem_union.mp hh with hh | hh
    · exact disjoint_left.mp hFB (p.support_eq ▸ mem_insert_of_mem hh) hu
    · exact disjoint_left.mp (c.property.blocks_disjoint ha hb hba.symm) hh hu
  obtain ⟨d, hd, ht, hT, _, _, _, _, hkeep⟩ :=
    JointClaims.exists_exposed_chain hc hcard hn p hp hs q hq hFQ (Or.inr hcase)
  have had := hkeep a ha has
  have hbd := hkeep b hb hbs
  by_contra! hh
  have hf : LocalFactor G (insert u (d.triangle ∪ a)) := by
    rw [hT]
    exact hcore u hout (by omega)
  exact hn (d.hasPacking_of_core_replacement hcard hbd had hba hu hf
    (hd.toFeasible.terminal_universal_replace hbd (by rw [ht]; exact hthree) hu))

end Erdos577.JointBridge
