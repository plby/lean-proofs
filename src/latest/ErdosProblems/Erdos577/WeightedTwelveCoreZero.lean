import ErdosProblems.Erdos577.WeightedTwelveDense
import ErdosProblems.Erdos577.DenseCliqueChains

/-! Each first-block vertex meets the old triangle and cannot also meet the dense core block. -/

namespace Erdos577.WeightedTwelve

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

theorem first_core_zero {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (h : WeightedPawBlock.Pattern12 p q)
    (hT : 11 ≤ contacts G p.triangle a) (hcl : G.IsNClique 4 a) :
    ∀ u ∈ q.support, degreeIn G u a = 0 := by
  have hTA : Disjoint p.triangle a := by
    have hFA : Disjoint p.support a := by
      rw [hp]
      exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
    exact hFA.mono_left (p.support_eq ▸ subset_insert _ _)
  intro u hu
  obtain ⟨i, rfl⟩ := (q.mem_support u).mp hu
  have hm : q i ∈ s := hq ▸ (q.mem_support _).mpr ⟨i, rfl⟩
  let d := c.presentPaw p hp
  have hrep := (hc.presentPaw_feasible p hp).terminal_universal_replace hs
    (by change 3 ≤ degreeIn G p.leaf s; rw [← hq, (counts p q h).1]) hm
  let e := d.replaceBlock s hs (d.swapTerminal hs hm hrep)
  have ha' : a ∈ e.blocks := mem_union_left _ (mem_erase.mpr ⟨has, ha⟩)
  have hcol := e.terminal_core_degree_le_one_of_dense_clique hcard hn ha' hcl hT
  change degreeIn G (q i) (p.triangle ∪ a) ≤ 1 at hcol
  apply (degreeIn_eq_zero_iff (G := G) (q i) a).mpr
  intro v hv huv
  have hno := JointCore.no_other_contact hTA hv huv hcol
  by_cases hi : i = 3
  · subst i
    exact hno (p.vertices 3) (by simp [Paw.triangle]) (first_rows p q h).2.symm
  · have hbits : ∀ i : Fin 4, i ≠ 3 → (7 : ℕ).testBit i.val = true := by decide +kernel
    exact hno (p.vertices 2) (by simp [Paw.triangle]) ((h.2.2.1 i).mpr (hbits i hi)).symm

end Erdos577.WeightedTwelve
