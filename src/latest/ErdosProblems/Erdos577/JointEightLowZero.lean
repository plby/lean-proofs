import ErdosProblems.Erdos577.JointEightLowTerminal
import ErdosProblems.Erdos577.JointEightFactors

/-! A complete outside block with a positive third row supplies the forbidden three-cycle factor. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V}

lemma clique_last_two {a : Finset V} (ha : G.IsNClique 4 a) {u w : V}
    (hu : u ∈ a) (hw : w ∈ a) (hne : u ≠ w) :
    ∃ v : Quadrilateral G, v.support = a ∧ v 2 = u ∧ v 3 = w := by
  have hsub : ({u, w} : Finset V) ⊆ a := insert_subset hu (singleton_subset_iff.mpr hw)
  have hrest : (a \ {u, w}).card = 2 := by
    rw [card_sdiff_of_subset hsub, ha.card_eq, card_pair_eq_two_iff.mpr hne]
  obtain ⟨z0, z1, hz, hrest⟩ := card_eq_two.mp hrest
  have hm0 : z0 ∈ a \ {u, w} := hrest.symm ▸ mem_insert_self _ _
  have hm1 : z1 ∈ a \ {u, w} := hrest.symm ▸ mem_insert_of_mem (mem_singleton_self _)
  have hn0 : z0 ≠ u ∧ z0 ≠ w := by simpa only [mem_insert, mem_singleton, not_or]
    using (mem_sdiff.mp hm0).2
  have hn1 : z1 ≠ u ∧ z1 ≠ w := by simpa only [mem_insert, mem_singleton, not_or]
    using (mem_sdiff.mp hm1).2
  let e := fourTuple z0 z1 u w hz hn0.1 hn0.2 hn1.1 hn1.2 hne
  have hem (i : Fin 4) : e i ∈ a := by
    fin_cases i
    · exact (mem_sdiff.mp hm0).1
    · exact (mem_sdiff.mp hm1).1
    · exact hu
    · exact hw
  let v := Quadrilateral.ofEdges e (fun i ↦ ha.isClique (hem i) (hem (i + 1))
    (e.injective.ne (by fin_cases i <;> decide)))
  refine ⟨v, ?_, rfl, rfl⟩
  apply eq_of_subset_of_card_le
  · intro z hz
    obtain ⟨i, rfl⟩ := (v.mem_support z).mp hz
    exact hem i
  · rw [v.card_support, ha.card_eq]

variable [Fintype V] [DecidableRel G.Adj]

theorem eight_low_zero {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : CaseTwo p q)
    (hweight : 17 ≤ eightWeight p q a)
    (hpos : 0 < degreeIn G p.leaf a + degreeIn G (q 3) a)
    (hlow : degreeIn G (q 3) a + degreeIn G p.center a + degreeIn G (p.vertices 3) a ≤ 6) :
    degreeIn G (p.vertices 3) a = 0 := by
  obtain ⟨_, ht3, hxt7, hT3, hcl⟩ :=
    eight_low_terminal hc hcard hdeg hn p hp hs ha has q hq hcase hweight hpos hlow
  obtain ⟨_, hT4, hdis, hxc4⟩ := eight_terminal_rows hc hcard hn p hp hs ha has q hq hcase ht3
  have hT := p.contacts_triangle a
  change contacts G p.triangle a = degreeIn G p.center a +
    (degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a) at hT
  have ht4 := degreeIn_le_card G (q 3) a
  rw [hcl.card_eq] at ht4
  have hw := hweight
  rw [eightWeight_eq_rows] at hw
  by_contra hz
  have hcpos : 0 < degreeIn G (p.vertices 3) a := Nat.pos_of_ne_zero hz
  have hx3 : degreeIn G p.leaf a = 3 := by omega
  have htfull : degreeIn G (q 3) a = 4 := by omega
  have hrpos : 0 < degreeIn G p.center a := by omega
  obtain ⟨w, hw⟩ := card_pos.mp hcpos
  obtain ⟨u, hu⟩ := card_pos.mp hrpos
  obtain ⟨hwa, hcw⟩ := mem_filter.mp hw
  obtain ⟨hua, hru⟩ := mem_filter.mp hu
  have hrc := triangle_rows_disjoint hc hcard hn p hp ha (by omega) p.center (p.vertices 3)
    p.center_mem_triangle (by simp [Paw.triangle])
    (p.vertices.injective.ne (by decide : (1 : Fin 4) ≠ 3))
  have huw : u ≠ w := fun he ↦ disjoint_left.mp hrc (mem_filter.mpr ⟨hua, hru⟩)
    (he.symm ▸ mem_filter.mpr ⟨hwa, hcw⟩)
  obtain ⟨v, hv, hv2, hv3⟩ := clique_last_two hcl hua hwa huw
  have hxnot : ¬G.Adj p.leaf (v 3) := by
    rw [hv3]
    intro hxw
    exact disjoint_left.mp hdis (mem_filter.mpr ⟨hwa, hxw⟩) (mem_filter.mpr ⟨hwa, hcw⟩)
  have hxrow := v.adj_iff_ne_three p.leaf (hv.symm ▸ hx3) hxnot
  have htrow := (degreeIn_eq_card_iff (q 3) a).mp (htfull.trans hcl.card_eq.symm)
  have hFA : Disjoint p.support v.support := by
    rw [hp, hv]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  have hpv (i j : Fin 4) : p.vertices i ≠ v j := fun he ↦ disjoint_left.mp hFA
    ((mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩) (he.symm ▸ (v.mem_support _).mpr ⟨j, rfl⟩)
  have hxt : p.leaf ≠ q 3 := fun he ↦ disjoint_left.mp hFQ
    (show p.leaf ∈ p.support from (mem_tupleSupport p.vertices _).mpr ⟨0, rfl⟩)
    (he.symm ▸ (q.mem_support _).mpr ⟨3, rfl⟩)
  have hcv3 : G.Adj (p.vertices 3) (v 3) := hv3.symm ▸ hcw
  have hrv2 : G.Adj p.center (v 2) := hv2.symm ▸ hru
  exact case_two_split_factor_false hc hcard hn p hp hs ha has q hq hcase v hv
    (QuadOn.of_vertices (hpv 1 3) (hpv 3 2) p.edge13 hcv3 (v.adjacent 2).symm hrv2.symm)
    (QuadOn.of_vertices hxt (v.injective.ne (by decide : (0 : Fin 4) ≠ 1))
      ((hxrow 0).mpr (by decide))
      (htrow (v 0) (hv ▸ (v.mem_support _).mpr ⟨0, rfl⟩)).symm
      (htrow (v 1) (hv ▸ (v.mem_support _).mpr ⟨1, rfl⟩)) ((hxrow 1).mpr (by decide)).symm)

end Erdos577.JointClaims
