import ErdosProblems.Erdos577.JointEightFactors
import ErdosProblems.Erdos577.JointEightWeighted

/-! In the high weighted case the two remaining triangle rows are zero. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma good_weighted_cases (p : Paw G) (v : Quadrilateral G)
    (h : WeightedPawBlock.Pattern10 p v ∨ WeightedPawBlock.Pattern11 p v ∨
      WeightedPawBlock.Pattern12 p v) :
    (degreeIn G p.leaf v.support = 4 ∧ 3 ≤ degreeIn G (p.vertices 2) v.support ∧
      degreeIn G (p.vertices 3) v.support = 0) ∨
    (degreeIn G p.leaf v.support = 3 ∧ degreeIn G (p.vertices 2) v.support = 4 ∧
      degreeIn G (p.vertices 3) v.support = 0) ∨
    (degreeIn G p.leaf v.support = 3 ∧ degreeIn G (p.vertices 2) v.support = 3 ∧
      degreeIn G (p.vertices 3) v.support = 1) := by
  have h0 : (∑ j : Fin 4, ((0 : ℕ).testBit j.val).toNat) = 0 := by decide +kernel
  have h7 : (∑ j : Fin 4, ((7 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
  have h8 : (∑ j : Fin 4, ((8 : ℕ).testBit j.val).toNat) = 1 := by decide +kernel
  have h14 : (∑ j : Fin 4, ((14 : ℕ).testBit j.val).toNat) = 3 := by decide +kernel
  have h15 : (∑ j : Fin 4, ((15 : ℕ).testBit j.val).toNat) = 4 := by decide +kernel
  rcases h with h | h | h
  · have hx := h.2.2.1.degree p v 0 15
    have hc := h.2.2.2.1.degree p v 3 0
    have hr := v.degree_ge_mask (p.vertices 2) 14 h.2.2.2.2
    rw [h15] at hx
    rw [h0] at hc
    rw [h14] at hr
    exact Or.inl ⟨hx, hr, hc⟩
  · have hx := h.2.1.degree p v 0 7
    have hr := h.2.2.1.degree p v 2 15
    have hc := h.2.2.2.degree p v 3 0
    rw [h7] at hx
    rw [h15] at hr
    rw [h0] at hc
    exact Or.inr (Or.inl ⟨hx, hr, hc⟩)
  · have hx := h.2.1.degree p v 0 7
    have hr := h.2.2.1.degree p v 2 7
    have hc := h.2.2.2.degree p v 3 8
    rw [h7] at hx hr
    rw [h8] at hc
    exact Or.inr (Or.inr ⟨hx, hr, hc⟩)

variable [Fintype V]

theorem eight_high_zero {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s a : Finset V} (hs : s ∈ c.blocks) (ha : a ∈ c.blocks) (has : a ≠ s)
    (q : Quadrilateral G) (hq : q.support = s) (hcase : CaseTwo p q)
    (hweight : 17 ≤ eightWeight p q a)
    (hpos : 0 < degreeIn G p.leaf a + degreeIn G (q 3) a)
    (hhigh : 7 ≤ degreeIn G (q 3) a + degreeIn G p.center a + degreeIn G (p.vertices 3) a) :
    degreeIn G (p.vertices 2) a = 0 ∧ degreeIn G (p.vertices 3) a = 0 := by
  have hFQ : Disjoint p.support q.support := by
    rw [hp, hq]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
  let p' := exposedPaw p q hFQ (Or.inr hcase)
  obtain ⟨v, hv, hpat⟩ := eight_high_patterns hc hcard hdeg hn p hp hs ha has q hq
    hcase hweight hpos hhigh hFQ
  have hcounts := good_weighted_cases p' v hpat
  change (degreeIn G (q 3) v.support = 4 ∧ 3 ≤ degreeIn G p.center v.support ∧
    degreeIn G (p.vertices 3) v.support = 0) ∨
    (degreeIn G (q 3) v.support = 3 ∧ degreeIn G p.center v.support = 4 ∧
    degreeIn G (p.vertices 3) v.support = 0) ∨
    (degreeIn G (q 3) v.support = 3 ∧ degreeIn G p.center v.support = 3 ∧
    degreeIn G (p.vertices 3) v.support = 1) at hcounts
  rw [hv] at hcounts
  have ht3 : 3 ≤ degreeIn G (q 3) a := by rcases hcounts with h | h | h <;> omega
  obtain ⟨_, hT4, hdis, hxc4⟩ := eight_terminal_rows hc hcard hn p hp hs ha has q hq hcase ht3
  have hT := p.contacts_triangle a
  change contacts G p.triangle a = degreeIn G p.center a +
    (degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a) at hT
  have hb0 : degreeIn G (p.vertices 2) a = 0 := by
    by_contra hh
    have ht4 : degreeIn G (q 3) a = 4 := by rcases hcounts with h | h | h <;> omega
    obtain ⟨d, hd, _, _, hp', _, _, _, hkeep⟩ :=
      exists_exposed_chain hc hcard hn p hp hs q hq hFQ (Or.inr hcase)
    have hr1 := (hd.toFeasible.claim_two_three hcard hdeg hn p' hp' (hkeep a ha has)
      ht4 (Nat.pos_of_ne_zero hh)).1
    change degreeIn G p.center a ≤ 1 at hr1
    rcases hcounts with h | h | h <;> omega
  refine ⟨hb0, ?_⟩
  by_contra hc0
  have ht3' : degreeIn G (q 3) a = 3 := by rcases hcounts with h | h | h <;> omega
  have hr3 : degreeIn G p.center a = 3 := by rcases hcounts with h | h | h <;> omega
  have hc1 : degreeIn G (p.vertices 3) a = 1 := by rcases hcounts with h | h | h <;> omega
  have h12 : WeightedPawBlock.Pattern12 p' v := by
    rcases hpat with h | h | h
    · have hh := h.2.2.2.1.degree p' v 3 0
      have hzero : (∑ j : Fin 4, ((0 : ℕ).testBit j.val).toNat) = 0 := by decide +kernel
      rw [hzero, hv] at hh
      exact False.elim (hc0 hh)
    · have hh := h.2.2.2.degree p' v 3 0
      have hzero : (∑ j : Fin 4, ((0 : ℕ).testBit j.val).toNat) = 0 := by decide +kernel
      rw [hzero, hv] at hh
      exact False.elim (hc0 hh)
    · exact h
  have hx3 : degreeIn G p.leaf a = 3 := by rw [eightWeight_eq_rows] at hweight; omega
  have hcv3 : G.Adj (p.vertices 3) (v 3) := (h12.2.2.2 3).mpr (by decide)
  have hrv2 : G.Adj p.center (v 2) := (h12.2.2.1 2).mpr (by decide)
  have htv0 : G.Adj (q 3) (v 0) := (h12.2.1 0).mpr (by decide)
  have htv1 : G.Adj (q 3) (v 1) := (h12.2.1 1).mpr (by decide)
  have hxnot : ¬G.Adj p.leaf (v 3) := by
    intro hh
    have hm : v 3 ∈ a := hv ▸ (v.mem_support _).mpr ⟨3, rfl⟩
    exact disjoint_left.mp hdis (mem_filter.mpr ⟨hm, hh⟩) (mem_filter.mpr ⟨hm, hcv3⟩)
  have hxrow := v.adj_iff_ne_three p.leaf (hv.symm ▸ hx3) hxnot
  have hFA : Disjoint p.support v.support := by
    rw [hp, hv]
    exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset ha)
  have hpv (i j : Fin 4) : p.vertices i ≠ v j := fun he ↦ disjoint_left.mp hFA
    ((mem_tupleSupport p.vertices _).mpr ⟨i, rfl⟩) (he.symm ▸ (v.mem_support _).mpr ⟨j, rfl⟩)
  have hxt : p.leaf ≠ q 3 := fun he ↦ disjoint_left.mp hFQ
    (show p.leaf ∈ p.support from (mem_tupleSupport p.vertices _).mpr ⟨0, rfl⟩)
    (he.symm ▸ (q.mem_support _).mpr ⟨3, rfl⟩)
  exact case_two_split_factor_false hc hcard hn p hp hs ha has q hq hcase v hv
    (QuadOn.of_vertices (hpv 1 3) (hpv 3 2) p.edge13 hcv3 (v.adjacent 2).symm hrv2.symm)
    (QuadOn.of_vertices hxt (v.injective.ne (by decide : (0 : Fin 4) ≠ 1))
      ((hxrow 0).mpr (by decide)) htv0.symm htv1 ((hxrow 1).mpr (by decide)).symm)

end Erdos577.JointClaims
