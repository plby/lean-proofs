import ErdosProblems.Erdos577.JointSingleExchange

/-! TeX9.53: retain the original heavy block while reducing a failed row bound to CaseII. -/

namespace Erdos577.JointClaims

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

def CaseTwoCore (c : TriangleChain G) (p : Paw G) (q : Quadrilateral G) (a : Finset V) : Prop :=
  p.support = c.remainder ∧ q.support ∈ c.blocks ∧ a ∈ c.blocks ∧ a ≠ q.support ∧
    CaseTwo p q ∧ 7 ≤ degreeIn G p.center a + degreeIn G (p.vertices 3) a ∧
    13 ≤ degreeIn G (p.vertices 3) a + contacts G p.triangle a

theorem case_two_core_of_labels {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = s)
    (hcase : CaseTwo p q) :
    ∃ (d : TriangleChain G) (p' : Paw G) (q' : Quadrilateral G) (a : Finset V),
      d.Strong ∧ CaseTwoCore d p' q' a ∧ p'.triangle = p.triangle ∧
      p'.vertices 3 = p.vertices 3 := by
  have present (a : Finset V) (ha : a ∈ c.blocks) (has : a ≠ s)
      (hpair : 7 ≤ degreeIn G p.center a + degreeIn G (p.vertices 3) a)
      (hheavy : 13 ≤ degreeIn G (p.vertices 3) a + contacts G p.triangle a) :
      ∃ (d : TriangleChain G) (p' : Paw G) (q' : Quadrilateral G) (a : Finset V),
        d.Strong ∧ CaseTwoCore d p' q' a ∧ p'.triangle = p.triangle ∧
        p'.vertices 3 = p.vertices 3 := by
    refine ⟨c.presentPaw p hp, p, q, a, hc.presentPaw_strong hcard hn p hp,
      ⟨p.support_eq, ?_, ha, ?_, hcase, hpair, hheavy⟩, rfl, rfl⟩
    · change q.support ∈ c.blocks
      rwa [hq]
    · rwa [hq]
  obtain ⟨a, ha, has, hheavy⟩ := exists_heavy_block hc hcard hdeg hn p hp hs q hq (Or.inr hcase)
  obtain ⟨hx0, ht0, hweighted⟩ := heavy_leaves_zero hc hcard hdeg hn p hp hs ha has q hq
    (Or.inr hcase) hheavy
  by_cases hpair : 7 ≤ degreeIn G p.center a + degreeIn G (p.vertices 3) a
  · exact present a ha has hpair hweighted
  have hother : 7 ≤ degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a := by
    have he := p.contacts_triangle a
    change contacts G p.triangle a = degreeIn G p.center a +
      (degreeIn G (p.vertices 2) a + degreeIn G (p.vertices 3) a) at he
    omega
  obtain ⟨b, hb, hbs, halt⟩ := exists_eight_alternative hc hcard hdeg hn p hp hs q hq hcase
  rcases halt with hzero | hpositive
  · obtain ⟨_, _, η, hsum, hT⟩ := hzero
    have hη := η.isLt
    have hr4 := degreeIn_le_card G p.center b
    rw [(c.property.blocks_quad b hb).card] at hr4
    exact present b hb hbs (by omega) (by omega)
  have hr4 := degreeIn_le_card G p.center b
  rw [(c.property.blocks_quad b hb).card] at hr4
  have ht3 : 3 ≤ degreeIn G (q 3) b := by
    rcases hpositive with ⟨η, he, _⟩ | h | h
    · omega
    · omega
    · omega
  have hba : b ≠ a := by intro he; rw [he, ht0] at ht3; omega
  by_cases hnewpair : 7 ≤ degreeIn G (q 3) b + degreeIn G p.center b
  · have hFQ : Disjoint p.support q.support := by
      rw [hp, hq]
      exact c.property.remainder_disjoint.mono_right (c.blockPartition.block_subset hs)
    obtain ⟨d, hd, _, _, hp', _, _, _, hkeep⟩ :=
      exists_exposed_chain hc hcard hn p hp hs q hq hFQ (Or.inr hcase)
    let p' := exposedPaw p q hFQ (Or.inr hcase)
    obtain ⟨v, hv⟩ := c.property.blocks_quad b hb
    obtain ⟨q', hq', hcase'⟩ := case_two_labels p' v (by rw [hv]; exact hnewpair)
    have htri : p'.triangle = p.triangle := exposedPaw_triangle p q hFQ (Or.inr hcase)
    refine ⟨d, p', q', a, hd, ⟨hp', ?_, hkeep a ha has, ?_, hcase', hother, ?_⟩, htri, rfl⟩
    · rw [hq', hv]
      exact hkeep b hb hbs
    · rw [hq', hv]
      exact hba.symm
    · change 13 ≤ degreeIn G (p.vertices 3) a + contacts G p'.triangle a
      rwa [htri]
  have hspecial : degreeIn G p.leaf b = 4 ∧ degreeIn G p.center b = 3 ∧
      degreeIn G (p.vertices 2) b = 1 := by
    rcases hpositive with ⟨η, he, _⟩ | h | h
    · omega
    · omega
    · exact ⟨h.1, by omega, by omega⟩
  obtain ⟨d, p', s', hd, hp', hcenter, hthird, htri, hs', hxs', hfull, hsecond, _, _, hkeep⟩ :=
    exists_single_neighbor_exchange hc hcard hn p hp hb hspecial.1 hspecial.2.1 hspecial.2.2
  obtain ⟨v, hv⟩ := d.property.blocks_quad s' hs'
  obtain ⟨q', hq', hcase'⟩ := case_two_labels p' v (by rw [hv]; omega)
  have hxa : p.leaf ∉ a := (c.presentPaw p hp).terminal_not_mem_block ha
  refine ⟨d, p', q', a, hd, ⟨hp', ?_, hkeep a ha hba.symm, ?_, hcase', ?_, ?_⟩, htri, hthird⟩
  · rwa [hq', hv]
  · rw [hq', hv]
    intro he
    exact hxa (he.symm ▸ hxs')
  · rwa [hcenter, hthird]
  · rwa [hthird, htri]

theorem case_two_core_of_second_failure {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks)
    (hfail : 7 ≤ degreeIn G p.leaf s + degreeIn G (p.vertices 2) s) :
    ∃ (d : TriangleChain G) (p' : Paw G) (q' : Quadrilateral G) (a : Finset V),
      d.Strong ∧ CaseTwoCore d p' q' a ∧ p'.triangle = p.triangle ∧
      p'.vertices 3 = p.vertices 3 := by
  obtain ⟨q, hq⟩ := c.property.blocks_quad s hs
  obtain ⟨v, hv, hcase⟩ := case_two_labels p q (by rw [hq]; exact hfail)
  exact case_two_core_of_labels hc hcard hdeg hn p hp hs v (hv.trans hq) hcase

theorem case_two_reduction {c : TriangleChain G} (hc : c.Feasible) {k : ℕ}
    (hcard : Fintype.card V = 4 * k) (hdeg : ∀ v, 2 * k ≤ G.degree v) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {s : Finset V} (hs : s ∈ c.blocks)
    (hfail : 7 ≤ degreeIn G p.leaf s + degreeIn G (p.vertices 2) s ∨
      7 ≤ degreeIn G p.leaf s + degreeIn G (p.vertices 3) s) :
    ∃ (d : TriangleChain G) (p' : Paw G) (q' : Quadrilateral G) (a : Finset V),
      d.Strong ∧ CaseTwoCore d p' q' a ∧ p'.triangle = p.triangle := by
  rcases hfail with h | h
  · obtain ⟨d, p', q', a, hd, hcore, htri, _⟩ :=
      case_two_core_of_second_failure hc hcard hdeg hn p hp hs h
    exact ⟨d, p', q', a, hd, hcore, htri⟩
  · have hp' : p.swapNoncentral.support = c.remainder := by rw [Paw.swapNoncentral_support, hp]
    obtain ⟨d, p', q', a, hd, hcore, htri, _⟩ :=
      case_two_core_of_second_failure hc hcard hdeg hn p.swapNoncentral hp' hs h
    rw [Paw.swapNoncentral_triangle] at htri
    exact ⟨d, p', q', a, hd, hcore, htri⟩

end Erdos577.JointClaims
