import ErdosProblems.Erdos577.FirstPawSixExcluded
import ErdosProblems.Erdos577.FirstPawFourExcluded
import ErdosProblems.Erdos577.FirstPawSevenExcluded
import ErdosProblems.Erdos577.FirstPawLeafCount

/-! Only patterns (3) and (8) survive the first classification, with every outside factor
and the sharp degree bounds needed in the subsequent core arguments. -/

namespace Erdos577

open Finset

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

namespace PawBlock

def FinalClassification (p : Paw G) (q : Quadrilateral G) : Prop :=
  degreeIn G p.leaf q.support = 1 ∧ contacts G p.support q.support = 9 ∧
    OutsideFactor p q ∧ ∃ swap : Bool, ∃ q' : Quadrilateral G, q'.support = q.support ∧
      (Pattern3 (FirstPaw.normalizedPaw p swap) q' ∨
        Pattern8 (FirstPaw.normalizedPaw p swap) q')

lemma surviving_counts (p : Paw G) (q : Quadrilateral G) (h : Pattern3 p q ∨ Pattern8 p q) :
    degreeIn G p.leaf q.support = 1 ∧ contacts G p.support q.support = 9 := by
  have he : (∑ j : Fin 4, ((1 : ℕ).testBit j.val).toNat) = 1 := by decide +kernel
  rcases h with h | h
  · constructor
    · exact (WeightedPawBlock.Row.degree p q 0 1 (h.2 0)).trans he
    · rw [h.2.contacts_eq p q ![1, 15, 9, 3]]
      decide +kernel
  · constructor
    · exact (WeightedPawBlock.Row.degree p q 0 1 (h.2 0)).trans he
    · rw [h.2.contacts_eq p q ![1, 15, 15, 0]]
      decide +kernel

end PawBlock

variable [Fintype V]

theorem TriangleChain.Feasible.first_paw_final {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hheavy : 9 ≤ contacts G p.support q.support) (hleaf : 0 < degreeIn G p.leaf q.support) :
    PawBlock.FinalClassification p q := by
  obtain ⟨_, _, swap, q', hq', hpat⟩ :=
    hc.first_paw_classification hcard hdeg hn p hp hb q hq hheavy hleaf
  let p' := FirstPaw.normalizedPaw p swap
  have hp' : p'.support = c.remainder := by rw [FirstPaw.normalizedPaw_support, hp]
  have hh : 9 ≤ contacts G p'.support q'.support := by
    rw [FirstPaw.normalizedPaw_support, hq']
    exact hheavy
  have hsurv : (PawBlock.Pattern3 p' q' ∧ PawBlock.OutsideFactor p' q') ∨
      (PawBlock.Pattern8 p' q' ∧ PawBlock.OutsideFactor p' q') := by
    rcases hpat with h | h | h | h | h | h
    · exact Or.inl h
    · exact False.elim (hc.not_first_paw_pattern4 hcard hdeg hn p' hp' hb q' (hq'.trans hq) hh h)
    · exact False.elim (hc.not_first_paw_pattern5 hcard hdeg hn p' hp' hb q' (hq'.trans hq) hh h)
    · exact False.elim (hc.not_first_paw_pattern6 hcard hdeg hn p' hp' hb q' (hq'.trans hq) hh h)
    · exact False.elim (hc.not_first_paw_pattern7 hcard hdeg hn p' hp' hb q' (hq'.trans hq) h)
    · exact Or.inr h
  have hpattern : PawBlock.Pattern3 p' q' ∨ PawBlock.Pattern8 p' q' := hsurv.imp And.left And.left
  have hout' : PawBlock.OutsideFactor p' q' := hsurv.elim And.right And.right
  obtain ⟨hl, hnine⟩ := PawBlock.surviving_counts p' q' hpattern
  rw [FirstPaw.normalizedPaw_leaf, hq'] at hl
  rw [FirstPaw.normalizedPaw_support, hq'] at hnine
  refine ⟨hl, hnine, ?_, swap, q', hq', hpattern⟩
  intro z hz hrow
  have hz' : z ∉ p'.support ∪ q'.support := by
    rw [FirstPaw.normalizedPaw_support, hq']
    exact hz
  have hr' : 2 ≤ degreeIn G z q'.support := by rw [hq']; exact hrow
  have hf := hout' z hz' hr'
  rwa [FirstPaw.normalizedPaw_triangle, hq'] at hf

theorem TriangleChain.Feasible.positive_leaf_contacts_le_nine {c : TriangleChain G}
    (hc : c.Feasible) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hleaf : 0 < degreeIn G p.leaf q.support) : contacts G p.support q.support ≤ 9 := by
  by_cases hh : 9 ≤ contacts G p.support q.support
  · exact (hc.first_paw_final hcard hdeg hn p hp hb q hq hh hleaf).2.1.le
  · omega

theorem TriangleChain.Feasible.two_leaf_contacts_le_eight {c : TriangleChain G}
    (hc : c.Feasible) {k : ℕ} (hcard : Fintype.card V = 4 * k)
    (hdeg : ∀ u, 2 * k ≤ G.degree u) (hn : ¬HasPacking G k)
    (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b)
    (hleaf : 2 ≤ degreeIn G p.leaf q.support) : contacts G p.support q.support ≤ 8 := by
  by_contra! hh
  have he := (hc.first_paw_final hcard hdeg hn p hp hb q hq (by omega) (by omega)).1
  omega

theorem TriangleChain.Feasible.paw_contacts_le_twelve {c : TriangleChain G} (hc : c.Feasible)
    {k : ℕ} (hcard : Fintype.card V = 4 * k) (hdeg : ∀ u, 2 * k ≤ G.degree u)
    (hn : ¬HasPacking G k) (p : Paw G) (hp : p.support = c.remainder)
    {b : Finset V} (hb : b ∈ c.blocks) (q : Quadrilateral G) (hq : q.support = b) :
    contacts G p.support q.support ≤ 12 := by
  by_cases hz : degreeIn G p.leaf q.support = 0
  · have h1 := degreeIn_le_card G (p.vertices 1) q.support
    have h2 := degreeIn_le_card G (p.vertices 2) q.support
    have h3 := degreeIn_le_card G (p.vertices 3) q.support
    rw [q.card_support] at h1 h2 h3
    have he := p.contacts_support q.support
    rw [p.contacts_triangle] at he
    change contacts G p.support q.support = degreeIn G p.leaf q.support +
      (degreeIn G (p.vertices 1) q.support +
      (degreeIn G (p.vertices 2) q.support + degreeIn G (p.vertices 3) q.support)) at he
    omega
  · have hh := hc.positive_leaf_contacts_le_nine hcard hdeg hn p hp hb q hq (by omega)
    omega

end Erdos577
