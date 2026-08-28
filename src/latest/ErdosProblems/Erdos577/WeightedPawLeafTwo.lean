import ErdosProblems.Erdos577.WeightedPawFinalClassification
import ErdosProblems.Erdos577.WeightedRows

/-! A two-contact leaf selects pattern (14) from the proved final weighted classification. -/

namespace Erdos577.WeightedPawBlock

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

lemma SixPatternsWithReplacements.leaf_two (p : Paw G) (q : Quadrilateral G)
    (h : SixPatternsWithReplacements p q) (hleaf : degreeIn G p.leaf q.support = 2) :
    Pattern14 p q := by
  have hnot (mask : ℕ) (hrow : Row p q 0 mask)
      (hmask : (∑ j : Fin 4, (mask.testBit j.val).toNat) ≠ 2) : False := by
    have hr := hrow.degree p q 0 mask
    change degreeIn G p.leaf q.support = _ at hr
    exact hmask (hr.symm.trans hleaf)
  rcases h with h | h | h | h | h | h
  · have h1 := h.1
    change degreeIn G p.leaf q.support = 1 at h1
    omega
  · exact False.elim (hnot 15 h.1.2.2.1 (by decide +kernel))
  · exact False.elim (hnot 7 h.1.2.1 (by decide +kernel))
  · exact False.elim (hnot 7 h.1.2.1 (by decide +kernel))
  · exact False.elim (hnot 1 h.2.1 (by decide +kernel))
  · exact h

lemma FinalClassification.leaf_two (p : Paw G) (q : Quadrilateral G)
    (h : FinalClassification p q) (hleaf : degreeIn G p.leaf q.support = 2) :
    ∃ swap : Bool, ∃ q' : Quadrilateral G, q'.support = q.support ∧
      Pattern14 (FirstPaw.normalizedPaw p swap) q' := by
  obtain ⟨swap, q', hq', hp⟩ := h
  refine ⟨swap, q', hq', hp.leaf_two (FirstPaw.normalizedPaw p swap) q' ?_⟩
  rw [FirstPaw.normalizedPaw_leaf, hq']
  exact hleaf

end Erdos577.WeightedPawBlock
