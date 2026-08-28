import ErdosProblems.Erdos577.JointCoreRefinedModel
import ErdosProblems.Erdos577.JointCorePatternTransport
import ErdosProblems.Erdos577.WeightedRows

/-! Exact arbitrary-graph rows for the finite maximal-core relabeling. -/

namespace Erdos577.JointCore

open Finset
open scoped BigOperators

variable {V : Type*} [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] in
lemma SourcePattern.diagonal_eq (tag : Fin 8) (p : Paw G) (q : Quadrilateral G)
    (h : SourcePattern tag p q) : Unattached.diagonal q = diagonal tag := by
  have h0 := h.1
  have h1 := h.2.1
  have hf : ∀ d e : Fin 4,
      (d.val.testBit 0 = true ↔ e.val.testBit 0 = true) →
      (d.val.testBit 1 = true ↔ e.val.testBit 1 = true) → d = e := by decide +kernel
  exact hf _ _ ((Unattached.diagonal_first q).trans h0) ((Unattached.diagonal_second q).trans h1)

def secondRow (p : Paw G) (q : Quadrilateral G) : Fin 16 :=
  row (PawEncoding.encoded p q).val 2

omit [DecidableEq V] in
lemma secondRow_bit (p : Paw G) (q : Quadrilateral G) (j : Fin 4) :
    (secondRow p q).val.testBit j.val = decide (G.Adj (p.vertices 2) (q j)) := by
  rw [secondRow, row_bit, PawEncoding.encoded_bit]

omit [DecidableEq V] in
lemma SourcePattern.allowed_second (tag : Fin 8) (p : Paw G) (q : Quadrilateral G)
    (h : SourcePattern tag p q) : Refinement.Allowed tag (secondRow p q) := by
  intro j
  have hj := h.2.2 2 j (by decide)
  change ((secondLower tag).testBit j.val = true → G.Adj (p.vertices 2) (q j)) ∧
    (G.Adj (p.vertices 2) (q j) → (secondUpper tag).testBit j.val = true) at hj
  rw [secondRow_bit]
  exact ⟨fun hh ↦ decide_eq_true (hj.1 hh), fun hh ↦ hj.2 (of_decide_eq_true hh)⟩

omit [DecidableEq V] in
lemma SourcePattern.refinement_row (tag : Fin 8) (p : Paw G) (q : Quadrilateral G)
    (h : SourcePattern tag p q) (i : Fin 4) (hi : i ≠ 0) :
    WeightedPawBlock.Row p q i (Refinement.rows tag (secondRow p q) i) := by
  intro j
  fin_cases i
  · exact False.elim (hi rfl)
  · have hj := h.2.2 1 j (by decide)
    exact ⟨hj.2, hj.1⟩
  · change G.Adj (p.vertices 2) (q j) ↔ (secondRow p q).val.testBit j.val = true
    rw [secondRow_bit, decide_eq_true_eq]
  · have hj := h.2.2 3 j (by decide)
    exact ⟨hj.2, hj.1⟩

lemma SourcePattern.refinement_counts (tag : Fin 8) (p : Paw G) (q : Quadrilateral G)
    (h : SourcePattern tag p q) :
    degreeIn G p.center q.support = Refinement.count tag (secondRow p q) 1 ∧
    degreeIn G (p.vertices 2) q.support = Refinement.count tag (secondRow p q) 2 ∧
    degreeIn G (p.vertices 3) q.support = Refinement.count tag (secondRow p q) 3 ∧
    contacts G p.triangle q.support = Refinement.count tag (secondRow p q) 1 +
      Refinement.count tag (secondRow p q) 2 + Refinement.count tag (secondRow p q) 3 := by
  have hr := (h.refinement_row tag p q 1 (by decide)).degree p q 1 _
  have hb := (h.refinement_row tag p q 2 (by decide)).degree p q 2 _
  have hc := (h.refinement_row tag p q 3 (by decide)).degree p q 3 _
  refine ⟨hr, hb, hc, ?_⟩
  rw [p.contacts_triangle, hr, hb, hc, Nat.add_assoc]
  rfl

lemma SourcePattern.bad_pattern_counts (tag : Fin 8) (p : Paw G) (q : Quadrilateral G)
    (h : SourcePattern tag p q) (htag : tag = 2 ∨ tag = 3) :
    degreeIn G p.center q.support + degreeIn G (p.vertices 3) q.support = 7 ∧
      contacts G p.triangle q.support = 9 := by
  have hf : ∀ tag : Fin 8, ∀ b : Fin 16, Refinement.Allowed tag b →
      (tag = 2 ∨ tag = 3) →
      Refinement.count tag b 1 + Refinement.count tag b 3 = 7 ∧
      Refinement.count tag b 1 + Refinement.count tag b 2 + Refinement.count tag b 3 = 9 := by
    decide +kernel
  obtain ⟨hr, _, hc, hT⟩ := h.refinement_counts tag p q
  rw [hr, hc, hT]
  exact hf tag (secondRow p q) (h.allowed_second tag p q) htag

lemma SourcePattern.bad_tags_excluded (tag : Fin 8) (p : Paw G) (q : Quadrilateral G)
    (h : SourcePattern tag p q)
    (hseven : degreeIn G p.center q.support + degreeIn G (p.vertices 3) q.support = 7 →
      10 ≤ contacts G p.triangle q.support) : tag ≠ 2 ∧ tag ≠ 3 := by
  have hnot (ht : tag = 2 ∨ tag = 3) : False := by
    obtain ⟨hpair, hT⟩ := h.bad_pattern_counts tag p q ht
    have hbound := hseven hpair
    omega
  exact ⟨fun he ↦ hnot (Or.inl he), fun he ↦ hnot (Or.inr he)⟩

end Erdos577.JointCore
