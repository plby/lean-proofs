import ErdosProblems.Erdos1105.SeparatedLeafSwap
import ErdosProblems.Erdos1105.DenseConnectedRepresentative
import ErdosProblems.Erdos1105.FullRepresentative

namespace Erdos1105

open SimpleGraph

theorem IsFullRepresentative.toColorRepresentative {V C : Type*}
    {c : (⊤ : SimpleGraph V).edgeSet → C} {R : SimpleGraph V} (hR : IsFullRepresentative c R) :
    ColorRepresentative ⊤ (extendColor c) R := by
  refine ⟨le_top, hR.rainbow, ?_⟩
  intro e he
  obtain ⟨f, hf⟩ := hR.palette (c ⟨e, he⟩)
  exact ⟨f.val, f.property, hf.trans (extendColor_edge c ⟨e, he⟩).symm⟩

theorem IsFullRepresentative.transfer {V C : Type*}
    {c : (⊤ : SimpleGraph V).edgeSet → C} {R Q : SimpleGraph V} (hR : IsFullRepresentative c R)
    (hQ : ColorRepresentative ⊤ (extendColor c) Q) : IsFullRepresentative c Q := by
  refine ⟨hQ.rainbow, ?_⟩
  intro i
  obtain ⟨e, he⟩ := hR.palette i
  obtain ⟨f, hf, hc⟩ := hQ.palette e.val (edgeSet_mono le_top e.property)
  exact ⟨⟨f, hf⟩, hc.trans he⟩

theorem IsFullRepresentative.nat_card_edges {V C : Type*} [Fintype V] [Fintype C]
    {c : (⊤ : SimpleGraph V).edgeSet → C} {R : SimpleGraph V} (hR : IsFullRepresentative c R) :
    Nat.card R.edgeSet = Fintype.card C := by
  classical
  rw [Nat.card_eq_fintype_card, ← edgeFinset_card, hR.card_edges]

/-- The general disconnected case reduces to deleting a vertex while
retaining every color. The dense boundary lemma ensures `n-1 ≥ k`. -/
theorem disconnected_high_colors_reduction {V C : Type*} [Fintype V] [Fintype C]
    (c : (⊤ : SimpleGraph V).edgeSet → C) {k : ℕ} (hk : 5 ≤ k) (hn : k ≤ Fintype.card V)
    (hfree : ∀ f : (pathGraph k).Copy (⊤ : SimpleGraph V), ¬IsRainbow f c)
    (R : SimpleGraph V) (hR : IsFullRepresentative c R)
    (hno : ∀ Q : SimpleGraph V, IsFullRepresentative c Q → ¬Q.Preconnected)
    (hq : pathFormula (Fintype.card V) k < Fintype.card C) :
    k < Fintype.card V ∧ ∃ Q, IsFullRepresentative c Q ∧ ∃ x, Q.IsIsolated x := by
  classical
  have hV : Nonempty V := Fintype.card_pos_iff.mp (by omega)
  let := hV
  have hnlarge : k < Fintype.card V := by
    by_contra! hsmall
    have heq : Fintype.card V = k := by omega
    have hclique : (Fintype.card V - 2).choose 2 + 1 < Nat.card R.edgeSet := by
      rw [hR.nat_card_edges]
      have hle : (k - 2).choose 2 + 1 ≤ pathFormula (Fintype.card V) k := le_max_left _ _
      rw [heq]
      exact hle.trans_lt hq
    obtain ⟨Q, hQ, hconn⟩ := exists_connected_representative_of_dense (extendColor c)
      hR.toColorRepresentative hclique
    exact hno Q (hR.transfer hQ) hconn
  obtain ⟨Q, H, hsep⟩ := exists_separatedRepresentative (⊤ : SimpleGraph V) (extendColor c)
  have hQ := hR.transfer hsep.representative
  have hhigh : pathFormula (Fintype.card V) k < Nat.card Q.edgeSet := by
    rw [hQ.nat_card_edges]
    exact hq
  obtain ⟨J, hJ, x, hx⟩ := hsep.high_colors_isolated_representative c hk hn hfree (hno Q hQ) hhigh
  exact ⟨hnlarge, J, hR.transfer hJ, x, hx⟩

end Erdos1105

#print axioms Erdos1105.disconnected_high_colors_reduction
