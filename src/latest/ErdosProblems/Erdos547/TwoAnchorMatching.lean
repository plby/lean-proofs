import ErdosProblems.Erdos547.PrivateCapacityCase
import ErdosProblems.Erdos547.TwoAnchorResidual
import ErdosProblems.Erdos547.WeightNormalization

/-!
# The two-anchor `(k, k/2)` matching lemma

The anchor with saturation `k` and its neighbour with saturation `k/2`
support any two positive total budgets summing to `k`, in one of the two
anchor orders. Both skew parameters may be zero.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem exists_two_anchor_matching_exact (μ : FractionalMatching G) (w : EdgeWeights G)
    {c d : V} (hcd : G.Adj c d) (γ δ a b : ℝ) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ)
    (ha : 0 < a) (hb : 0 < b)
    (hc : w.saturation μ.load c = a + b) (hd : w.saturation μ.load d = (a + b) / 2) :
    ∃ σ : SkewMatching G γ, ∃ τ : SkewMatching G δ,
      (AnchoredPair σ τ w c d ∨ AnchoredPair σ τ w d c) ∧
      PairDominated σ τ μ ∧ σ.total = a ∧ τ.total = b := by
  classical
  obtain ⟨D⟩ := exists_saturation_decomposition μ w d
  obtain ⟨E⟩ := exists_cross_anchor_split D.cross D.active
    (D.cross_between.crosses disjoint_compl_right)
    (w.truncate D.full.load D.full.load_nonneg) c
  let X := 2 * D.full.total + E.privatePart.total
  by_cases hA : a ≤ X
  · obtain ⟨σ, τ, hp, hdom, htσ, htτ⟩ :=
      D.pair_of_private_capacity E hcd γ δ hγ hδ a b ha.le hb.le hc.ge hA
    exact ⟨σ, τ, Or.inr hp, hdom, htσ, htτ⟩
  by_cases hB : b ≤ X
  · obtain ⟨τ, σ, hp, hdom, htτ, htσ⟩ :=
      D.pair_of_private_capacity E hcd δ γ hδ hγ b a hb.le ha.le (by linarith) hB
    exact ⟨σ, τ, Or.inl hp.swap, hdom.swap, htσ, htτ⟩
  let r := a - X
  let s := b - X
  have hr : 0 < r := sub_pos.mpr (lt_of_not_ge hA)
  have hs : 0 < s := sub_pos.mpr (lt_of_not_ge hB)
  have hsum : r + s = 2 * E.shared.total := by
    have hD := D.saturation_eq
    rw [hd, E.total_eq] at hD
    dsimp [r, s, X]
    linarith
  obtain ⟨_, _, hsumA, _⟩ := positive_skew_parts r γ hr hγ
  obtain ⟨_, _, hsumB, _⟩ := positive_skew_parts s δ hs hδ
  rcases residual_orientation_dichotomy (r / (1 + γ)) (γ * (r / (1 + γ)))
    (s / (1 + δ)) (δ * (s / (1 + δ))) E.shared.total (by linarith) with hL | hR
  · obtain ⟨σ, τ, hp, hdom, ht, hlarge⟩ :=
      D.assemble_residual_totals E hcd γ δ r s hγ hδ hr hs hsum hL
    have hσ : σ.total = a := by change σ.total = X + (a - X) at ht; linarith
    have hτ : b ≤ τ.total := by rw [hc, hσ] at hlarge; linarith
    obtain ⟨σ', τ', hp', hdom', htσ', htτ'⟩ := hp.trim hdom a b ha.le hb.le hσ.ge hτ
    exact ⟨σ', τ', Or.inr hp', hdom', htσ', htτ'⟩
  · obtain ⟨τ, σ, hp, hdom, ht, hlarge⟩ :=
      D.assemble_residual_totals E hcd δ γ s r hδ hγ hs hr (by linarith) hR
    have hτ : τ.total = b := by change τ.total = X + (b - X) at ht; linarith
    have hσ : a ≤ σ.total := by rw [hc, hτ] at hlarge; linarith
    obtain ⟨τ', σ', hp', hdom', htτ', htσ'⟩ := hp.trim hdom b a hb.le ha.le hτ.ge hσ
    exact ⟨σ', τ', Or.inl hp'.swap, hdom'.swap, htσ', htτ'⟩

theorem exists_two_anchor_matching (μ : FractionalMatching G) (w : EdgeWeights G)
    {c d : V} (hcd : G.Adj c d) (γ δ a b : ℝ) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ)
    (ha : 0 < a) (hb : 0 < b)
    (hc : a + b ≤ w.saturation μ.load c) (hd : (a + b) / 2 ≤ w.saturation μ.load d) :
    ∃ σ : SkewMatching G γ, ∃ τ : SkewMatching G δ,
      (AnchoredPair σ τ w c d ∨ AnchoredPair σ τ w d c) ∧
      PairDominated σ τ μ ∧ σ.total = a ∧ τ.total = b := by
  obtain ⟨w', hw', hc', hd'⟩ := w.exists_two_prescribed_saturations μ.load μ.load_nonneg
    hcd.ne (a + b) ((a + b) / 2) (by linarith) (by linarith) hc hd
  obtain ⟨σ, τ, hp, hdom, hσ, hτ⟩ :=
    exists_two_anchor_matching_exact μ w' hcd γ δ a b hγ hδ ha hb hc' hd'
  exact ⟨σ, τ, hp.imp (fun h ↦ h.mono_weights hw') (fun h ↦ h.mono_weights hw'), hdom, hσ, hτ⟩

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_two_anchor_matching
