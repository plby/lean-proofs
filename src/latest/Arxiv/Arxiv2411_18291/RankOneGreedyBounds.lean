import Arxiv.Arxiv2411_18291.RankOneLegalExtensions
import Arxiv.Arxiv2411_18291.GreedyEmbeddingProcess

/-! # Deterministic degree and availability bounds in rank one -/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r t i : ℕ}

omit [Fintype W] in
theorem IsAdmissible.exists_root {H : Hypergraph W (r + 1)}
    (hA : IsAdmissible H F) (hH : H.Nonempty) : ∃ e ∈ H, e.val ⊆ F := by
  obtain ⟨e, he⟩ := hH
  by_cases heF : e.val ⊆ F
  · exact ⟨e, he, heF⟩
  · obtain ⟨f, hf, hfF, _⟩ := hA e he heF
    exact ⟨f, hf, hfF⟩

omit [Fintype W] in
theorem rankOne_root_length_lt (H : Hypergraph W 1) (hH : H.Nonempty)
    (hA : IsAdmissible H F) (Φ : ℕ → F ↪ V) {θ : ℝ}
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun j : Fin t => rootImage (Φ j) f hf) θ) :
    (t : ℝ) < θ * Fintype.card V := by
  obtain ⟨f, hf, hfF⟩ := hA.exists_root hH
  have h := hroots f hf hfF (⟨∅, rfl⟩ : Block V 0)
  simpa only [familyDegree, empty_subset, filter_true, card_univ, Fintype.card_fin] using h

omit [Fintype W] [Fintype V] [DecidableEq W] in
theorem historyDegree_le_length (h : FiniteHistoryProcess.History (EmbeddingState W V) i)
    (e : Block W r) (S : Finset V) : historyDegree h e S ≤ i := by
  calc
    _ ≤ ∑ _j ∈ range i, 1 := sum_le_sum fun j _ => edgeIncidence_le_one _ _
    _ = i := by simp only [sum_const, card_range, smul_eq_mul, mul_one]

omit [Fintype W] in
theorem historyGood_of_length_lt (H : Hypergraph W (r + 1)) {L : ℝ}
    (ht : (t : ℝ) < L * Fintype.card V) (hi : i ≤ t)
    (h : FiniteHistoryProcess.History (EmbeddingState W V) i) : historyGood H F L h := by
  intro e _ S
  have hle : (historyDegree h e S.val : ℝ) ≤ t := by
    exact_mod_cast (historyDegree_le_length h e S.val).trans hi
  exact hle.trans_lt ht

theorem rankOne_history_legal_nonempty (φ : F ↪ V) (H : Hypergraph W 1)
    (B : Hypergraph V 1) {θ : ℝ} (hB : IsGraphBounded B θ) (hθ : 0 ≤ θ)
    (hw : 2 * Fintype.card W ≤ Fintype.card V)
    (hsmall : θ + H.card * θ ≤ 1 / 2)
    (ht : (t : ℝ) < θ * Fintype.card V) (hi : i ≤ t)
    (h : FiniteHistoryProcess.History (EmbeddingState W V) i) :
    (legalExtensions φ H (historyForbidden H B F h)).Nonempty := by
  have hb := (isGraphBounded_one_iff _ _).mp
    (historyForbidden_bounded (F := F) H B h hB hθ (historyGood_of_length_lt H ht hi h))
  have hN : (θ + H.card * θ) * Fintype.card V ≤ (1 / 2 : ℝ) * Fintype.card V :=
    mul_le_mul_of_nonneg_right hsmall (Nat.cast_nonneg _)
  have hW : 2 * (Fintype.card W : ℝ) ≤ Fintype.card V := by exact_mod_cast hw
  apply legalExtensions_nonempty_rankOne
  have hc : (Fintype.card W : ℝ) + (historyForbidden H B F h).card ≤ Fintype.card V := by
    linarith only [hb, hN, hW]
  exact_mod_cast hc

end Arxiv2411_18291
