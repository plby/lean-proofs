import Arxiv.Arxiv2411_18291.RankOneGreedyBounds
import Arxiv.Arxiv2411_18291.GreedyCertainSuccess

/-! # The general rank-one greedy lemma with the printed smallness bound

The ordinary process succeeds with probability one and retains the input
degree bound. No lower density cutoff is needed.
-/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W}

theorem rankOne_greedy_probability_one (H : Hypergraph W 1) (hA : IsAdmissible H F)
    (hw : 2 * Fintype.card W ≤ Fintype.card V) {θ : ℝ} (hθ : 0 < θ)
    (hsmall : θ < (8 * (H.card : ℝ))⁻¹)
    (t : ℕ) (Φ : ℕ → F ↪ V) (B : Hypergraph V 1) (hB : IsGraphBounded B θ)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun j : Fin t => rootImage (Φ j) f hf) θ) :
    (unstoppedGreedyProbability Φ H B).real (allEdgesGreedyFamilyEvent Φ H B θ t) = 1 := by
  have hH : H.Nonempty := by
    by_contra h
    have he : H = ∅ := not_nonempty_iff_eq_empty.mp h
    simp only [he, card_empty, Nat.cast_zero, mul_zero, inv_zero] at hsmall
    exact (hθ.trans hsmall).false
  have hM : (1 : ℝ) ≤ H.card := by exact_mod_cast card_pos.mpr hH
  have hMpos : (0 : ℝ) < 8 * H.card := by positivity
  have hmul : θ * (8 * H.card) < 1 :=
    (lt_div_iff₀ hMpos).mp (by simpa only [one_div] using hsmall)
  have hMθ : θ ≤ (H.card : ℝ) * θ := le_mul_of_one_le_left hθ.le hM
  have hs : θ + H.card * θ ≤ 1 / 2 := by nlinarith only [hmul, hMθ]
  have ht := rankOne_root_length_lt H hH hA Φ hroots
  rw [allEdgesGreedyFamilyEvent_eq Φ H B t le_rfl hroots]
  apply unstopped_greedy_probability_one_of_available
  · intro ω
    exact historyGood_of_length_lt H ht le_rfl _
  · intro i hi h
    exact rankOne_history_legal_nonempty (Φ i) H B hB hθ.le hw hs ht hi.le h

theorem rankOne_greedy_paper_probability_one (H : Hypergraph W 1) (hA : IsAdmissible H F)
    (hw : 2 * Fintype.card W ≤ Fintype.card V) {θ : ℝ} (hθ : 0 < θ)
    (hsmall : θ < (8 * (H.card : ℝ))⁻¹)
    (t : ℕ) (Φ : ℕ → F ↪ V) (B : Hypergraph V 1) (hB : IsGraphBounded B θ)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun j : Fin t => rootImage (Φ j) f hf) θ) :
    (unstoppedGreedyProbability Φ H B).real
      (allEdgesGreedyFamilyEvent Φ H B (4 * θ) t) = 1 := by
  have h := rankOne_greedy_probability_one H hA hw hθ hsmall t Φ B hB hroots
  rw [allEdgesGreedyFamilyEvent_eq Φ H B t le_rfl hroots] at h
  rw [allEdgesGreedyFamilyEvent_eq Φ H B t (by linarith only [hθ] : θ ≤ 4 * θ) hroots]
  apply le_antisymm measureReal_le_one
  rw [← h]
  exact measureReal_mono (greedyFamilyEvent_mono Φ H B t (by linarith only [hθ]))

end Arxiv2411_18291
