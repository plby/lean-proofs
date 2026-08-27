import Arxiv.Arxiv2411_18291.FiniteGreedyProbability

/-! # Probability of separated placements produced by the ordinary greedy process -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {F : Finset W} {r : ℕ}

def separatedGreedyFamilyEvent (Φ : ℕ → F ↪ V) (Rel : ℕ → ℕ → Prop)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) (L : ℝ) (t : ℕ) :
    Set (ℕ → EmbeddingState W V) :=
  {ω | ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
    IsGreedyFamily (fun i => Φ i) H B Ψ L ∧
      (∀ i j : Fin t, i < j → Rel i j →
        Disjoint ((univ \ F).map (Ψ i).val) ((univ \ F).map (Ψ j).val)) ∧
      ∀ i : Fin t, ω (i + 1) = chosenEmbedding (Ψ i).val}

theorem prescribed_separated_event_subset (Φ : ℕ → F ↪ V) (Rel : ℕ → ℕ → Prop)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) (L : ℝ) (t : ℕ) :
    prescribedGreedyFamilyEvent Φ (separatedCandidates Φ Rel) H B L t ⊆
      separatedGreedyFamilyEvent Φ Rel H B L t := by
  rintro ω ⟨Ψ, hΨ, hmem, hmatch⟩
  exact ⟨Ψ, hΨ, separatedCandidates_disjoint Φ Rel ω Ψ hmem hmatch, hmatch⟩

theorem measurableSet_separatedGreedyFamilyEvent (Φ : ℕ → F ↪ V) (Rel : ℕ → ℕ → Prop)
    (H : Hypergraph W (r + 1)) (B : Hypergraph V (r + 1)) (L : ℝ) (t : ℕ) :
    MeasurableSet (separatedGreedyFamilyEvent Φ Rel H B L t) := by
  classical
  unfold separatedGreedyFamilyEvent
  simp only [Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro Ψ
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · by_cases h : IsGreedyFamily (fun i => Φ i) H B Ψ L <;> simp [h]
  · by_cases h : ∀ i j : Fin t, i < j → Rel i j →
        Disjoint ((univ \ F).map (Ψ i).val) ((univ \ F).map (Ψ j).val) <;> simp [h]
  · simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact (measurableSet_singleton (chosenEmbedding (Ψ i).val)).preimage
      (measurable_pi_apply ((i : ℕ) + 1))

theorem separated_greedy_probability_paper_threshold {q n d : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (H : Hypergraph W (r + 1)) (hH : H.card ≤ n)
    (hw : 4 * Fintype.card W ^ 2 ≤ n)
    (hsize : 4 * Fintype.card W * (d * Fintype.card W) ≤ n)
    (hadm : IsAdmissible H F) {θ : ℝ}
    (hlo : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ θ)
    (hsmall : H.card * (θ + H.card * (8 * (r + 1).factorial * θ)) ≤ 1 / 4)
    (t : ℕ) (Φ : ℕ → F ↪ Fin n) (Rel : ℕ → ℕ → Prop)
    (B : Hypergraph (Fin n) (r + 1)) (hB : IsGraphBounded B θ)
    (hrel : ∀ i < t, (priorRelated Rel i).card ≤ d)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ) :
    1 - Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) <
      (unstoppedPrescribedGreedyProbability Φ (separatedCandidates Φ Rel) H B).real
        (separatedGreedyFamilyEvent Φ Rel H B (8 * (r + 1).factorial * θ) t) := by
  have hθ : 0 ≤ θ := (Real.rpow_nonneg (Nat.cast_nonneg n) _).trans hlo
  have hL : 4 * ((r + 1).factorial : ℝ) * θ / (1 / 2) =
      8 * (r + 1).factorial * θ := by ring
  have hhalf : (1 / 2 : ℝ) / 2 = 1 / 4 := by norm_num
  have hscaled : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ θ / (1 / 2) := by
    linarith only [hlo, hθ]
  have hb := unstopped_prescribed_probability_paper_threshold hqr hn H hH hadm hθ
    (by norm_num : (0 : ℝ) < 1 / 2) hscaled
    (by simpa only [hL, hhalf] using hsmall) t Φ (separatedCandidates Φ Rel) B hB
    (separatedCandidates_lower_bound Φ Rel H _ hrel
      (by simpa only [Fintype.card_fin] using hw)
      (by simpa only [Fintype.card_fin] using hsize)) hroots
  rw [hL] at hb
  exact hb.trans_le (measureReal_mono (prescribed_separated_event_subset Φ Rel H B _ t))

theorem small_pattern_separated_probability_paper_threshold {q n d : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (H : Hypergraph W (r + 1)) (hH : H.card ≤ (4 * q) ^ (2 * q))
    (hadm : IsAdmissible H F) (hd : d ≤ (4 * q) ^ (8 * q))
    {A ρ : ℝ} (hA : 1 ≤ A) (hAb : A ≤ (4 * q : ℝ) ^ (24 * q))
    (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (t : ℕ) (Φ : ℕ → F ↪ Fin n) (Rel : ℕ → ℕ → Prop)
    (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B (A * (n : ℝ) ^ (-ρ)))
    (hrel : ∀ i < t, (priorRelated Rel i).card ≤ d)
    (hroots : ∀ f ∈ H, ∀ hf : f.val ⊆ F,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) (A * (n : ℝ) ^ (-ρ))) :
    1 - Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) <
      (unstoppedPrescribedGreedyProbability Φ (separatedCandidates Φ Rel) H B).real
        (separatedGreedyFamilyEvent Φ Rel H B
          (8 * (r + 1).factorial * (A * (n : ℝ) ^ (-ρ))) t) := by
  obtain ⟨hnpos, hsize, hsep, hsmall, _⟩ :=
    small_pattern_separated_greedy_numerics hqr hn hw hH hd hA hAb hρ hρhalf
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hnpos
  have hMsize : H.card ≤ n := hH.trans
    ((Nat.pow_le_pow_right (by omega) (by omega : 2 * q ≤ 90 * q)).trans
      ((boost_threshold_le_paper_threshold hqr).trans hn))
  have hlo : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ A * (n : ℝ) ^ (-ρ) :=
    (Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hρhalf)).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) hA)
  exact separated_greedy_probability_paper_threshold hqr hn H hMsize hsize hsep hadm
    hlo hsmall t Φ Rel B hB hrel hroots

end Arxiv2411_18291
