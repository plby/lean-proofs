import Arxiv.Arxiv2411_18291.FiniteGreedyProbability
import Arxiv.Arxiv2411_18291.ExplicitDecoderPlacement

/-!
# The actual decoder-region placements succeed with high probability at n0

The event records the embeddings chosen by the ordinary greedy trajectory,
their disjoint punctured cliques, and the resulting bounded graph.
-/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem small_clique_pattern_bounds_two_q {q s r : ℕ} (hq : 2 ≤ q) (hs : s ≤ 2 * q) :
    s ≤ (4 * q) ^ (2 * q) ∧ s.choose r ≤ (4 * q) ^ (2 * q) := by
  constructor
  · exact hs.trans ((by omega : 2 * q ≤ 4 * q).trans
      (Nat.le_self_pow (by omega : 2 * q ≠ 0) (4 * q)))
  · calc
      _ ≤ 2 ^ s := Nat.choose_le_two_pow s r
      _ ≤ 2 ^ (2 * q) := Nat.pow_le_pow_right (by decide : 0 < 2) hs
      _ = 4 ^ q := by rw [pow_mul]; norm_num
      _ ≤ (4 * q) ^ q := Nat.pow_le_pow_left (by omega) q
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {s r : ℕ}

def cliquePlacementEvent (F₀ : Block W (r + 1)) (hW : Fintype.card W = s)
    (t : ℕ) (E : ℕ → Block V (r + 1)) (B : Hypergraph V (r + 1)) (θ : ℝ) :
    Set (ℕ → EmbeddingState W V) :=
  {ω | ∃ Ψ : (i : Fin t) → EmbeddingExtension (edgeRootMap F₀ (E i)),
    (∀ i : Fin t, ω (i + 1) = chosenEmbedding (Ψ i).val) ∧
      IsCliqueCover (complete V (r + 1) \ B) (fun i : Fin t => E i)
        (fun i => embeddingClique hW (Ψ i).val) ∧
      IsGraphBounded (cliqueCoverGraph (r := r) (fun i => embeddingClique hW (Ψ i).val))
        ((1 + 4 * (r + 1).factorial * s.choose (r + 1)) * θ)}

theorem greedy_event_subset_cliquePlacementEvent (F₀ : Block W (r + 1))
    (hW : Fintype.card W = s) (t : ℕ) (E : ℕ → Block V (r + 1))
    (B : Hypergraph V (r + 1)) {θ : ℝ} (hθ : 0 ≤ θ) (hB : IsGraphBounded B θ)
    (hE : Function.Injective (fun i : Fin t => E i)) (hEB : ∀ i < t, E i ∈ B) :
    greedyFamilyEvent (fun i => edgeRootMap F₀ (E i)) (complete W (r + 1)) B
        (4 * (r + 1).factorial * θ) t ⊆ cliquePlacementEvent F₀ hW t E B θ := by
  rintro ω ⟨Ψ, hΨ, hmatch⟩
  refine ⟨Ψ, hmatch,
    hΨ.cliqueCover_complement F₀ hW (fun i => E i) B Ψ hE (fun i => hEB i i.isLt), ?_⟩
  have hL : 0 ≤ 4 * (r + 1).factorial * θ := by positivity
  have hb := (hΨ.graphBounded hB hL).subgraph
    (cliqueGraph_subset_base_union_new F₀ hW (fun i => E i) B Ψ (fun i => hEB i i.isLt))
  have hc : (complete W (r + 1)).card = s.choose (r + 1) := by
    simp only [complete, card_univ, Block, Fintype.card_finset_len, hW]
  have heq : θ + (complete W (r + 1)).card * (4 * (r + 1).factorial * θ) =
      (1 + 4 * (r + 1).factorial * s.choose (r + 1)) * θ := by rw [hc]; ring
  simpa only [heq] using hb

omit [DecidableEq W] in
theorem measurableSet_cliquePlacementEvent (F₀ : Block W (r + 1))
    (hW : Fintype.card W = s) (t : ℕ) (E : ℕ → Block V (r + 1))
    (B : Hypergraph V (r + 1)) (θ : ℝ) :
    MeasurableSet (cliquePlacementEvent F₀ hW t E B θ) := by
  classical
  unfold cliquePlacementEvent
  simp only [Set.ofPred_exists, Set.ofPred_and]
  apply MeasurableSet.iUnion
  intro Ψ
  refine MeasurableSet.inter ?_ (MeasurableSet.inter ?_ ?_)
  · simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact (measurableSet_singleton (chosenEmbedding (Ψ i).val)).preimage
      (measurable_pi_apply ((i : ℕ) + 1))
  · by_cases h : IsCliqueCover (complete V (r + 1) \ B) (fun i : Fin t => E i)
        (fun i => embeddingClique hW (Ψ i).val) <;> simp [h]
  · by_cases h : IsGraphBounded
        (cliqueCoverGraph (r := r) (fun i => embeddingClique hW (Ψ i).val))
        ((1 + 4 * (r + 1).factorial * s.choose (r + 1)) * θ) <;> simp [h]

theorem indexed_clique_placement_probability_scaled {q n : ℕ}
    (F₀ : Block W (r + 1)) (hW : Fintype.card W = s)
    (hqr : r + 1 < q) (hs : s ≤ 2 * q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {A ρ : ℝ} (hA : 1 ≤ A) (hAb : A ≤ (4 * q : ℝ) ^ (24 * q))
    (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (t : ℕ) (E : ℕ → Block (Fin n) (r + 1)) (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B (A * (n : ℝ) ^ (-ρ)))
    (hE : Function.Injective (fun i : Fin t => E i)) (hEB : ∀ i < t, E i ∈ B)
    (hbound : IsEdgeFamilyBounded (fun i : Fin t => E i)
      (A * (n : ℝ) ^ (-ρ))) :
    1 - Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) <
      (unstoppedGreedyProbability (fun i => edgeRootMap F₀ (E i)) (complete W (r + 1)) B).real
        (cliquePlacementEvent F₀ hW t E B (A * (n : ℝ) ^ (-ρ))) := by
  let θ := A * (n : ℝ) ^ (-ρ)
  let Φ : ℕ → F₀.val ↪ Fin n := fun i => edgeRootMap F₀ (E i)
  obtain ⟨hw, hH⟩ := small_clique_pattern_bounds_two_q (r := r + 1) (by omega : 2 ≤ q) hs
  have hc : (complete W (r + 1)).card = s.choose (r + 1) := by
    simp only [complete, card_univ, Block, Fintype.card_finset_len, hW]
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hlo : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤ θ :=
    (Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hρhalf)).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) hA)
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hθ : 0 ≤ θ := mul_nonneg hA0 (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hhi : θ ≤ (4 * q : ℝ) ^ (24 * q) *
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)) :=
    mul_le_mul hAb (Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hρ))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _) (by positivity)
  have hroots : ∀ f ∈ complete W (r + 1), ∀ hf : f.val ⊆ F₀.val,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf) θ := by
    intro f _ hf
    have hf0 : f = F₀ :=
      Subtype.ext (eq_of_subset_of_card_le hf (by rw [f.property, F₀.property]))
    subst f
    simpa only [Φ, rootImage_edgeRootMap] using hbound
  have hb := small_pattern_uniform_greedy_probability_paper_threshold hqr hn
    (by simpa only [hW] using hw) (complete W (r + 1)) (by simpa only [hc] using hH)
    (complete_root_admissible F₀) hlo hhi t Φ B hB hroots
  exact hb.trans_le (measureReal_mono
    (greedy_event_subset_cliquePlacementEvent F₀ hW t E B hθ hB hE hEB))

theorem indexed_clique_placement_probability_at_exponent {q n : ℕ}
    (F₀ : Block W (r + 1)) (hW : Fintype.card W = s)
    (hqr : r + 1 < q) (hs : s ≤ 2 * q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {ρ : ℝ} (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (t : ℕ) (E : ℕ → Block (Fin n) (r + 1)) (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-ρ)))
    (hE : Function.Injective (fun i : Fin t => E i)) (hEB : ∀ i < t, E i ∈ B)
    (hbound : IsEdgeFamilyBounded (fun i : Fin t => E i)
      ((n : ℝ) ^ (-ρ))) :
    1 - Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) <
      (unstoppedGreedyProbability (fun i => edgeRootMap F₀ (E i)) (complete W (r + 1)) B).real
        (cliquePlacementEvent F₀ hW t E B ((n : ℝ) ^ (-ρ))) := by
  simpa only [one_mul] using indexed_clique_placement_probability_scaled F₀ hW hqr hs hn
    (A := 1) le_rfl (one_le_pow₀ (by exact_mod_cast (show 1 ≤ 4 * q by omega)))
    hρ hρhalf t E B (by simpa only [one_mul] using hB) hE hEB
    (by simpa only [one_mul] using hbound)

theorem indexed_clique_placement_probability_paper_threshold {q n : ℕ}
    (F₀ : Block W (r + 1)) (hW : Fintype.card W = s)
    (hqr : r + 1 < q) (hs : s ≤ 2 * q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (t : ℕ) (E : ℕ → Block (Fin n) (r + 1)) (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))))
    (hE : Function.Injective (fun i : Fin t => E i)) (hEB : ∀ i < t, E i ∈ B)
    (hbound : IsEdgeFamilyBounded (fun i : Fin t => E i)
      ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)))) :
    1 - Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) <
      (unstoppedGreedyProbability (fun i => edgeRootMap F₀ (E i)) (complete W (r + 1)) B).real
        (cliquePlacementEvent F₀ hW t E B ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)))) := by
  have hα := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  exact indexed_clique_placement_probability_at_exponent F₀ hW hqr hs hn le_rfl
    (by linarith only [hα]) t E B hB hE hEB hbound

end Arxiv2411_18291
