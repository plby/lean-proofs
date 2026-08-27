import Arxiv.Arxiv2411_18291.FiniteGreedyProbability
import Arxiv.Arxiv2411_18291.ExplicitEliminationPlacements

/-! # High-probability cancellation placements with both prescribed roots -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r : ℕ}

def eliminationPlacementEvent (S : ExchangeSystem W q (r + 1)) (N : Block W q)
    (t : ℕ) (P Q : Fin t → Block V q) (Φ : ℕ → ↥(S.base.val ∪ N.val) ↪ V)
    (B : Hypergraph V (r + 1)) (θ L : ℝ) : Set (ℕ → EmbeddingState W V) :=
  {ω | ∃ Ψ : (i : Fin t) → EmbeddingExtension (Φ i),
    (IsGreedyFamily (fun i => Φ i) S.graph B Ψ L ∧
      (∀ i, mapBlock (Ψ i).val S.base = P i ∧ mapBlock (Ψ i).val N = Q i) ∧
      IsGraphBounded
        (B ∪ greedyFamilyGraph (S.base.val ∪ N.val) S.graph (fun i => (Ψ i).val))
        (θ + S.graph.card * L)) ∧
      ∀ i : Fin t, ω (i + 1) = chosenEmbedding (Ψ i).val}

theorem greedy_event_subset_eliminationPlacementEvent
    (S : ExchangeSystem W q (r + 1)) (N : Block W q)
    (t : ℕ) (P Q : Fin t → Block V q) (Φ : ℕ → ↥(S.base.val ∪ N.val) ↪ V)
    (B : Hypergraph V (r + 1)) {θ L : ℝ} (hB : IsGraphBounded B θ) (hL : 0 ≤ L)
    (hΦP : ∀ i : Fin t, rootImage (Φ i) S.base subset_union_left = P i)
    (hΦQ : ∀ i : Fin t, rootImage (Φ i) N subset_union_right = Q i) :
    greedyFamilyEvent Φ S.graph B L t ⊆ eliminationPlacementEvent S N t P Q Φ B θ L := by
  rintro ω ⟨Ψ, hΨ, hmatch⟩
  exact ⟨Ψ, ⟨hΨ, fun i => pair_extension_roots (Φ i) (hΦP i) (hΦQ i) (Ψ i),
    hΨ.graphBounded hB hL⟩, hmatch⟩

theorem measurableSet_eliminationPlacementEvent
    (S : ExchangeSystem W q (r + 1)) (N : Block W q)
    (t : ℕ) (P Q : Fin t → Block V q) (Φ : ℕ → ↥(S.base.val ∪ N.val) ↪ V)
    (B : Hypergraph V (r + 1)) (θ L : ℝ) :
    MeasurableSet (eliminationPlacementEvent S N t P Q Φ B θ L) := by
  classical
  unfold eliminationPlacementEvent
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro Ψ
  rw [Set.ofPred_and]
  apply MeasurableSet.inter
  · by_cases h : IsGreedyFamily (fun i => Φ i) S.graph B Ψ L ∧
        (∀ i, mapBlock (Ψ i).val S.base = P i ∧ mapBlock (Ψ i).val N = Q i) ∧
        IsGraphBounded
          (B ∪ greedyFamilyGraph (S.base.val ∪ N.val) S.graph (fun i => (Ψ i).val))
          (θ + S.graph.card * L) <;> simp [h]
  · simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact (measurableSet_singleton (chosenEmbedding (Ψ i).val)).preimage
      (measurable_pi_apply ((i : ℕ) + 1))

theorem elimination_placements_probability_paper_threshold
    {W : Type*} [Fintype W] [DecidableEq W] {q r n : ℕ}
    (S : ExchangeSystem W q (r + 1)) (N : Block W q) (e : Block W (r + 1))
    (hpair : IsEliminationPair S N e) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (hS : S.graph.card ≤ (4 * q) ^ (2 * q)) (M : ℕ) (hM : 0 < M)
    {A ρ : ℝ} (hA : 1 ≤ A)
    (hAb : ((q.choose (r + 1) * M : ℕ) : ℝ) * A ≤ (4 * q : ℝ) ^ (24 * q))
    (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (hD : IsCliqueFamilyBounded r D (A * (n : ℝ) ^ (-ρ)))
    (hB : IsGraphBounded B (A * (n : ℝ) ^ (-ρ)))
    (hmult : ∀ f : Block (Fin n) (r + 1), (D.filter fun Q => f.val ⊆ Q.val).card ≤ M)
    (t : ℕ) (P Q : Fin t → Block (Fin n) q)
    (hP : ∀ i, P i ∈ D) (hQ : ∀ i, Q i ∈ D)
    (hinj : Function.Injective fun i => (P i, Q i))
    (Φ : ℕ → ↥(S.base.val ∪ N.val) ↪ Fin n)
    (hΦP : ∀ i : Fin t, rootImage (Φ i) S.base subset_union_left = P i)
    (hΦQ : ∀ i : Fin t, rootImage (Φ i) N subset_union_right = Q i) :
    1 - Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) <
      (unstoppedGreedyProbability Φ S.graph B).real
        (eliminationPlacementEvent S N t P Q Φ B (A * (n : ℝ) ^ (-ρ))
          (8 * (r + 1).factorial * (((q.choose (r + 1) * M : ℕ) : ℝ) *
            A * (n : ℝ) ^ (-ρ)))) := by
  have hK : (1 : ℝ) ≤ (q.choose (r + 1) * M : ℕ) := by
    exact_mod_cast Nat.mul_pos (Nat.choose_pos hqr.le) hM
  have hAnonneg : 0 ≤ A := le_trans zero_le_one hA
  have hAK : A ≤ ((q.choose (r + 1) * M : ℕ) : ℝ) * A := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hK hAnonneg
  have hKA : 1 ≤ ((q.choose (r + 1) * M : ℕ) : ℝ) * A := hA.trans hAK
  have hB' : IsGraphBounded B
      (((q.choose (r + 1) * M : ℕ) : ℝ) * A *
        (n : ℝ) ^ (-ρ)) :=
    hB.mono (mul_le_mul_of_nonneg_right hAK (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have hroots : ∀ f ∈ S.graph, ∀ hf : f.val ⊆ S.base.val ∪ N.val,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf)
        (((q.choose (r + 1) * M : ℕ) : ℝ) * A *
          (n : ℝ) ^ (-ρ)) := by
    intro f hf hroot
    have h := hpair.root_inputs hqr.le hD hM hmult P Q hP hQ hinj (fun i => Φ i)
      hΦP hΦQ f hf hroot
    simpa only [mul_assoc] using h
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  have hlo : (n : ℝ) ^ (-(1 / 2 : ℝ)) ≤
      ((q.choose (r + 1) * M : ℕ) : ℝ) * A * (n : ℝ) ^ (-ρ) :=
    (Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hρhalf)).trans
      (le_mul_of_one_le_left (Real.rpow_nonneg (Nat.cast_nonneg n) _) hKA)
  have hhi : ((q.choose (r + 1) * M : ℕ) : ℝ) * A * (n : ℝ) ^ (-ρ) ≤
      (4 * q : ℝ) ^ (24 * q) * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 3)) :=
    mul_le_mul hAb (Real.rpow_le_rpow_of_exponent_le hn1 (neg_le_neg hρ))
      (Real.rpow_nonneg (Nat.cast_nonneg n) _) (by positivity)
  have hb := small_pattern_uniform_greedy_probability_paper_threshold hqr hn hw S.graph hS
    (hpair.admissible hqr.le) hlo hhi t Φ B hB' hroots
  have hL : 4 * (r + 1).factorial *
      (((q.choose (r + 1) * M : ℕ) : ℝ) * A * (n : ℝ) ^ (-ρ)) ≤
      8 * (r + 1).factorial *
        (((q.choose (r + 1) * M : ℕ) : ℝ) * A * (n : ℝ) ^ (-ρ)) := by
    have hp := Real.rpow_nonneg (Nat.cast_nonneg n) (-ρ)
    have hf : (0 : ℝ) ≤ (r + 1).factorial := Nat.cast_nonneg _
    have hk : (0 : ℝ) ≤ (q.choose (r + 1) * M : ℕ) := Nat.cast_nonneg _
    nlinarith only [mul_nonneg hf (mul_nonneg (mul_nonneg hk hAnonneg) hp)]
  have hb' := hb.trans_le (measureReal_mono (greedyFamilyEvent_mono Φ S.graph B t hL))
  exact hb'.trans_le (measureReal_mono
    (greedy_event_subset_eliminationPlacementEvent S N t P Q Φ B hB (by positivity) hΦP hΦQ))

end Arxiv2411_18291
