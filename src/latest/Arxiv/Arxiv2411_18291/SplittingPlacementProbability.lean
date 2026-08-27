import Arxiv.Arxiv2411_18291.SeparatedGreedyProbability
import Arxiv.Arxiv2411_18291.FlexibleSplittingPlacements

/-! # High-probability splitting placements on the actual repeated roots -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r : ℕ}

def splittingPlacementEvent (S : ExchangeSystem W q (r + 1))
    (t : ℕ) (Q : ℕ → Block V q) (B : Hypergraph V (r + 1)) (θ L : ℝ) :
    Set (ℕ → EmbeddingState W V) :=
  {ω | ∃ Ψ : (i : Fin t) → EmbeddingExtension (edgeRootMap S.base (Q i)),
    (IsGreedyFamily (fun i => edgeRootMap S.base (Q i)) S.graph B Ψ L ∧
      (∀ i j : Fin t, i ≠ j → r + 1 ≤ ((Q i).val ∩ (Q j).val).card →
        Disjoint ((univ \ S.base.val).map (Ψ i).val)
          ((univ \ S.base.val).map (Ψ j).val)) ∧
      IsGraphBounded (B ∪ greedyFamilyGraph S.base.val S.graph (fun i => (Ψ i).val))
        (θ + S.graph.card * L)) ∧
      ∀ i : Fin t, ω (i + 1) = chosenEmbedding (Ψ i).val}

theorem separated_event_subset_splittingPlacementEvent (S : ExchangeSystem W q (r + 1))
    (t : ℕ) (Q : ℕ → Block V q) (B : Hypergraph V (r + 1)) {θ L : ℝ}
    (hB : IsGraphBounded B θ) (hL : 0 ≤ L) :
    separatedGreedyFamilyEvent (fun i => edgeRootMap S.base (Q i))
        (fun i j => r + 1 ≤ ((Q i).val ∩ (Q j).val).card) S.graph B L t ⊆
      splittingPlacementEvent S t Q B θ L := by
  rintro ω ⟨Ψ, hΨ, hsep, hmatch⟩
  refine ⟨Ψ, ⟨hΨ, ?_, hΨ.graphBounded hB hL⟩, hmatch⟩
  intro i j hij hshare
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · exact hsep i j hlt hshare
  · exact (hsep j i hgt (by simpa only [inter_comm] using hshare)).symm

theorem measurableSet_splittingPlacementEvent (S : ExchangeSystem W q (r + 1))
    (t : ℕ) (Q : ℕ → Block V q) (B : Hypergraph V (r + 1)) (θ L : ℝ) :
    MeasurableSet (splittingPlacementEvent S t Q B θ L) := by
  classical
  unfold splittingPlacementEvent
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro Ψ
  rw [Set.ofPred_and]
  apply MeasurableSet.inter
  · by_cases h : IsGreedyFamily (fun i => edgeRootMap S.base (Q i)) S.graph B Ψ L ∧
        (∀ i j : Fin t, i ≠ j → r + 1 ≤ ((Q i).val ∩ (Q j).val).card →
          Disjoint ((univ \ S.base.val).map (Ψ i).val)
            ((univ \ S.base.val).map (Ψ j).val)) ∧
        IsGraphBounded (B ∪ greedyFamilyGraph S.base.val S.graph (fun i => (Ψ i).val))
          (θ + S.graph.card * L) <;> simp [h]
  · simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    exact (measurableSet_singleton (chosenEmbedding (Ψ i).val)).preimage
      (measurable_pi_apply ((i : ℕ) + 1))

theorem splitting_placements_probability_at_exponent
    {W : Type*} [Fintype W] [DecidableEq W] {q r n : ℕ}
    (S : ExchangeSystem W q (r + 1)) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (hS : S.graph.card ≤ (4 * q) ^ (2 * q)) (C M : ℕ) (hC : 0 < C)
    (hconflict : q.choose (r + 1) * (C * M) ≤ (4 * q) ^ (8 * q))
    {A ρ : ℝ} (hA : 1 ≤ A) (hAb : (C : ℝ) * A ≤ (4 * q : ℝ) ^ (24 * q))
    (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (hD : IsCliqueFamilyBounded r D (A * (n : ℝ) ^ (-ρ)))
    (hB : IsGraphBounded B (A * (n : ℝ) ^ (-ρ)))
    (hmult : ∀ e : Block (Fin n) (r + 1), (D.filter fun P => e.val ⊆ P.val).card ≤ M)
    (t : ℕ) (Q : ℕ → Block (Fin n) q) (hQ : ∀ i < t, Q i ∈ D)
    (hrep : ∀ P, (univ.filter fun i : Fin t => Q i = P).card ≤ C) :
    1 - Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) <
      (unstoppedPrescribedGreedyProbability (fun i => edgeRootMap S.base (Q i))
        (separatedCandidates (fun i => edgeRootMap S.base (Q i))
          (fun i j => r + 1 ≤ ((Q i).val ∩ (Q j).val).card)) S.graph B).real
        (splittingPlacementEvent S t Q B (A * (n : ℝ) ^ (-ρ))
          (8 * (r + 1).factorial * (C * A * (n : ℝ) ^ (-ρ)))) := by
  have hC1 : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have hAnonneg : 0 ≤ A := le_trans zero_le_one hA
  have hACA : A ≤ (C : ℝ) * A := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hC1 hAnonneg
  have hCA : 1 ≤ (C : ℝ) * A := hA.trans hACA
  have hadm := admissible_clique_root S.graph S.base hqr.le
    (S.positive_decomposition.clique_subset S.base_mem)
  let Φ : ℕ → S.base.val ↪ Fin n := fun i => edgeRootMap S.base (Q i)
  let Rel : ℕ → ℕ → Prop := fun i j => r + 1 ≤ ((Q i).val ∩ (Q j).val).card
  have hB' : IsGraphBounded B (C * A * (n : ℝ) ^ (-ρ)) :=
    hB.mono (mul_le_mul_of_nonneg_right hACA (Real.rpow_nonneg (Nat.cast_nonneg n) _))
  have hroots : ∀ f ∈ S.graph, ∀ hf : f.val ⊆ S.base.val,
      IsEdgeFamilyBounded (fun i : Fin t => rootImage (Φ i) f hf)
        (C * A * (n : ℝ) ^ (-ρ)) := by
    intro f _ hf
    have hsub (i : Fin t) : (rootImage (Φ i) f hf).val ⊆ (Q i).val := by
      calc
        _ ⊆ usedVertices (Φ i) := rootImage_subset_usedVertices (Φ i) f hf
        _ = _ := edgeRootMap_usedVertices S.base (Q i)
    have hh := hD.repeated_edgeFamily hqr.le (fun i : Fin t => Q i)
      (fun i => hQ i i.isLt) hC hrep (fun i : Fin t => rootImage (Φ i) f hf) hsub
    simpa only [mul_assoc] using hh
  have hb := small_pattern_separated_probability_paper_threshold
    hqr hn hw S.graph hS hadm hconflict hCA hAb hρ hρhalf t Φ Rel B hB'
    (prior_clique_overlap_card_le (r + 1) D Q t hQ hrep hmult) hroots
  have hCnonneg : (0 : ℝ) ≤ C := Nat.cast_nonneg C
  exact hb.trans_le (measureReal_mono
    (separated_event_subset_splittingPlacementEvent S t Q B hB (by positivity)))

end Arxiv2411_18291
