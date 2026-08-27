import Arxiv.Arxiv2411_18291.DecoderPlacementProbability
import Arxiv.Arxiv2411_18291.SparseLocalDecoders

/-! # High-probability output of the local-decoder stage -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r : ℕ}

def decoderRootSequence (B : Hypergraph V (r + 1)) (e₀ : Block V (r + 1)) :
    ℕ → Block V (r + 1) :=
  fun i => if hi : i < B.card then (B.equivFin.symm ⟨i, hi⟩).val else e₀

omit [Fintype V] [DecidableEq V] in
@[simp] theorem decoderRootSequence_eq (B : Hypergraph V (r + 1))
    (e₀ : Block V (r + 1)) (i : Fin B.card) :
    decoderRootSequence B e₀ i = (B.equivFin.symm i).val := by
  unfold decoderRootSequence
  rw [dif_pos i.isLt]

def decoderFamilyOfPlacements {B : Hypergraph V (r + 1)}
    (hW : Fintype.card W = q + (r + 1)) (f : B → W ↪ V) : Finset (Block V q) :=
  cliqueRefinement q (univ.image (fun e => embeddingClique hW (f e)))

def localDecoderOutputEvent (B : Hypergraph V (r + 1))
    (hW : Fintype.card W = q + (r + 1)) (θ : ℝ) : Set (ℕ → EmbeddingState W V) :=
  {ω | ∃ f : B → W ↪ V,
    (IsCliqueCover (complete V (r + 1) \ B) (fun e : B => e.val)
        (fun e => embeddingClique hW (f e)) ∧
      IsLocalDecoderFamily B (decoderFamilyOfPlacements hW f) ∧
      IsGraphBounded (cliqueSupport (r + 1) (decoderFamilyOfPlacements hW f))
        ((1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)) * θ)) ∧
      ∀ e : B, ω ((B.equivFin e : ℕ) + 1) = chosenEmbedding (f e)}

omit [DecidableEq W] in
theorem cliquePlacementEvent_subset_localDecoderOutputEvent
    (hqr : r + 1 ≤ q) (F₀ : Block W (r + 1))
    (hW : Fintype.card W = q + (r + 1)) (B : Hypergraph V (r + 1))
    (e₀ : Block V (r + 1)) (θ : ℝ) :
    cliquePlacementEvent F₀ hW B.card (decoderRootSequence B e₀) B θ ⊆
      localDecoderOutputEvent B hW θ := by
  classical
  rintro ω ⟨Ψ, hmatch, hcover, hbound⟩
  let enum : Fin B.card ≃ B := B.equivFin.symm
  let f : B → W ↪ V := fun e => (Ψ (enum.symm e)).val
  let Z : B → Block V (q + (r + 1)) := fun e => embeddingClique hW (f e)
  have hZ : IsCliqueCover (complete V (r + 1) \ B) (fun e : B => e.val) Z := by
    constructor
    · intro e
      have heq : decoderRootSequence B e₀ (enum.symm e) = e.val := by
        simp only [decoderRootSequence_eq, enum, Equiv.symm_symm, Equiv.symm_apply_apply]
      simpa only [heq] using hcover.punctured (enum.symm e)
    · intro e d hed
      exact hcover.disjoint (fun h => hed (enum.symm.injective h))
  have hb : IsGraphBounded (cliqueCoverGraph (r := r) Z)
      ((1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)) * θ) := by
    dsimp only [Z, f]
    rw [cliqueCoverGraph_reindex enum.symm
      (fun i : Fin B.card => embeddingClique hW (Ψ i).val)]
    exact hbound
  refine ⟨f, ⟨hZ, hZ.localDecoderFamily hqr,
    hb.subgraph hZ.decomposition.refinement_support_subset⟩, ?_⟩
  intro e
  exact hmatch (enum.symm e)

omit [DecidableEq W] in
theorem measurableSet_localDecoderOutputEvent (B : Hypergraph V (r + 1))
    (hW : Fintype.card W = q + (r + 1)) (θ : ℝ) :
    MeasurableSet (localDecoderOutputEvent B hW θ) := by
  classical
  unfold localDecoderOutputEvent
  simp only [Set.ofPred_exists]
  apply MeasurableSet.iUnion
  intro f
  rw [Set.ofPred_and]
  apply MeasurableSet.inter
  · by_cases h : IsCliqueCover (complete V (r + 1) \ B) (fun e : B => e.val)
          (fun e => embeddingClique hW (f e)) ∧
        IsLocalDecoderFamily B (decoderFamilyOfPlacements hW f) ∧
        IsGraphBounded (cliqueSupport (r + 1) (decoderFamilyOfPlacements hW f))
          ((1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)) * θ) <;> simp [h]
  · simp only [Set.ofPred_forall]
    apply MeasurableSet.iInter
    intro e
    exact (measurableSet_singleton (chosenEmbedding (f e))).preimage
      (measurable_pi_apply ((B.equivFin e : ℕ) + 1))

theorem local_decoder_output_probability_scaled {n : ℕ}
    (F₀ : Block W (r + 1)) (hW : Fintype.card W = q + (r + 1))
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {A ρ : ℝ} (hA : 1 ≤ A) (hAb : A ≤ (4 * q : ℝ) ^ (24 * q))
    (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (B : Hypergraph (Fin n) (r + 1)) (e₀ : Block (Fin n) (r + 1))
    (hB : IsGraphBounded B (A * (n : ℝ) ^ (-ρ))) :
    1 - Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) <
      (unstoppedGreedyProbability (fun i => edgeRootMap F₀ (decoderRootSequence B e₀ i))
        (complete W (r + 1)) B).real (localDecoderOutputEvent B hW (A * (n : ℝ) ^ (-ρ))) := by
  let E := decoderRootSequence B e₀
  have hEmem (i : Fin B.card) : E i ∈ B := by
    rw [show E i = (B.equivFin.symm i).val from decoderRootSequence_eq B e₀ i]
    exact (B.equivFin.symm i).property
  have hEinj : Function.Injective (fun i : Fin B.card => E i) := by
    intro i j hij
    apply B.equivFin.symm.injective
    apply Subtype.ext
    simpa only [E, decoderRootSequence_eq] using hij
  have hb := indexed_clique_placement_probability_scaled F₀ hW hqr (by omega) hn
    hA hAb hρ hρhalf B.card E B hB hEinj (fun i hi => hEmem ⟨i, hi⟩)
    (hB.edgeFamily (fun i : Fin B.card => E i) hEmem hEinj)
  exact hb.trans_le (measureReal_mono
    (cliquePlacementEvent_subset_localDecoderOutputEvent hqr.le F₀ hW B e₀ _))

theorem local_decoder_output_probability_at_exponent {n : ℕ}
    (F₀ : Block W (r + 1)) (hW : Fintype.card W = q + (r + 1))
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {ρ : ℝ} (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (B : Hypergraph (Fin n) (r + 1)) (e₀ : Block (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-ρ))) :
    1 - Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) <
      (unstoppedGreedyProbability (fun i => edgeRootMap F₀ (decoderRootSequence B e₀ i))
        (complete W (r + 1)) B).real (localDecoderOutputEvent B hW ((n : ℝ) ^ (-ρ))) := by
  simpa only [one_mul] using local_decoder_output_probability_scaled F₀ hW hqr hn
    (A := 1) le_rfl (one_le_pow₀ (by exact_mod_cast (show 1 ≤ 4 * q by omega)))
    hρ hρhalf B e₀ (by simpa only [one_mul] using hB)

end Arxiv2411_18291
