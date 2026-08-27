import Arxiv.Arxiv2411_18291.DecoderFamilyProbability
import Arxiv.Arxiv2411_18291.FiniteObservedOutput

/-! # Finite output laws of the actual local-decoder process -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r : ℕ}

structure LocalDecoderOutput (B : Hypergraph V (r + 1))
    (hW : Fintype.card W = q + (r + 1)) (θ : ℝ) where
  embedding : B → W ↪ V
  cover : IsCliqueCover (complete V (r + 1) \ B) (fun e : B => e.val)
    (fun e => embeddingClique hW (embedding e))
  decoder : IsLocalDecoderFamily B (decoderFamilyOfPlacements hW embedding)
  bounded : IsGraphBounded (cliqueSupport (r + 1) (decoderFamilyOfPlacements hW embedding))
    ((1 + 4 * (r + 1).factorial * (q + (r + 1)).choose (r + 1)) * θ)

omit [DecidableEq W] in
theorem LocalDecoderOutput.embedding_injective (B : Hypergraph V (r + 1))
    (hW : Fintype.card W = q + (r + 1)) (θ : ℝ) :
    Function.Injective (fun O : LocalDecoderOutput B hW θ => O.embedding) := by
  intro E F h
  cases E
  cases F
  cases h
  rfl

omit [DecidableEq W] in
instance LocalDecoderOutput.finite (B : Hypergraph V (r + 1))
    (hW : Fintype.card W = q + (r + 1)) (θ : ℝ) : Finite (LocalDecoderOutput B hW θ) :=
  Finite.of_injective (fun O => O.embedding) (LocalDecoderOutput.embedding_injective B hW θ)

def decoderReadEquiv (B : Hypergraph V (r + 1)) : B ≃ B :=
  (Fintype.equivFin B).trans ((finCongr (Fintype.card_coe B)).trans B.equivFin.symm)

omit [Fintype V] [DecidableEq V] in
theorem decoderReadEquiv_time (B : Hypergraph V (r + 1)) (i : B) :
    (B.equivFin (decoderReadEquiv B i) : ℕ) = (Fintype.equivFin B i : ℕ) := by
  simp [decoderReadEquiv]

def decoderOutputObservation {B : Hypergraph V (r + 1)}
    {hW : Fintype.card W = q + (r + 1)} {θ : ℝ}
    (O : LocalDecoderOutput B hW θ) (i : B) : EmbeddingState W V :=
  chosenEmbedding (O.embedding (decoderReadEquiv B i))

omit [DecidableEq W] in
theorem localDecoderOutputEvent_eq_observed (B : Hypergraph V (r + 1))
    (hW : Fintype.card W = q + (r + 1)) (θ : ℝ) :
    localDecoderOutputEvent B hW θ =
      FiniteHistoryProcess.observedOutputEvent
        (decoderOutputObservation (B := B) (hW := hW) (θ := θ)) := by
  ext ω
  constructor
  · rintro ⟨f, ⟨hcover, hdec, hb⟩, hmatch⟩
    refine ⟨⟨f, hcover, hdec, hb⟩, ?_⟩
    intro i
    dsimp only [decoderOutputObservation]
    rw [← decoderReadEquiv_time B i]
    exact hmatch (decoderReadEquiv B i)
  · rintro ⟨O, hmatch⟩
    refine ⟨O.embedding, ⟨O.cover, O.decoder, O.bounded⟩, ?_⟩
    intro e
    have ht : (Fintype.equivFin B ((decoderReadEquiv B).symm e) : ℕ) =
        (B.equivFin e : ℕ) := by
      simpa only [Equiv.apply_symm_apply] using
        (decoderReadEquiv_time B ((decoderReadEquiv B).symm e)).symm
    simpa only [decoderOutputObservation, ht, Equiv.apply_symm_apply] using
      hmatch ((decoderReadEquiv B).symm e)

def localDecoderOutputLaw (F₀ : Block W (r + 1))
    (B : Hypergraph V (r + 1)) (e₀ : Block V (r + 1))
    (hW : Fintype.card W = q + (r + 1)) (θ : ℝ) :
    PMF (Option (LocalDecoderOutput B hW θ)) :=
  FiniteHistoryProcess.observedOutputLaw
    (unstoppedGreedyProbability (fun i => edgeRootMap F₀ (decoderRootSequence B e₀ i))
      (complete W (r + 1)) B) decoderOutputObservation

theorem localDecoderOutputLaw_failure_real (F₀ : Block W (r + 1))
    (B : Hypergraph V (r + 1)) (e₀ : Block V (r + 1))
    (hW : Fintype.card W = q + (r + 1)) (θ : ℝ) :
    (localDecoderOutputLaw F₀ B e₀ hW θ none).toReal = 1 -
      (unstoppedGreedyProbability (fun i => edgeRootMap F₀ (decoderRootSequence B e₀ i))
        (complete W (r + 1)) B).real (localDecoderOutputEvent B hW θ) := by
  rw [localDecoderOutputEvent_eq_observed]
  exact FiniteHistoryProcess.observedOutputLaw_failure_real _ _

theorem localDecoderOutputLaw_failure_lt {n : ℕ}
    (F₀ : Block W (r + 1)) (hW : Fintype.card W = q + (r + 1))
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {A ρ : ℝ} (hA : 1 ≤ A) (hAb : A ≤ (4 * q : ℝ) ^ (24 * q))
    (hρ : paperAlpha q (r + 1) / 3 ≤ ρ) (hρhalf : ρ ≤ 1 / 2)
    (B : Hypergraph (Fin n) (r + 1)) (e₀ : Block (Fin n) (r + 1))
    (hB : IsGraphBounded B (A * (n : ℝ) ^ (-ρ))) :
    (localDecoderOutputLaw F₀ B e₀ hW (A * (n : ℝ) ^ (-ρ)) none).toReal <
      Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) := by
  rw [localDecoderOutputLaw_failure_real]
  have hp := local_decoder_output_probability_scaled F₀ hW hqr hn hA hAb hρ hρhalf B e₀ hB
  linarith only [hp]

end Arxiv2411_18291
