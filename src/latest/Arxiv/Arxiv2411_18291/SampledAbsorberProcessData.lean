import Arxiv.Arxiv2411_18291.NormalizedDecoderOutput
import Arxiv.Arxiv2411_18291.NormalizedSplittingOutput
import Arxiv.Arxiv2411_18291.CancellationOutputLaws
import Arxiv.Arxiv2411_18291.NormalizedElimination
import Arxiv.Arxiv2411_18291.AbsorberJointFailure
import Arxiv.Arxiv2411_18291.AbsorberFromGenerators

/-! # The output specification of the sampled absorber process -/

open Finset

noncomputable section

namespace Arxiv2411_18291

def SampledAbsorberProcessSuccess
    {X W U : Type*} [Fintype X] [Fintype W] [Fintype U]
    [DecidableEq X] [DecidableEq W] [DecidableEq U] {q r n : ℕ}
    (F₀ : Block X (r + 1)) (hX : Fintype.card X = q + (r + 1))
    (S : ExchangeSystem W q (r + 1)) (T : ExchangeSystem U q (r + 1)) (N : Block U q)
    (B : Hypergraph (Fin n) (r + 1)) (D₁ : Finset (Block (Fin n) q))
    (d₀ : Block (Fin n) (r + 1)) (Q₀ : Block (Fin n) q) : Prop :=
    let C := absorberCoefficientCap q (r + 1)
    let M := absorberGeneratorMultiplicity q (r + 1)
    let A := 2 * splittingFactor S C (absorberNormalizationFactor q (r + 1))
    let x := (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))
    let Decoder := LocalDecoderOutput B hX (2 * x)
    let D := fun O : Decoder => D₁ ∪ decoderFamilyOfPlacements hX O.embedding
    let B' := fun O : Decoder =>
      B ∪ cliqueSupport (r + 1) (decoderFamilyOfPlacements hX O.embedding)
    let Split := fun O : Decoder => SplittingFamily S (D O) (B' O) C (A * x)
    let First := fun (O : Decoder) (F : Split O) =>
      EliminationFamily T N F.graph F.pairPositive F.pairNegative
        (firstEliminationFactor T C M A * x)
    ∃ Φ₁ : ∀ O : Decoder, Split O → ℕ → ↥(T.base.val ∪ N.val) ↪ Fin n,
    ∃ L : ∀ (O : Decoder) (F : Split O) (E : First O F), FurtherEliminationPairs F E,
    ∃ Φ₂ : ∀ (O : Decoder) (F : Split O), First O F →
      ℕ → ↥(T.base.val ∪ N.val) ↪ Fin n,
    let p₁ := localDecoderOutputLaw F₀ B d₀ hX (2 * x)
    let p₂ := fun O : Decoder => splittingFamilyOutputLaw S (D O) (B' O) C Q₀ (A * x)
    let p₃ := fun (O : Decoder) (F : Split O) =>
      eliminationFamilyOutputLaw T N F.graph F.pairPositive F.pairNegative (Φ₁ O F)
        (firstEliminationFactor T C M A * x)
    let p₄ := fun (O : Decoder) (F : Split O) (E : First O F) =>
      eliminationFamilyOutputLaw T N E.graph (L O F E).positive
        (fun i : E.badNegative => i.val) (Φ₂ O F E) (secondEliminationFactor T C M A * x)
    (FiniteHistoryProcess.fourStageOutput p₁ p₂ p₃ p₄ none).toReal <
        Real.exp (-((n : ℝ) ^ (1 / 10 : ℝ))) ∧
      ∀ (O : Decoder) (F : Split O) (E : First O F)
        (G : EliminationFamily T N E.graph (L O F E).positive
          (fun i : E.badNegative => i.val) (secondEliminationFactor T C M A * x)),
        let H := cliqueSupport (r + 1) (finalNegative F E (L O F E) G)
        HasDecomposition q H ∧ Disjoint H B ∧
          IsGraphBounded H ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 4))) ∧
          AbsorbsGeneratedLeaves D₁ B H

end Arxiv2411_18291
