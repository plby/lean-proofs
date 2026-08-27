import Arxiv.Arxiv2411_18291.HalfAlphaSplitting
import Arxiv.Arxiv2411_18291.NormalizedElimination
import Arxiv.Arxiv2411_18291.SmallCarrierExchange

/-! # Finite hosts absorbing every normalized bounded representation -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_sparse_signed_absorber_half_alpha
    {W U : Type*} [Fintype W] [Fintype U] [DecidableEq W] [DecidableEq U] {q r n : ℕ}
    (S : ExchangeSystem W q (r + 1)) {A₀ : Finset (Block W q)}
    (hA₀ : IsExchangeFamily S A₀) (hlocal : IsPositiveFrameLocal S A₀)
    (hcross : IsCrossSimple (r + 1) S.positive S.negative)
    (T : ExchangeSystem U q (r + 1)) (N : Block U q) (e₀ : Block U (r + 1))
    (hpair : IsEliminationPair T N e₀) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hwS : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (hwT : Fintype.card U ≤ (4 * q) ^ (2 * q))
    (hS : S.graph.card ≤ absorberExchangeEdges q (r + 1))
    (hT : T.graph.card ≤ absorberExchangeEdges q (r + 1))
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (hD : IsCliqueFamilyBounded r D (2 * absorberNormalizationFactor q (r + 1) *
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))))
    (hB : IsGraphBounded B (2 * absorberNormalizationFactor q (r + 1) *
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))))
    (hDB : cliqueSupport (r + 1) D ⊆ B)
    (hmult : ∀ e : Block (Fin n) (r + 1),
      (D.filter fun P => e.val ⊆ P.val).card ≤ absorberGeneratorMultiplicity q (r + 1)) :
    ∃ H : Hypergraph (Fin n) (r + 1), HasDecomposition q H ∧ Disjoint H B ∧
      IsGraphBounded H ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 4))) ∧
      AbsorbsBoundedRepresentations D B H (absorberCoefficientCap q (r + 1)) := by
  obtain ⟨F⟩ := exists_normalized_splitting_family_half_alpha S hqr hn hwS hS
    D B hD hB hDB hmult
  obtain ⟨E, L, G, hdecomp, hdis, hbound⟩ :=
    exists_normalized_two_stage_elimination_paper_threshold S hA₀ T N e₀ hpair hqr hn hwT
      hS hT D B hmult F
  exact ⟨cliqueSupport (r + 1) (finalNegative F E L G), ⟨_, hdecomp⟩, hdis, hbound,
    two_stage_absorbs_bounded_representations F hA₀ hlocal hcross E L G hpair hqr.le⟩

/-- The finite signed absorber constructs both exchange patterns and every
placement. Only the normalized input family and its support are supplied. -/
theorem exists_normalized_signed_absorber_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (hD : IsCliqueFamilyBounded r D (2 * absorberNormalizationFactor q (r + 1) *
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))))
    (hB : IsGraphBounded B (2 * absorberNormalizationFactor q (r + 1) *
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))))
    (hDB : cliqueSupport (r + 1) D ⊆ B)
    (hmult : ∀ e : Block (Fin n) (r + 1),
      (D.filter fun P => e.val ⊆ P.val).card ≤ absorberGeneratorMultiplicity q (r + 1)) :
    ∃ H : Hypergraph (Fin n) (r + 1), HasDecomposition q H ∧ Disjoint H B ∧
      IsGraphBounded H ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 4))) ∧
      AbsorbsBoundedRepresentations D B H (absorberCoefficientCap q (r + 1)) := by
  obtain ⟨S, A₀, hS, hA₀, hcross, hlocal, hwS⟩ :=
    exists_small_carrier_clique_exchange q (r + 1) (Nat.succ_pos r) hqr
  obtain ⟨T, N, e₀, hpair, hT, hwT⟩ := exists_small_carrier_elimination_pattern q r hqr
  exact exists_sparse_signed_absorber_half_alpha S.system hA₀ hlocal hcross T.system N e₀
    hpair hqr hn hwS hwT hS hT D B hD hB hDB hmult

end Arxiv2411_18291
