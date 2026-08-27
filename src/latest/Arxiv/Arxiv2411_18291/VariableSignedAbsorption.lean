import Arxiv.Arxiv2411_18291.VariableFurtherCancellation

/-! # The fixed variable-capacity host absorbs every matched signed leave -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W U V : Type*} [Fintype W] [Fintype U] [Fintype V]
variable [DecidableEq W] [DecidableEq U] [DecidableEq V] {q r : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {C : Block V q → ℕ} {θ θ' θ'' : ℝ}
variable {T : ExchangeSystem U q (r + 1)} {N₀ : Block U q} {e₀ : Block U (r + 1)}
variable {F : VariableSplittingFamily S D B C θ}
variable {P₀ N₁ : Finset (Block V q)}

theorem VariableNearMatching.two_stage_signed_representation (M : VariableNearMatching F P₀ N₁)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    (hlocal : IsPositiveFrameLocal S A) (hcross : IsCrossSimple (r + 1) S.positive S.negative)
    (E : EliminationFamily T N₀ F.graph F.pairPositive F.pairNegative θ')
    (L : VariableFurtherEliminationPairs F E)
    (G : EliminationFamily T N₀ E.graph L.positive (fun i : E.badNegative => i.val) θ'')
    (hpair : IsEliminationPair T N₀ e₀) (hqr : r + 1 ≤ q)
    (hP₀ : P₀ ⊆ F.positiveCliques) (hN₁ : N₁ ⊆ F.negativeCliques)
    (J : Hypergraph V (r + 1))
    (hJ : boundary (r + 1) (indicator P₀ - indicator N₁) = indicator J) :
    ∃ P N : Finset (Block V q), Disjoint P N ∧ N ⊆ variableFinalNegative F E L G ∧
      boundary (r + 1) (indicator P - indicator N) = indicator J := by
  let P := E.replacePositive M.selected P₀
  let N := E.replaceNegative M.selected N₁
  have hp : P ⊆ F.positiveCliques ∪ E.positiveCliques := M.first_positive_subset E hP₀
  have hn : N ⊆ F.negativeFar ∪ E.negativeCliques := M.first_negative_subset E hN₁
  have hb : boundary (r + 1) (indicator P - indicator N) = indicator J :=
    (M.first_boundary E hpair hqr hP₀ hN₁).trans hJ
  have hnonneg (e : Block V (r + 1)) : 0 ≤ boundary (r + 1) (indicator P - indicator N) e := by
    rw [hb]
    simp only [indicator]
    split_ifs <;> norm_num
  refine ⟨G.replacePositive (L.selected N) P, G.replaceNegative (L.selected N) N,
    L.second_signs_disjoint G hpair hqr P N hp hn
      (M.first_signs_disjoint E hpair hqr hP₀ hN₁),
    L.second_negative_subset G N hn, ?_⟩
  exact (L.second_boundary G hA hlocal hcross hpair hqr P N hp hn hnonneg).trans hb

theorem VariableNearMatching.two_stage_absorbs (M : VariableNearMatching F P₀ N₁)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    (hlocal : IsPositiveFrameLocal S A) (hcross : IsCrossSimple (r + 1) S.positive S.negative)
    (E : EliminationFamily T N₀ F.graph F.pairPositive F.pairNegative θ')
    (L : VariableFurtherEliminationPairs F E)
    (G : EliminationFamily T N₀ E.graph L.positive (fun i : E.badNegative => i.val) θ'')
    (hpair : IsEliminationPair T N₀ e₀) (hqr : r + 1 ≤ q)
    (hP₀ : P₀ ⊆ F.positiveCliques) (hN₁ : N₁ ⊆ F.negativeCliques)
    (J : Hypergraph V (r + 1)) (hJB : J ⊆ B)
    (hJ : boundary (r + 1) (indicator P₀ - indicator N₁) = indicator J) :
    HasDecomposition q (cliqueSupport (r + 1) (variableFinalNegative F E L G) ∪ J) := by
  obtain ⟨P, N, _, hN, hb⟩ :=
    M.two_stage_signed_representation hA hlocal hcross E L G hpair hqr hP₀ hN₁ J hJ
  exact hasDecomposition_of_signed hqr (variableFinalNegative_decomposition F E L G hpair) hN
    (Disjoint.mono_right hJB (variableFinalNegative_avoids_original F E L G hpair)) hb

end Arxiv2411_18291
