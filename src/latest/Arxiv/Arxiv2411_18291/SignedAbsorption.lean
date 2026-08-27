import Arxiv.Arxiv2411_18291.FurtherCancellation

/-!
# Universal absorption of the bounded signed representations

Both cancellation stages can be chosen for each representation after the
host has been fixed. The final negative cliques belong to its fixed true
decomposition. Adding back the unused host cliques therefore gives a true
decomposition of the host together with the represented leave.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

/-- One fixed host absorbs every leave with a bounded representation on `D`. -/
def AbsorbsBoundedRepresentations (D : Finset (Block V q)) (B H : Hypergraph V r)
    (C : ℕ) : Prop :=
  ∀ J : Hypergraph V r, J ⊆ B → ∀ Φ : Block V q → ℤ,
    (∀ Q, |Φ Q| ≤ C) → (∀ Q, Q ∉ D → Φ Q = 0) →
    boundary r Φ = indicator J → HasDecomposition q (H ∪ J)

variable {W U : Type*} [Fintype W] [Fintype U] [DecidableEq W] [DecidableEq U] {C : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {θ θ' θ'' : ℝ}
variable {T : ExchangeSystem U q (r + 1)} {N₀ : Block U q} {e₀ : Block U (r + 1)}

theorem two_stage_signed_representation (F : SplittingFamily S D B C θ)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    (hlocal : IsPositiveFrameLocal S A) (hcross : IsCrossSimple (r + 1) S.positive S.negative)
    (E : EliminationFamily T N₀ F.graph F.pairPositive F.pairNegative θ')
    (L : FurtherEliminationPairs F E)
    (G : EliminationFamily T N₀ E.graph L.positive (fun i : E.badNegative => i.val) θ'')
    (hpair : IsEliminationPair T N₀ e₀) (hqr : r + 1 ≤ q)
    (Φ : Block V q → ℤ) (hΦ : ∀ Q, |Φ Q| ≤ C) (hs : ∀ Q, Q ∉ D → Φ Q = 0)
    (J : Hypergraph V (r + 1)) (hJ : boundary (r + 1) Φ = indicator J) :
    ∃ P N : Finset (Block V q), Disjoint P N ∧ N ⊆ finalNegative F E L G ∧
      boundary (r + 1) (indicator P - indicator N) = indicator J := by
  obtain ⟨P₀, N₁, M, hP₀, hN₁, hdis, hb, hn⟩ :=
    split_and_first_cancel F hA E hpair hqr Φ hΦ hs J hJ
  let P := E.replacePositive M.selected P₀
  let N := E.replaceNegative M.selected N₁
  have hp : P ⊆ F.positiveCliques ∪ E.positiveCliques := M.first_positive_subset E hP₀
  have hnonneg (e : Block V (r + 1)) : 0 ≤ boundary (r + 1) (indicator P - indicator N) e := by
    change 0 ≤ boundary (r + 1) (indicator (E.replacePositive M.selected P₀) -
      indicator (E.replaceNegative M.selected N₁)) e
    rw [hb]
    simp only [indicator]
    split_ifs <;> norm_num
  refine ⟨G.replacePositive (L.selected N) P, G.replaceNegative (L.selected N) N,
    L.second_signs_disjoint G hpair hqr P N hp hn hdis,
    L.second_negative_subset G N hn, ?_⟩
  exact (L.second_boundary G hA hlocal hcross hpair hqr P N hp hn hnonneg).trans hb

theorem two_stage_absorbs_bounded_representations (F : SplittingFamily S D B C θ)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    (hlocal : IsPositiveFrameLocal S A) (hcross : IsCrossSimple (r + 1) S.positive S.negative)
    (E : EliminationFamily T N₀ F.graph F.pairPositive F.pairNegative θ')
    (L : FurtherEliminationPairs F E)
    (G : EliminationFamily T N₀ E.graph L.positive (fun i : E.badNegative => i.val) θ'')
    (hpair : IsEliminationPair T N₀ e₀) (hqr : r + 1 ≤ q) :
    AbsorbsBoundedRepresentations D B (cliqueSupport (r + 1) (finalNegative F E L G)) C := by
  intro J hJB Φ hΦ hs hJ
  obtain ⟨P, N, _, hN, hb⟩ :=
    two_stage_signed_representation F hA hlocal hcross E L G hpair hqr Φ hΦ hs J hJ
  exact hasDecomposition_of_signed hqr (finalNegative_decomposition F E L G hpair) hN
    (Disjoint.mono_right hJB (finalNegative_avoids_original F E L G hpair)) hb

end Arxiv2411_18291
