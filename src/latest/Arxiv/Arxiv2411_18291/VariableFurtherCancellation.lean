import Arxiv.Arxiv2411_18291.VariableFurtherPartnerSelection
import Arxiv.Arxiv2411_18291.VariableFirstCancellation
import Arxiv.Arxiv2411_18291.VariableFinalNegativeFamily

/-!
# Removing the selected bad negative cliques

The second stage uses the forced, distinct far partners. Its selected
replacements preserve the boundary and leave all negative coefficients
inside the fixed family that decomposes the absorber host.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W U V : Type*} [Fintype W] [Fintype U] [Fintype V]
variable [DecidableEq W] [DecidableEq U] [DecidableEq V] {q r : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {C : Block V q → ℕ} {θ θ' θ'' : ℝ}
variable {T : ExchangeSystem U q (r + 1)} {N₀ : Block U q} {e₀ : Block U (r + 1)}
variable {F : VariableSplittingFamily S D B C θ}
variable {E : EliminationFamily T N₀ F.graph F.pairPositive F.pairNegative θ'}

theorem variable_first_signed_support (hpair : IsEliminationPair T N₀ e₀)
    (P N : Finset (Block V q)) (hP : P ⊆ F.positiveCliques ∪ E.positiveCliques)
    (hN : N ⊆ F.negativeFar ∪ E.negativeCliques) :
    cliqueSupport (r + 1) (P ∪ N) ⊆ E.graph := by
  have hsub : P ∪ N ⊆ F.cliques ∪ E.cliques := by
    intro Q hQ
    rw [F.cliques_eq_signs, E.cliques_eq_signs]
    rcases mem_union.mp hQ with hp | hn
    · rcases mem_union.mp (hP hp) with hf | he
      · exact mem_union_left _ (mem_union_left _ hf)
      · exact mem_union_right _ (mem_union_left _ he)
    · rcases mem_union.mp (hN hn) with hf | he
      · exact mem_union_left _ (mem_union_right _ (mem_sdiff.mp hf).1)
      · exact mem_union_right _ (mem_union_right _ he)
  exact (biUnion_subset_biUnion_of_subset_left _ hsub).trans
    (E.union_cliques_support hpair F.cliques F.cliques_support)

variable (L : VariableFurtherEliminationPairs F E)
variable (G : EliminationFamily T N₀ E.graph L.positive (fun i : E.badNegative => i.val) θ'')

theorem VariableFurtherEliminationPairs.second_boundary
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    (hlocal : IsPositiveFrameLocal S A) (hcross : IsCrossSimple (r + 1) S.positive S.negative)
    (hpair : IsEliminationPair T N₀ e₀) (hqr : r + 1 ≤ q)
    (P N : Finset (Block V q)) (hP : P ⊆ F.positiveCliques ∪ E.positiveCliques)
    (hN : N ⊆ F.negativeFar ∪ E.negativeCliques)
    (hnonneg : ∀ e, 0 ≤ boundary (r + 1) (indicator P - indicator N) e) :
    boundary (r + 1) (indicator (G.replacePositive (L.selected N) P) -
      indicator (G.replaceNegative (L.selected N) N)) =
      boundary (r + 1) (indicator P - indicator N) := by
  apply G.replace_boundary hpair hqr (L.selected N)
    (L.selected_positive_injective hA hlocal hcross hpair P N hP hnonneg)
    Subtype.coe_injective.injOn P N (variable_first_signed_support hpair P N hP hN)
    (L.selected_positive_subset hpair P N hP hnonneg)
  rw [L.selected_negative]
  exact inter_subset_left

theorem VariableFurtherEliminationPairs.second_signs_disjoint (hpair : IsEliminationPair T N₀ e₀)
    (hqr : r + 1 ≤ q) (P N : Finset (Block V q))
    (hP : P ⊆ F.positiveCliques ∪ E.positiveCliques)
    (hN : N ⊆ F.negativeFar ∪ E.negativeCliques) (hdis : Disjoint P N) :
    Disjoint (G.replacePositive (L.selected N) P) (G.replaceNegative (L.selected N) N) :=
  G.replace_signs_disjoint hpair hqr (L.selected N) P N
    (variable_first_signed_support hpair P N hP hN) hdis

theorem VariableFurtherEliminationPairs.second_negative_subset (N : Finset (Block V q))
    (hN : N ⊆ F.negativeFar ∪ E.negativeCliques) :
    G.replaceNegative (L.selected N) N ⊆ variableFinalNegative F E L G := by
  intro Q hQ
  rcases mem_union.mp hQ with hold | hnew
  · obtain ⟨hQN, hnot⟩ := mem_sdiff.mp hold
    have hbad : Q ∉ E.badNegative := by
      intro hQbad
      apply hnot
      rw [L.selected_negative]
      exact mem_inter.mpr ⟨hQN, hQbad⟩
    apply mem_union_left
    rcases mem_union.mp (hN hQN) with hf | he
    · exact mem_union_left _ hf
    · apply mem_union_right
      by_contra hgood
      exact hbad (mem_sdiff.mpr ⟨he, hgood⟩)
  · exact mem_union_right _ (G.selectedNegative_subset (L.selected N) hnew)

end Arxiv2411_18291
