import Arxiv.Arxiv2411_18291.NearMatching
import Arxiv.Arxiv2411_18291.SelectedElimination
import Arxiv.Arxiv2411_18291.FirstElimination

/-!
# The first signed cancellation stage

Use the matching selected by the signed representation. The replacement
preserves its boundary and disjoint signs. All negative near splitting
cliques disappear; the negative far splitting cliques are retained.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W U V : Type*} [Fintype W] [Fintype U] [Fintype V]
variable [DecidableEq W] [DecidableEq U] [DecidableEq V] {q r C : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {θ θ' : ℝ}
variable {T : ExchangeSystem U q (r + 1)} {N₀ : Block U q} {e₀ : Block U (r + 1)}
variable {F : SplittingFamily S D B C θ} {P N : Finset (Block V q)}

theorem NearMatching.remaining_negative (M : NearMatching F P N) (hN : N ⊆ F.negativeCliques) :
    N \ M.selected.image F.pairNegative = N ∩ F.negativeFar := by
  rw [M.selected_negative]
  ext Q
  simp only [mem_sdiff, mem_inter, SplittingFamily.negativeFar]
  constructor
  · intro h
    exact ⟨h.1, hN h.1, fun hn => h.2 ⟨h.1, hn⟩⟩
  · intro h
    exact ⟨h.1, fun hn => h.2.2 hn.2⟩

theorem NearMatching.remaining_positiveFar (M : NearMatching F P N) :
    P ∩ F.positiveFar ⊆ P \ M.selected.image F.pairPositive := by
  intro Q hQ
  obtain ⟨hP, hfar⟩ := mem_inter.mp hQ
  refine mem_sdiff.mpr ⟨hP, ?_⟩
  intro h
  exact (mem_sdiff.mp hfar).2 (mem_inter.mp (M.selected_positive_subset h)).2

theorem SplittingFamily.signed_subfamilies_support (F : SplittingFamily S D B C θ)
    (hP : P ⊆ F.positiveCliques) (hN : N ⊆ F.negativeCliques) :
    cliqueSupport (r + 1) (P ∪ N) ⊆ F.graph := by
  intro e he
  obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.mp he
  apply F.cliques_support
  refine mem_biUnion.mpr ⟨Q, ?_, heQ⟩
  rw [F.cliques_eq_signs]
  exact union_subset_union hP hN hQ

variable (E : EliminationFamily T N₀ F.graph F.pairPositive F.pairNegative θ')

theorem NearMatching.first_boundary (M : NearMatching F P N)
    (hpair : IsEliminationPair T N₀ e₀) (hqr : r + 1 ≤ q)
    (hP : P ⊆ F.positiveCliques) (hN : N ⊆ F.negativeCliques) :
    boundary (r + 1) (indicator (E.replacePositive M.selected P) -
      indicator (E.replaceNegative M.selected N)) =
      boundary (r + 1) (indicator P - indicator N) := by
  apply E.replace_boundary hpair hqr M.selected M.positive_injective M.negative_injective
    P N (F.signed_subfamilies_support hP hN)
    (M.selected_positive_subset.trans inter_subset_left)
  rw [M.selected_negative]
  exact inter_subset_left

theorem NearMatching.first_signs_disjoint (M : NearMatching F P N)
    (hpair : IsEliminationPair T N₀ e₀) (hqr : r + 1 ≤ q)
    (hP : P ⊆ F.positiveCliques) (hN : N ⊆ F.negativeCliques) :
    Disjoint (E.replacePositive M.selected P) (E.replaceNegative M.selected N) :=
  E.replace_signs_disjoint hpair hqr M.selected P N (F.signed_subfamilies_support hP hN)
    (Disjoint.mono hP hN (F.signs_disjoint hqr))

theorem NearMatching.first_positive_subset (M : NearMatching F P N)
    (hP : P ⊆ F.positiveCliques) :
    E.replacePositive M.selected P ⊆ F.positiveCliques ∪ E.positiveCliques :=
  union_subset_union (sdiff_subset.trans hP) (E.selectedPositive_subset M.selected)

theorem NearMatching.first_negative_eq (M : NearMatching F P N)
    (hN : N ⊆ F.negativeCliques) :
    E.replaceNegative M.selected N = (N ∩ F.negativeFar) ∪ E.selectedNegative M.selected := by
  rw [EliminationFamily.replaceNegative, M.remaining_negative hN]

theorem NearMatching.first_negative_subset (M : NearMatching F P N)
    (hN : N ⊆ F.negativeCliques) :
    E.replaceNegative M.selected N ⊆ F.negativeFar ∪ E.negativeCliques := by
  rw [M.first_negative_eq E hN]
  exact union_subset_union inter_subset_right (E.selectedNegative_subset M.selected)

theorem split_and_first_cancel (F : SplittingFamily S D B C θ)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    (E : EliminationFamily T N₀ F.graph F.pairPositive F.pairNegative θ')
    (hpair : IsEliminationPair T N₀ e₀) (hqr : r + 1 ≤ q)
    (Φ : Block V q → ℤ) (hΦ : ∀ Q, |Φ Q| ≤ C) (hs : ∀ Q, Q ∉ D → Φ Q = 0)
    (L : Hypergraph V (r + 1)) (hL : boundary (r + 1) Φ = indicator L) :
    ∃ P N : Finset (Block V q), ∃ M : NearMatching F P N,
      P ⊆ F.positiveCliques ∧ N ⊆ F.negativeCliques ∧
      Disjoint (E.replacePositive M.selected P) (E.replaceNegative M.selected N) ∧
      boundary (r + 1) (indicator (E.replacePositive M.selected P) -
        indicator (E.replaceNegative M.selected N)) = indicator L ∧
      E.replaceNegative M.selected N ⊆ F.negativeFar ∪ E.negativeCliques := by
  obtain ⟨P, N, hP, hN, _, hb⟩ := F.signed_representation_with_signs hqr Φ hΦ hs
  obtain ⟨M⟩ := F.exists_nearMatching hA P N hP hN (by
    intro e _
    rw [hb, hL]
    simp only [indicator]
    split_ifs <;> norm_num)
  exact ⟨P, N, M, hP, hN, M.first_signs_disjoint E hpair hqr hP hN,
    (M.first_boundary E hpair hqr hP hN).trans (hb.trans hL), M.first_negative_subset E hN⟩

end Arxiv2411_18291
