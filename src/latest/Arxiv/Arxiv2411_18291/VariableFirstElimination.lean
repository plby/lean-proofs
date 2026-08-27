import Arxiv.Arxiv2411_18291.VariableNearCancellationPairs
import Arxiv.Arxiv2411_18291.EliminationNegativeGeometry

/-! # Geometry of the first elimination after variable splitting -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W U V : Type*} [Fintype W] [Fintype U] [Fintype V]
variable [DecidableEq W] [DecidableEq U] [DecidableEq V] {q r : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {C : Block V q → ℕ} {θ θ' : ℝ}
variable {T : ExchangeSystem U q (r + 1)} {N : Block U q} {e₀ : Block U (r + 1)}

theorem variable_first_elimination_negative_avoids_original (F : VariableSplittingFamily S D B C θ)
    {A₀ : Finset (Block W q)} (hA₀ : IsExchangeFamily S A₀)
    (E : EliminationFamily T N F.graph F.pairPositive F.pairNegative θ')
    (hpair : IsEliminationPair T N e₀) {R : Block V q} (hR : R ∈ E.negativeCliques) :
    Disjoint (cliqueEdges (r + 1) R) B :=
  E.negative_disjoint_previous hpair subset_union_left (F.near_pair_old_inter hA₀) hR

theorem variable_first_good_negative_disjoint_splitting (F : VariableSplittingFamily S D B C θ)
    (E : EliminationFamily T N F.graph F.pairPositive F.pairNegative θ')
    {R Q : Block V q} (hR : R ∈ E.goodNegative) (hQ : Q ∈ F.cliques) :
    Disjoint (cliqueEdges (r + 1) R) (cliqueEdges (r + 1) Q) := by
  apply Disjoint.mono_right _ (mem_filter.mp hR).2
  intro e he
  exact F.cliques_support (mem_biUnion.mpr ⟨Q, hQ, he⟩)

theorem variable_first_bad_negative_partner (F : VariableSplittingFamily S D B C θ)
    {A₀ : Finset (Block W q)} (hA₀ : IsExchangeFamily S A₀)
    (E : EliminationFamily T N F.graph F.pairPositive F.pairNegative θ')
    (hpair : IsEliminationPair T N e₀) {R : Block V q} (hR : R ∈ E.badNegative) :
    ∃ e : Block V (r + 1), ∃ Q ∈ F.positiveFar,
      cliqueEdges (r + 1) R ∩ F.graph = {e} ∧ e ∈ cliqueEdges (r + 1) Q ∧
      R.val ∩ Q.val = e.val ∧
      ∀ Q' ∈ F.positiveCliques, e ∈ cliqueEdges (r + 1) Q' → Q' = Q := by
  obtain ⟨e, heG, hRe⟩ := E.badNegative_inter_singleton hpair hR
  have heR : e ∈ cliqueEdges (r + 1) R :=
    (mem_inter.mp (hRe ▸ mem_singleton_self e)).1
  have heB : e ∉ B := fun h =>
    disjoint_left.mp (variable_first_elimination_negative_avoids_original F hA₀ E hpair
      (mem_sdiff.mp hR).1) heR h
  obtain ⟨i, _, hi⟩ := mem_biUnion.mp (mem_sdiff.mp hR).1
  obtain ⟨R₀, hR₀, hmap⟩ := (mem_mapGraph _ _ _).mp hi
  have heN : e ∈ cliqueEdges (r + 1) (F.pairNegative i) := by
    have heI := mem_inter.mpr ⟨heR, heG⟩
    rw [← hmap, E.negative_copy_inter_original hpair i hR₀] at heI
    exact (mem_inter.mp heI).2
  obtain ⟨Q, hQ, heQ, huniq⟩ := F.negativeNear_positiveFar_partner i.val.1.property heN heB
  have hQall : Q ∈ F.cliques := by
    rw [F.cliques_eq_signs]
    exact mem_union_left _ (mem_sdiff.mp hQ).1
  have hQG : cliqueEdges (r + 1) Q ⊆ F.graph := by
    intro f hf
    exact F.cliques_support (mem_biUnion.mpr ⟨Q, hQall, hf⟩)
  exact ⟨e, Q, hQ, hRe, heQ,
    vertices_inter_eq_of_graph_inter_singleton (Nat.succ_pos r) R Q F.graph e hRe hQG heQ,
    huniq⟩

theorem variable_first_negative_support_avoids_original
    (F : VariableSplittingFamily S D B C θ) {A : Finset (Block W q)}
    (hA : IsExchangeFamily S A)
    (E : EliminationFamily T N F.graph F.pairPositive F.pairNegative θ')
    (hpair : IsEliminationPair T N e₀) :
    Disjoint (cliqueSupport (r + 1) (F.negativeFar ∪ E.negativeCliques)) B := by
  apply disjoint_left.mpr
  intro e he heB
  obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.mp he
  rcases mem_union.mp hQ with hF | hE
  · exact disjoint_left.mp (F.negativeFar_disjoint_original hF) heQ heB
  · exact disjoint_left.mp (variable_first_elimination_negative_avoids_original
      F hA E hpair hE) heQ heB

end Arxiv2411_18291
