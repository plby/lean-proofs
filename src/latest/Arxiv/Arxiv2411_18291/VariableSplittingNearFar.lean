import Arxiv.Arxiv2411_18291.VariableSplittingCopyGeometry
import Arxiv.Arxiv2411_18291.SplittingNearFar

/-! # Near and far variable-capacity splitting cliques

Near cliques meet the original graph in exactly one edge. Far negative
cliques are edge-disjoint from every other negative splitting clique.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r : ℕ} {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {C : Block V q → ℕ} {θ : ℝ}

def VariableSplittingFamily.negativeNear
    (F : VariableSplittingFamily S D B C θ) : Finset (Block V q) :=
  F.negativeCliques.filter fun P => (cliqueEdges (r + 1) P ∩ B).Nonempty

def VariableSplittingFamily.negativeFar
    (F : VariableSplittingFamily S D B C θ) : Finset (Block V q) :=
  F.negativeCliques \ F.negativeNear

def VariableSplittingFamily.positiveNear
    (F : VariableSplittingFamily S D B C θ) : Finset (Block V q) :=
  F.positiveCliques.filter fun P => (cliqueEdges (r + 1) P ∩ B).Nonempty

def VariableSplittingFamily.positiveFar
    (F : VariableSplittingFamily S D B C θ) : Finset (Block V q) :=
  F.positiveCliques \ F.positiveNear

theorem VariableSplittingFamily.negativeNear_source (F : VariableSplittingFamily S D B C θ)
    {P : Block V q} (hP : P ∈ F.negativeNear) :
    ∃ s : VariableCliqueSlots D C, ∃ P₀ ∈ S.nearCliques,
      s.2.1 = false ∧ mapBlock (F.embedding s) P₀ = P := by
  obtain ⟨hP, hnear⟩ := mem_filter.mp hP
  obtain ⟨s, _, hs⟩ := mem_biUnion.mp hP
  rw [S.negativeReplacement_map] at hs
  obtain ⟨P₀, hP₀, heq⟩ := (mem_mapGraph _ _ _).mp hs
  have hn := F.near_of_copy_inter s (S.negativeReplacement_subset _ hP₀) (heq ▸ hnear)
  exact ⟨s, P₀, hn, S.negativeReplacement_near_sign _ hP₀ hn, heq⟩

theorem VariableSplittingFamily.positiveNear_source (F : VariableSplittingFamily S D B C θ)
    {P : Block V q} (hP : P ∈ F.positiveNear) :
    ∃ s : VariableCliqueSlots D C, ∃ P₀ ∈ S.nearCliques,
      s.2.1 = true ∧ mapBlock (F.embedding s) P₀ = P := by
  obtain ⟨hP, hnear⟩ := mem_filter.mp hP
  obtain ⟨s, _, hs⟩ := mem_biUnion.mp hP
  rw [S.positiveReplacement_map] at hs
  obtain ⟨P₀, hP₀, heq⟩ := (mem_mapGraph _ _ _).mp hs
  have hn := F.near_of_copy_inter s (S.positiveReplacement_subset _ hP₀) (heq ▸ hnear)
  exact ⟨s, P₀, hn, S.positiveReplacement_near_sign _ hP₀ hn, heq⟩

theorem VariableSplittingFamily.negativeNear_inter (F : VariableSplittingFamily S D B C θ)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    {P : Block V q} (hP : P ∈ F.negativeNear) :
    ∃ e ∈ B, cliqueEdges (r + 1) P ∩ B = {e} := by
  obtain ⟨s, P₀, hP₀, _, rfl⟩ := F.negativeNear_source hP
  have h := F.near_copy_inter hA s ⟨P₀, hP₀⟩
  refine ⟨_, ?_, h⟩
  exact (mem_inter.mp (h ▸ mem_singleton_self _)).2

theorem VariableSplittingFamily.positiveNear_inter (F : VariableSplittingFamily S D B C θ)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    {P : Block V q} (hP : P ∈ F.positiveNear) :
    ∃ e ∈ B, cliqueEdges (r + 1) P ∩ B = {e} := by
  obtain ⟨s, P₀, hP₀, _, rfl⟩ := F.positiveNear_source hP
  have h := F.near_copy_inter hA s ⟨P₀, hP₀⟩
  refine ⟨_, ?_, h⟩
  exact (mem_inter.mp (h ▸ mem_singleton_self _)).2

theorem VariableSplittingFamily.negativeFar_disjoint_original
    (F : VariableSplittingFamily S D B C θ)
    {P : Block V q} (hP : P ∈ F.negativeFar) : Disjoint (cliqueEdges (r + 1) P) B := by
  obtain ⟨hP, hnot⟩ := mem_sdiff.mp hP
  apply disjoint_left.mpr
  intro e heP heB
  exact hnot (mem_filter.mpr ⟨hP, ⟨e, mem_inter.mpr ⟨heP, heB⟩⟩⟩)

theorem VariableSplittingFamily.positiveFar_disjoint_original
    (F : VariableSplittingFamily S D B C θ)
    {P : Block V q} (hP : P ∈ F.positiveFar) : Disjoint (cliqueEdges (r + 1) P) B := by
  obtain ⟨hP, hnot⟩ := mem_sdiff.mp hP
  apply disjoint_left.mpr
  intro e heP heB
  exact hnot (mem_filter.mpr ⟨hP, ⟨e, mem_inter.mpr ⟨heP, heB⟩⟩⟩)

theorem VariableSplittingFamily.negativeFar_disjoint_negative
    (F : VariableSplittingFamily S D B C θ)
    {P Q : Block V q} (hP : P ∈ F.negativeFar) (hQ : Q ∈ F.negativeCliques)
    (hPQ : P ≠ Q) : Disjoint (cliqueEdges (r + 1) P) (cliqueEdges (r + 1) Q) := by
  obtain ⟨s, _, hs⟩ := mem_biUnion.mp (mem_sdiff.mp hP).1
  obtain ⟨t, _, ht⟩ := mem_biUnion.mp hQ
  by_cases hst : s = t
  · subst t
    exact (S.map (F.embedding s)).negativeReplacement_cliques_disjoint _ hs ht hPQ
  · apply disjoint_left.mpr
    intro e heP heQ
    have heB := F.copy_inter_subset hst (mem_inter.mpr
      ⟨(S.map (F.embedding s)).replacement_clique_subset
          ((S.map (F.embedding s)).negativeReplacement_subset _ hs) heP,
        (S.map (F.embedding t)).replacement_clique_subset
          ((S.map (F.embedding t)).negativeReplacement_subset _ ht) heQ⟩)
    exact disjoint_left.mp (F.negativeFar_disjoint_original hP) heP heB

end Arxiv2411_18291
