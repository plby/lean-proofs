import Arxiv.Arxiv2411_18291.SplittingCopyGeometry

/-!
# Near and far splitting cliques

The classification can be read off from the placed cliques themselves:
near means meeting the original graph, and far means avoiding it.
Near cliques retain the sign of their root slot. Negative far cliques
are edge-disjoint from all other negative splitting cliques.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [Fintype V] [DecidableEq W] [DecidableEq V]
variable {q r C : ℕ}

theorem ExchangeSystem.positiveReplacement_map (S : ExchangeSystem W q r) (f : W ↪ V)
    (b : Bool) : (S.map f).positiveReplacement b = mapGraph f (S.positiveReplacement b) := by
  cases b <;> simp [positiveReplacement, ExchangeSystem.map, mapGraph_erase]

theorem ExchangeSystem.negativeReplacement_map (S : ExchangeSystem W q r) (f : W ↪ V)
    (b : Bool) : (S.map f).negativeReplacement b = mapGraph f (S.negativeReplacement b) := by
  cases b <;> simp [negativeReplacement, ExchangeSystem.map, mapGraph_erase]

theorem ExchangeSystem.negativeReplacement_cliques_disjoint (S : ExchangeSystem W q r)
    (b : Bool) {P Q : Block W q} (hP : P ∈ S.negativeReplacement b)
    (hQ : Q ∈ S.negativeReplacement b) (hPQ : P ≠ Q) :
    Disjoint (cliqueEdges r P) (cliqueEdges r Q) := by
  cases b
  · exact S.negative_decomposition.cliques_disjoint hP hQ hPQ
  · exact S.positive_decomposition.cliques_disjoint
      (mem_erase.mp hP).2 (mem_erase.mp hQ).2 hPQ

theorem ExchangeSystem.negativeReplacement_near_sign (S : ExchangeSystem W q r)
    (b : Bool) {P : Block W q} (hP : P ∈ S.negativeReplacement b)
    (hnear : P ∈ S.nearCliques) : b = false := by
  cases b
  · rfl
  · exact (disjoint_left.mp S.disjoint (mem_erase.mp hP).2 (S.near_negative hnear)).elim

theorem ExchangeSystem.positiveReplacement_near_sign (S : ExchangeSystem W q r)
    (b : Bool) {P : Block W q} (hP : P ∈ S.positiveReplacement b)
    (hnear : P ∈ S.nearCliques) : b = true := by
  cases b
  · exact (disjoint_left.mp S.disjoint (mem_erase.mp hP).2 (S.near_negative hnear)).elim
  · rfl

variable {S : ExchangeSystem W q (r + 1)} {D : Finset (Block V q)}
variable {B : Hypergraph V (r + 1)} {θ : ℝ}

def SplittingFamily.negativeNear (F : SplittingFamily S D B C θ) : Finset (Block V q) :=
  F.negativeCliques.filter fun P => (cliqueEdges (r + 1) P ∩ B).Nonempty

def SplittingFamily.negativeFar (F : SplittingFamily S D B C θ) : Finset (Block V q) :=
  F.negativeCliques \ F.negativeNear

def SplittingFamily.positiveNear (F : SplittingFamily S D B C θ) : Finset (Block V q) :=
  F.positiveCliques.filter fun P => (cliqueEdges (r + 1) P ∩ B).Nonempty

def SplittingFamily.positiveFar (F : SplittingFamily S D B C θ) : Finset (Block V q) :=
  F.positiveCliques \ F.positiveNear

theorem SplittingFamily.negativeNear_source (F : SplittingFamily S D B C θ)
    {P : Block V q} (hP : P ∈ F.negativeNear) :
    ∃ s : SignedCliqueSlots D C, ∃ P₀ ∈ S.nearCliques,
      s.2.1 = false ∧ mapBlock (F.embedding s) P₀ = P := by
  obtain ⟨hP, hnear⟩ := mem_filter.mp hP
  obtain ⟨s, _, hs⟩ := mem_biUnion.mp hP
  rw [S.negativeReplacement_map] at hs
  obtain ⟨P₀, hP₀, heq⟩ := (mem_mapGraph _ _ _).mp hs
  have hn := F.near_of_copy_inter s (S.negativeReplacement_subset _ hP₀) (heq ▸ hnear)
  exact ⟨s, P₀, hn, S.negativeReplacement_near_sign _ hP₀ hn, heq⟩

theorem SplittingFamily.positiveNear_source (F : SplittingFamily S D B C θ)
    {P : Block V q} (hP : P ∈ F.positiveNear) :
    ∃ s : SignedCliqueSlots D C, ∃ P₀ ∈ S.nearCliques,
      s.2.1 = true ∧ mapBlock (F.embedding s) P₀ = P := by
  obtain ⟨hP, hnear⟩ := mem_filter.mp hP
  obtain ⟨s, _, hs⟩ := mem_biUnion.mp hP
  rw [S.positiveReplacement_map] at hs
  obtain ⟨P₀, hP₀, heq⟩ := (mem_mapGraph _ _ _).mp hs
  have hn := F.near_of_copy_inter s (S.positiveReplacement_subset _ hP₀) (heq ▸ hnear)
  exact ⟨s, P₀, hn, S.positiveReplacement_near_sign _ hP₀ hn, heq⟩

theorem SplittingFamily.negativeNear_inter (F : SplittingFamily S D B C θ)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    {P : Block V q} (hP : P ∈ F.negativeNear) :
    ∃ e ∈ B, cliqueEdges (r + 1) P ∩ B = {e} := by
  obtain ⟨s, P₀, hP₀, _, rfl⟩ := F.negativeNear_source hP
  have h := F.near_copy_inter hA s ⟨P₀, hP₀⟩
  refine ⟨_, ?_, h⟩
  exact (mem_inter.mp (h ▸ mem_singleton_self _)).2

theorem SplittingFamily.positiveNear_inter (F : SplittingFamily S D B C θ)
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A)
    {P : Block V q} (hP : P ∈ F.positiveNear) :
    ∃ e ∈ B, cliqueEdges (r + 1) P ∩ B = {e} := by
  obtain ⟨s, P₀, hP₀, _, rfl⟩ := F.positiveNear_source hP
  have h := F.near_copy_inter hA s ⟨P₀, hP₀⟩
  refine ⟨_, ?_, h⟩
  exact (mem_inter.mp (h ▸ mem_singleton_self _)).2

theorem SplittingFamily.negativeFar_disjoint_original (F : SplittingFamily S D B C θ)
    {P : Block V q} (hP : P ∈ F.negativeFar) : Disjoint (cliqueEdges (r + 1) P) B := by
  obtain ⟨hP, hnot⟩ := mem_sdiff.mp hP
  apply disjoint_left.mpr
  intro e heP heB
  exact hnot (mem_filter.mpr ⟨hP, ⟨e, mem_inter.mpr ⟨heP, heB⟩⟩⟩)

theorem SplittingFamily.positiveFar_disjoint_original (F : SplittingFamily S D B C θ)
    {P : Block V q} (hP : P ∈ F.positiveFar) : Disjoint (cliqueEdges (r + 1) P) B := by
  obtain ⟨hP, hnot⟩ := mem_sdiff.mp hP
  apply disjoint_left.mpr
  intro e heP heB
  exact hnot (mem_filter.mpr ⟨hP, ⟨e, mem_inter.mpr ⟨heP, heB⟩⟩⟩)

theorem SplittingFamily.negativeFar_disjoint_negative (F : SplittingFamily S D B C θ)
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
