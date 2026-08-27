import Arxiv.Arxiv2411_18291.ExchangeConfiguration
import Arxiv.Arxiv2411_18291.ExchangeReplacement
import Arxiv.Arxiv2411_18291.CliqueIntersections

/-!
# Near and far cliques of an exchange configuration

A replacement clique is near when it shares an edge with the base.
Every near clique belongs to the negative decomposition and to the
distinguished exchange family. Its intersection with the base is exactly
one edge, including at the level of vertex sets.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

def ExchangeSystem.nearCliques (S : ExchangeSystem V q r) : Finset (Block V q) :=
  S.replacementCliques.filter fun P => (cliqueEdges r P ∩ cliqueEdges r S.base).Nonempty

def ExchangeSystem.farCliques (S : ExchangeSystem V q r) : Finset (Block V q) :=
  S.replacementCliques \ S.nearCliques

theorem ExchangeSystem.near_negative (S : ExchangeSystem V q r) {P : Block V q}
    (hP : P ∈ S.nearCliques) : P ∈ S.negative := by
  obtain ⟨hP, e, he⟩ := mem_filter.mp hP
  rcases mem_union.mp hP with hN | hpos
  · exact hN
  · have hd := S.positive_decomposition.cliques_disjoint (mem_erase.mp hpos).2 S.base_mem
      (mem_erase.mp hpos).1
    exact (disjoint_left.mp hd (mem_inter.mp he).1 (mem_inter.mp he).2).elim

theorem ExchangeSystem.far_disjoint_base (S : ExchangeSystem V q r) {P : Block V q}
    (hP : P ∈ S.farCliques) : Disjoint (cliqueEdges r P) (cliqueEdges r S.base) := by
  obtain ⟨hPR, hnot⟩ := mem_sdiff.mp hP
  apply disjoint_left.mpr
  intro e heP heB
  exact hnot (mem_filter.mpr ⟨hPR, ⟨e, mem_inter.mpr ⟨heP, heB⟩⟩⟩)

theorem IsExchangeFamily.negative_near_inter {S : ExchangeSystem V q r}
    {A : Finset (Block V q)} (hA : IsExchangeFamily S A) {P : Block V q} (hP : P ∈ S.negative)
    {e : Block V r} (heP : e ∈ cliqueEdges r P) (heB : e ∈ cliqueEdges r S.base) :
    P ∈ A ∧ cliqueEdges r P ∩ cliqueEdges r S.base = {e} := by
  obtain ⟨Q, hQ, hinter⟩ := hA.2.2.1 e heB
  have heQ : e ∈ cliqueEdges r Q := by
    have he : e ∈ cliqueEdges r Q ∩ cliqueEdges r S.base := hinter ▸ mem_singleton_self e
    exact (mem_inter.mp he).1
  have hPQ : P = Q := by
    by_contra hne
    exact disjoint_left.mp (S.negative_decomposition.cliques_disjoint hP (hA.1 hQ) hne) heP heQ
  simpa only [hPQ] using And.intro hQ hinter

theorem IsExchangeFamily.near_root {S : ExchangeSystem V q r}
    {A : Finset (Block V q)} (hA : IsExchangeFamily S A) (hr : 0 < r)
    {P : Block V q} (hP : P ∈ S.nearCliques) :
    P ∈ A ∧ ∃ e ∈ cliqueEdges r S.base, P.val ∩ S.base.val = e.val := by
  obtain ⟨e, he⟩ := (mem_filter.mp hP).2
  have h := hA.negative_near_inter (S.near_negative hP) (mem_inter.mp he).1 (mem_inter.mp he).2
  exact ⟨h.1, e, (mem_inter.mp he).2,
    vertices_inter_eq_of_cliqueEdges_singleton hr P S.base e h.2⟩

theorem IsExchangeFamily.near_inter_card {S : ExchangeSystem V q r}
    {A : Finset (Block V q)} (hA : IsExchangeFamily S A) (hr : 0 < r)
    {P : Block V q} (hP : P ∈ S.nearCliques) : (P.val ∩ S.base.val).card = r := by
  obtain ⟨_, e, _, he⟩ := hA.near_root hr hP
  rw [he, e.property]

theorem IsExchangeFamily.replacement_inter_card_le {S : ExchangeSystem V q r}
    {A : Finset (Block V q)} (hA : IsExchangeFamily S A) (hr : 0 < r)
    {P : Block V q} (hP : P ∈ S.replacementCliques) : (P.val ∩ S.base.val).card ≤ r := by
  by_cases hnear : P ∈ S.nearCliques
  · exact (hA.near_inter_card hr hnear).le
  · exact (clique_inter_card_lt_of_disjoint P S.base
      (S.far_disjoint_base (mem_sdiff.mpr ⟨hP, hnear⟩))).le

def IsExchangeFamily.nearRoot {S : ExchangeSystem V q r} {A : Finset (Block V q)}
    (hA : IsExchangeFamily S A) (hr : 0 < r) (P : S.nearCliques) : Block V r :=
  ⟨P.val.val ∩ S.base.val, hA.near_inter_card hr P.property⟩

theorem IsExchangeFamily.nearRoot_inter {S : ExchangeSystem V q r}
    {A : Finset (Block V q)} (hA : IsExchangeFamily S A) (hr : 0 < r) (P : S.nearCliques) :
    cliqueEdges r P.val ∩ cliqueEdges r S.base = {hA.nearRoot hr P} :=
  cliqueEdges_inter_singleton_of_vertices P.val S.base (hA.nearRoot hr P) rfl

theorem IsExchangeFamily.nearRoot_mem {S : ExchangeSystem V q r}
    {A : Finset (Block V q)} (hA : IsExchangeFamily S A) (hr : 0 < r) (P : S.nearCliques) :
    hA.nearRoot hr P ∈ cliqueEdges r S.base :=
  (mem_cliqueEdges _ _).mpr inter_subset_right

theorem IsExchangeFamily.nearRoot_injective {S : ExchangeSystem V q r}
    {A : Finset (Block V q)} (hA : IsExchangeFamily S A) (hr : 0 < r) :
    Function.Injective (hA.nearRoot hr) := by
  intro P Q heq
  apply Subtype.ext
  by_contra hPQ
  have heP : hA.nearRoot hr P ∈ cliqueEdges r P.val :=
    (mem_cliqueEdges _ _).mpr inter_subset_left
  have heQ : hA.nearRoot hr Q ∈ cliqueEdges r Q.val :=
    (mem_cliqueEdges _ _).mpr inter_subset_left
  exact disjoint_left.mp (S.negative_decomposition.cliques_disjoint
    (S.near_negative P.property) (S.near_negative Q.property) hPQ) heP (heq ▸ heQ)

end Arxiv2411_18291
