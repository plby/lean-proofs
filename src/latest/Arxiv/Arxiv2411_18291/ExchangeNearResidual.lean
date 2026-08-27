import Arxiv.Arxiv2411_18291.IntegralExchangeGeneration
import Arxiv.Arxiv2411_18291.ExchangeFrameStructure

/-!
# The base boundary modulo the near-clique boundaries

Removing all near cliques from the negative decomposition leaves only far
cliques. The positive decomposition with its base removed is also far.
Consequently the base minus the sum of its near-clique boundaries is
generated whenever all far-clique boundaries are generated.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [Fintype W] [DecidableEq W] [Fintype V] [DecidableEq V]
variable {q r : ℕ}

omit [Fintype W] [DecidableEq W] in
theorem sum_indicator_cliqueEdges (D : Finset (Block V q)) :
    (∑ Q ∈ D, indicator (cliqueEdges r Q)) = boundary r (indicator D) := by
  funext e
  simp only [Finset.sum_apply, indicator, mem_cliqueEdges, ← sum_filter, sum_const,
    nsmul_eq_mul, mul_one, boundary_indicator]

theorem ExchangeSystem.image_replacement_identity (S : ExchangeSystem W q r) (f : W ↪ V) :
    indicator (cliqueEdges r (mapBlock f S.base)) =
      (∑ P ∈ S.negative, indicator (cliqueEdges r (mapBlock f P))) -
        ∑ P ∈ S.positive.erase S.base, indicator (cliqueEdges r (mapBlock f P)) := by
  have h := (S.map f).boundary_replacement
  rw [ExchangeSystem.replacementVector, boundary_sub, ← sum_indicator_cliqueEdges,
    ← sum_indicator_cliqueEdges] at h
  change (∑ P ∈ mapGraph f S.negative, indicator (cliqueEdges r P)) -
      (∑ P ∈ (mapGraph f S.positive).erase (mapBlock f S.base), indicator (cliqueEdges r P)) =
        indicator (cliqueEdges r (mapBlock f S.base)) at h
  rw [← mapGraph_erase] at h
  simpa only [mapGraph, sum_map, blockEmbedding, Function.Embedding.coeFn_mk] using h.symm

omit [Fintype V] [DecidableEq V] in
theorem ExchangeSystem.positive_erase_subset_far (S : ExchangeSystem W q r) :
    S.positive.erase S.base ⊆ S.farCliques := by
  intro P hP
  refine mem_sdiff.mpr ⟨mem_union_right _ hP, fun hnear => ?_⟩
  exact disjoint_left.mp S.disjoint (mem_erase.mp hP).2 (S.near_negative hnear)

theorem ExchangeSystem.image_base_sub_near_generated (S : ExchangeSystem W q r)
    (f : W ↪ V) (D : Finset (Block V q))
    (hfar : ∀ P ∈ S.farCliques, GeneratedBy D (indicator (cliqueEdges r (mapBlock f P)))) :
    GeneratedBy D (indicator (cliqueEdges r (mapBlock f S.base)) -
      ∑ P : S.nearCliques, indicator (cliqueEdges r (mapBlock f P.val))) := by
  have hn : GeneratedBy D (∑ P ∈ S.negative \ S.nearCliques,
      indicator (cliqueEdges r (mapBlock f P))) :=
    GeneratedBy.sum _ _ (fun P hP => hfar P (mem_sdiff.mpr
      ⟨mem_union_left _ (mem_sdiff.mp hP).1, (mem_sdiff.mp hP).2⟩))
  have hp : GeneratedBy D (∑ P ∈ S.positive.erase S.base,
      indicator (cliqueEdges r (mapBlock f P))) :=
    GeneratedBy.sum _ _ (fun P hP => hfar P (S.positive_erase_subset_far hP))
  have hsub : S.nearCliques ⊆ S.negative := fun _ hP => S.near_negative hP
  have hgen := hn.sub hp
  have hsplit : (∑ P ∈ S.negative \ S.nearCliques, indicator (cliqueEdges r (mapBlock f P))) =
      (∑ P ∈ S.negative, indicator (cliqueEdges r (mapBlock f P))) -
        ∑ P ∈ S.nearCliques, indicator (cliqueEdges r (mapBlock f P)) :=
    eq_sub_iff_add_eq.mpr (sum_sdiff hsub)
  rw [hsplit] at hgen
  rw [S.image_replacement_identity f, Finset.sum_coe_sort S.nearCliques
    (fun P => indicator (cliqueEdges r (mapBlock f P)))]
  convert hgen using 1
  abel

theorem IsExchangeFamily.sum_nearRoot_map {S : ExchangeSystem W q r}
    {A : Finset (Block W q)} (hA : IsExchangeFamily S A) (hr : 0 < r)
    (f : W ↪ V) {M : Type*} [AddCommMonoid M] (g : Block V r → M) :
    (∑ P : S.nearCliques, g (mapBlock f (hA.nearRoot hr P))) =
      ∑ e ∈ cliqueEdges r (mapBlock f S.base), g e := by
  calc
    _ = ∑ e : cliqueEdges r S.base, g (mapBlock f e.val) :=
      (hA.nearRootEquiv hr).sum_comp (fun e => g (mapBlock f e.val))
    _ = ∑ e ∈ cliqueEdges r S.base, g (mapBlock f e) :=
      Finset.sum_coe_sort (cliqueEdges r S.base) (fun e => g (mapBlock f e))
    _ = ∑ e ∈ mapGraph f (cliqueEdges r S.base), g e := by
      simp only [mapGraph, sum_map, blockEmbedding, Function.Embedding.coeFn_mk]
    _ = _ := by rw [map_cliqueEdges]

end Arxiv2411_18291
