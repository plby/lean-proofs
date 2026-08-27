import Arxiv.Arxiv2411_18291.RainbowReplacementWitnesses
import Arxiv.Arxiv2411_18291.RainbowPuncturedPairGeneration
import Arxiv.Arxiv2411_18291.ExchangeNearResidual

/-!
# The rainbow relation for an arbitrary clique

Fix one punctured rainbow reference clique through each edge. An arbitrary
clique boundary differs from the sum of its uncoloured-edge references by
an integer combination of rainbow cliques. The near cliques account for
the reference terms exactly once each; the far cliques are already rainbow.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {I W V : Type*} [Fintype I] [Fintype W] [DecidableEq W]
variable [Fintype V] [DecidableEq V] {q r t : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)} {N : Block W q}
variable {σ : I → Equiv.Perm V} {G : Hypergraph V (r + 1)}

theorem rainbow_clique_residual_generated (hA : IsExchangeFamily S A)
    (hE : RainbowAvoidingExtensionProperties S N σ G t) (ht : q.choose (r + 1) ≤ t)
    (R : Block V (r + 1) → Block V q) (hRroot : ∀ e, e.val ⊆ (R e).val)
    (hRcol : ∀ e, IsRainbow (fun i => mapGraph (σ i).toEmbedding G)
      ((cliqueEdges (r + 1) (R e)).erase e))
    (hpair : ∀ P Q : Block V q, ∀ e : Block V (r + 1),
      e.val ⊆ P.val → e.val ⊆ Q.val →
      IsRainbow (fun i => mapGraph (σ i).toEmbedding G) ((cliqueEdges (r + 1) P).erase e) →
      IsRainbow (fun i => mapGraph (σ i).toEmbedding G) ((cliqueEdges (r + 1) Q).erase e) →
      GeneratedBy (rainbowCliqueFamily (fun i => mapGraph (σ i).toEmbedding G) q)
        (indicator (cliqueEdges (r + 1) P) - indicator (cliqueEdges (r + 1) Q)))
    (Q : Block V q) :
    GeneratedBy (rainbowCliqueFamily (fun i => mapGraph (σ i).toEmbedding G) q)
      (indicator (cliqueEdges (r + 1) Q) - ∑ e ∈ cliqueEdges (r + 1) Q,
        if e ∈ permutedUnion σ G then 0 else indicator (cliqueEdges (r + 1) (R e))) := by
  let D := rainbowCliqueFamily (fun i => mapGraph (σ i).toEmbedding G) q
  let w : Block V (r + 1) → Block V (r + 1) → ℤ := fun e =>
    if e ∈ permutedUnion σ G then 0 else indicator (cliqueEdges (r + 1) (R e))
  change GeneratedBy D (indicator (cliqueEdges (r + 1) Q) - ∑ e ∈ cliqueEdges (r + 1) Q, w e)
  obtain ⟨f, hf, hnear, hgood, hfar⟩ := hE.clique_replacement_colours hA ht Q
  have hfarGen : ∀ P ∈ S.farCliques,
      GeneratedBy D (indicator (cliqueEdges (r + 1) (mapBlock f P))) := by
    intro P hP
    exact generatedBy_clique ((mem_rainbowCliqueFamily _ _).mpr (hfar P hP))
  have hbase := S.image_base_sub_near_generated f D hfarGen
  have hnearGen (P : S.nearCliques) : GeneratedBy D
      (indicator (cliqueEdges (r + 1) (mapBlock f P.val)) -
        w (mapBlock f (hA.nearRoot (Nat.succ_pos r) P))) := by
    let e := mapBlock f (hA.nearRoot (Nat.succ_pos r) P)
    change GeneratedBy D (indicator (cliqueEdges (r + 1) (mapBlock f P.val)) -
      if e ∈ permutedUnion σ G then 0 else indicator (cliqueEdges (r + 1) (R e)))
    by_cases he : e ∈ permutedUnion σ G
    · rw [if_pos he, sub_zero]
      exact generatedBy_clique ((mem_rainbowCliqueFamily _ _).mpr (hgood P he))
    · rw [if_neg he]
      have heP : e.val ⊆ (mapBlock f P.val).val := by
        change (P.val.val ∩ S.base.val).map f ⊆ P.val.val.map f
        exact map_subset_map.mpr inter_subset_left
      exact hpair (mapBlock f P.val) (R e) e heP (hRroot e) (hnear P) (hRcol e)
  have hsum := GeneratedBy.sum univ
    (fun P : S.nearCliques => indicator (cliqueEdges (r + 1) (mapBlock f P.val)) -
      w (mapBlock f (hA.nearRoot (Nat.succ_pos r) P))) (fun P _ => hnearGen P)
  rw [sum_sub_distrib] at hsum
  have hrootSum : (∑ P : S.nearCliques, w (mapBlock f (hA.nearRoot (Nat.succ_pos r) P))) =
      ∑ e ∈ cliqueEdges (r + 1) Q, w e := by
    simpa only [hf] using hA.sum_nearRoot_map (Nat.succ_pos r) f w
  have hresult := hbase.add hsum
  rw [hf, hrootSum] at hresult
  convert hresult using 1
  abel

end Arxiv2411_18291
