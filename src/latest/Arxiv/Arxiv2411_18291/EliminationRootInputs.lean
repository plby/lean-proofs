import Arxiv.Arxiv2411_18291.EliminationPattern
import Arxiv.Arxiv2411_18291.CliquePairBounds

/-!
# Bounded inputs for simultaneous elimination placements

An induced root edge of the elimination pattern lies in one of its two
designated cliques. The same side works for every prescribed embedding.
The bounded repetition of distinct overlapping pairs therefore supplies
the input edge-family bounds required by the random greedy theorem.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W V : Type*} [DecidableEq W] {q r : ℕ} {F : Finset W}

theorem rootImage_subset_rootImage (φ : F ↪ V) (e : Block W r) (Q : Block W q)
    (he : e.val ⊆ F) (hQ : Q.val ⊆ F) (heQ : e.val ⊆ Q.val) :
    (rootImage φ e he).val ⊆ (rootImage φ Q hQ).val := by
  apply map_subset_map.mpr
  intro x hx
  have hxe : x.val ∈ e.val := by simpa only [rootBlock, mem_subtype] using hx
  simpa only [rootBlock, mem_subtype] using heQ hxe

variable [Fintype W]
variable {S : ExchangeSystem W q (r + 1)} {N : Block W q} {e : Block W (r + 1)}

theorem IsEliminationPair.root_edge_cases (h : IsEliminationPair S N e)
    {f : Block W (r + 1)} (hf : f ∈ S.graph) (hroot : f.val ⊆ S.base.val ∪ N.val) :
    f.val ⊆ S.base.val ∨ f.val ⊆ N.val := by
  have hlocal := h.locality f hf
  rwa [inter_eq_left.mpr hroot] at hlocal

variable [Fintype V] [DecidableEq V] {I : Type*} [Fintype I]

theorem IsEliminationPair.root_inputs (h : IsEliminationPair S N e) (hqr : r + 1 ≤ q)
    {D : Finset (Block V q)} {θ : ℝ} (hD : IsCliqueFamilyBounded r D θ) {M : ℕ} (hM : 0 < M)
    (hmult : ∀ f : Block V (r + 1), (D.filter fun Q => f.val ⊆ Q.val).card ≤ M)
    (P Q : I → Block V q) (hP : ∀ i, P i ∈ D) (hQ : ∀ i, Q i ∈ D)
    (hinj : Function.Injective fun i => (P i, Q i)) (φ : I → ↥(S.base.val ∪ N.val) ↪ V)
    (hφP : ∀ i, rootImage (φ i) S.base subset_union_left = P i)
    (hφQ : ∀ i, rootImage (φ i) N subset_union_right = Q i)
    (f : Block W (r + 1)) (hf : f ∈ S.graph) (hroot : f.val ⊆ S.base.val ∪ N.val) :
    IsEdgeFamilyBounded (fun i => rootImage (φ i) f hroot)
      (((q.choose (r + 1) * M : ℕ) : ℝ) * θ) := by
  have heP : e.val ⊆ S.base.val := by rw [← h.vertex_inter]; exact inter_subset_left
  have heQ : e.val ⊆ N.val := by rw [← h.vertex_inter]; exact inter_subset_right
  have heRoot : e.val ⊆ S.base.val ∪ N.val := heP.trans subset_union_left
  have hcommon (i : I) : r + 1 ≤ ((P i).val ∩ (Q i).val).card := by
    have hp := rootImage_subset_rootImage (φ i) e S.base heRoot subset_union_left heP
    have hq := rootImage_subset_rootImage (φ i) e N heRoot subset_union_right heQ
    rw [hφP i] at hp
    rw [hφQ i] at hq
    simpa only [(rootImage (φ i) e heRoot).property] using card_le_card (subset_inter hp hq)
  apply hD.paired_edgeFamily hqr hM hmult P Q hP hQ hinj hcommon
  rcases h.root_edge_cases hf hroot with hp | hq
  · left
    intro i
    rw [← hφP i]
    exact rootImage_subset_rootImage (φ i) f S.base hroot subset_union_left hp
  · right
    intro i
    rw [← hφQ i]
    exact rootImage_subset_rootImage (φ i) f N hroot subset_union_right hq

end Arxiv2411_18291
