import Arxiv.Arxiv2411_18291.NearFrameCandidates
import Arxiv.Arxiv2411_18291.RainbowExtensions
import Arxiv.Arxiv2411_18291.ColouredGenerators

/-!
# Near-clique candidates for every rainbow base

The initial colours are fixed. For a rainbow base their edge colours supply
the prescribed near-clique colours. Other bases use all extensions as a
dummy candidate family, so a single uniform colour experiment can treat
every root map without imposing conditions on the initial colours.
-/

open Finset Filter
open scoped Topology

noncomputable section

namespace Arxiv2411_18291

variable {J W V : Type*} [Fintype W] [DecidableEq W] {q r : ℕ}
variable {S : ExchangeSystem W q r} {A : Finset (Block W q)}

theorem IsExchangeFamily.nearRootImage_mem_base [Fintype V] [DecidableEq V]
    (hA : IsExchangeFamily S A) (hr : 0 < r)
    (φ : S.base.val ↪ V) (i : Fin (q.choose r)) :
    hA.nearRootImage hr φ i ∈ cliqueEdges r (rootImage φ S.base Subset.rfl) := by
  apply (mem_cliqueEdges _ _).mpr
  rw [rootImage_self]
  exact hA.nearRootImage_subset hr φ i

theorem eventually_rainbow_near_candidates [Fintype J] (hA : IsExchangeFamily S A)
    (hr : 0 < r) (hqr : r < q) {b α τ : ℝ} (hb : 0 < b) (hα : 0 ≤ α) (hτ : 0 < τ)
    (hgap : α * ((q.choose r - 1 : ℕ) : ℝ) < 1) :
    ∀ᶠ n : ℕ in atTop, ∀ K G : Hypergraph (Fin n) r, ∀ D : Finset (Block (Fin n) q),
      b * (n : ℝ) ^ (-α) ≤ density K →
      (∀ e ∈ G, |((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        cliqueMainTerm n (density K) q r r| ≤
          (n : ℝ) ^ (-τ) * cliqueMainTerm n (density K) q r r) →
      ∀ σ : J → Equiv.Perm (Fin n), ∀ φ : S.base.val ↪ Fin n,
      ∃ T : Finset (EmbeddingExtension φ),
        (min (nearFrameDensityConstant b q r) (3 / 4) *
          (n : ℝ) ^ (-(α * ((q.choose r - 1 : ℕ) : ℝ) * q.choose r))) *
            (n : ℝ) ^ (Fintype.card W - q) ≤ T.card ∧
        (IsRainbow (fun j => mapGraph (σ j).toEmbedding G)
          (cliqueEdges r (rootImage φ S.base Subset.rfl)) →
          ∀ f ∈ T, ∀ P ∈ S.nearCliques, mapBlock f.val P ∈ permutedUnion σ D) := by
  classical
  filter_upwards [eventually_near_frame_candidates (J := J) hA hr hqr hb hτ hgap,
    eventually_ge_atTop (4 * (Fintype.card W) ^ 2), eventually_ge_atTop 1]
      with n hnear hn hn1
  intro K G D hd hcount σ φ
  by_cases hR : IsRainbow (fun j => mapGraph (σ j).toEmbedding G)
      (cliqueEdges r (rootImage φ S.base Subset.rfl))
  · obtain ⟨colour, hcolour⟩ := hR
    let c (i : Fin (q.choose r)) : J :=
      colour ⟨hA.nearRootImage hr φ i, hA.nearRootImage_mem_base hr φ i⟩
    obtain ⟨T, hT, hnearT⟩ := hnear K G D hd hcount σ φ c (fun i => hcolour _)
    refine ⟨T, ?_, fun _ f hf P hP => ?_⟩
    · exact (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (min_le_left _ _) (by positivity)) (by positivity)).trans hT
    · let i := (hA.nearEnumeration hr).symm ⟨P, hP⟩
      have hi : hA.nearPattern hr i = P :=
        congrArg Subtype.val ((hA.nearEnumeration hr).apply_symm_apply ⟨P, hP⟩)
      exact mapGraph_subset_permutedUnion σ D (c i) (hi ▸ hnearT f hf i)
  · refine ⟨univ, ?_, fun h => (hR h).elim⟩
    have hpow : (n : ℝ) ^ (-(α * ((q.choose r - 1 : ℕ) : ℝ) * q.choose r)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hn1)
        (neg_nonpos.mpr (by positivity))
    have hc0 : 0 ≤ min (nearFrameDensityConstant b q r) (3 / 4) :=
      le_min (nearFrameDensityConstant_pos hb q r).le (by norm_num)
    have hc := (mul_le_mul_of_nonneg_left hpow hc0).trans
      (by simpa only [mul_one] using min_le_right (nearFrameDensityConstant b q r) (3 / 4))
    have hext := card_embeddingExtension_three_quarters φ
      (by simpa only [Fintype.card_fin] using hn)
    rw [Fintype.card_fin, S.base.property] at hext
    rw [card_univ]
    exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans hext

end Arxiv2411_18291
