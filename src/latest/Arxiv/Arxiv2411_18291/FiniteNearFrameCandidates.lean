import Arxiv.Arxiv2411_18291.FiniteNearFrameNumerics
import Arxiv.Arxiv2411_18291.FiniteCliqueColours
import Arxiv.Arxiv2411_18291.ExchangeCliqueCounts
import Arxiv.Arxiv2411_18291.RainbowNearCandidates

/-! # Finite near-frame candidates with a normalized density loss -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem paper_generator_count_error_le_half {q r n : ℕ} (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n) :
    (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) ≤ 1 / 2 := by
  have hk : (1 : ℝ) ≤ q.choose (r + 1) := by exact_mod_cast Nat.choose_pos hqr.le
  have hm := mul_le_mul_of_nonneg_right hk
    (Real.rpow_nonneg (Nat.cast_nonneg n) (-(paperAlpha q (r + 1) / 10)))
  have hs := paper_good_density_error_small hqr hn
  nlinarith only [hm, hs]

theorem good_edge_rooted_count_lower_of_half_error_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (K G : Hypergraph (Fin n) (r + 1)) (D : Finset (Block (Fin n) q))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hcount : ∀ e ∈ G, |((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) -
      cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
        (1 / 2 : ℝ) *
          cliqueMainTerm n (density K) q (r + 1) (r + 1))
    (σ : Equiv.Perm (Fin n)) (e : Block (Fin n) (r + 1))
    (he : e ∈ mapGraph σ.toEmbedding G) :
    ((1 / 2 : ℝ) ^ (q.choose (r + 1) - 1) / (2 * (q - (r + 1)).factorial)) *
      (n : ℝ) ^ (-(paperAlpha q (r + 1) * ((q.choose (r + 1) - 1 : ℕ) : ℝ))) *
        (n : ℝ) ^ (q - (r + 1)) ≤
          ((mapGraph σ.toEmbedding D).filter fun Q => e.val ⊆ Q.val).card := by
  obtain ⟨e₀, he₀, heq⟩ := (mem_mapGraph _ _ _).mp he
  rw [← heq, card_mapGraph_containing]
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hhalf := relative_count_half_lower
    (cliqueMainTerm_nonneg hn0.le (density_nonneg K) q (r + 1) (r + 1))
    (by norm_num) (hcount e₀ he₀)
  have hlo := edgeMainTerm_polynomial_lower hn0 (by norm_num : (0 : ℝ) < 1 / 2)
    (paper_host_density_bounds hqr hn K hd).1 q (r + 1)
  calc
    _ = (((1 / 2 : ℝ) ^ (q.choose (r + 1) - 1) / (q - (r + 1)).factorial) *
        (n : ℝ) ^ (-(paperAlpha q (r + 1) * ((q.choose (r + 1) - 1 : ℕ) : ℝ))) *
          (n : ℝ) ^ (q - (r + 1))) / 2 := by ring
    _ ≤ cliqueMainTerm n (density K) q (r + 1) (r + 1) / 2 :=
      div_le_div_of_nonneg_right hlo (by norm_num)
    _ ≤ _ := hhalf

theorem good_edge_rooted_count_lower_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (K G : Hypergraph (Fin n) (r + 1)) (D : Finset (Block (Fin n) q))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hcount : ∀ e ∈ G, |((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) -
      cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
          cliqueMainTerm n (density K) q (r + 1) (r + 1))
    (σ : Equiv.Perm (Fin n)) (e : Block (Fin n) (r + 1))
    (he : e ∈ mapGraph σ.toEmbedding G) :
    ((1 / 2 : ℝ) ^ (q.choose (r + 1) - 1) / (2 * (q - (r + 1)).factorial)) *
      (n : ℝ) ^ (-(paperAlpha q (r + 1) * ((q.choose (r + 1) - 1 : ℕ) : ℝ))) *
        (n : ℝ) ^ (q - (r + 1)) ≤
          ((mapGraph σ.toEmbedding D).filter fun Q => e.val ⊆ Q.val).card := by
  exact good_edge_rooted_count_lower_of_half_error_paper_threshold hqr hn K G D hd
    (fun e he => (hcount e he).trans (mul_le_mul_of_nonneg_right
      (paper_generator_count_error_le_half hqr hn)
      (cliqueMainTerm_nonneg (Nat.cast_nonneg n) (density_nonneg K) _ _ _))) σ e he

variable {J W : Type*} [Fintype W] [DecidableEq W] {q r n h : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)}

theorem near_frame_candidates_of_half_error_paper_threshold (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K G : Hypergraph (Fin n) (r + 1)) (D : Finset (Block (Fin n) q))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hcount : ∀ e ∈ G, |((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) -
      cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
        (1 / 2 : ℝ) *
          cliqueMainTerm n (density K) q (r + 1) (r + 1))
    (σ : J → Equiv.Perm (Fin n)) (φ : S.base.val ↪ Fin n)
    (colour : Fin (q.choose (r + 1)) → J)
    (hcolour : ∀ i, hA.nearRootImage (Nat.succ_pos r) φ i ∈
      mapGraph (σ (colour i)).toEmbedding G) :
    ∃ T : Finset (EmbeddingExtension φ),
      ((3 / 4 : ℝ) * (n : ℝ) ^ (-(paperAlpha q (r + 1) *
        ((q.choose (r + 1) - 1 : ℕ) : ℝ) * q.choose (r + 1) + 1 / 40))) *
          (n : ℝ) ^ (Fintype.card W - q) ≤ T.card ∧
      ∀ f ∈ T, ∀ i, mapBlock f.val (hA.nearPattern (Nat.succ_pos r) i) ∈
        mapGraph (σ (colour i)).toEmbedding D := by
  classical
  let c : ℝ := (1 / 2 : ℝ) ^ (q.choose (r + 1) - 1) / (2 * (q - (r + 1)).factorial)
  let γ := paperAlpha q (r + 1) * ((q.choose (r + 1) - 1 : ℕ) : ℝ)
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hk : 0 < q.choose (r + 1) := Nat.choose_pos hqr.le
  have hsq := (hA.choose_sq_le (Nat.succ_pos r)).trans hSh
  let idx (i : ℕ) : Fin (q.choose (r + 1)) := if hi : i < q.choose (r + 1) then
    ⟨i, hi⟩ else ⟨0, hk⟩
  have hidx (i : Fin (q.choose (r + 1))) : idx i = i := by
    dsimp only [idx]
    rw [dif_pos i.isLt]
  let e (i : ℕ) := hA.nearRootImage (Nat.succ_pos r) φ (idx i)
  let C (i : ℕ) := (mapGraph (σ (colour (idx i))).toEmbedding D).filter
    (fun Q => (e i).val ⊆ Q.val)
  let Q := hA.nearPattern (Nat.succ_pos r)
  have heB (i : ℕ) : (e i).val ⊆ usedVertices φ :=
    hA.nearRootImage_subset (Nat.succ_pos r) φ (idx i)
  have hC (i : ℕ) : ∀ P ∈ C i, (e i).val ⊆ P.val := fun _ hP => (mem_filter.mp hP).2
  have hφ (i : Fin (q.choose (r + 1))) (x : S.base.val)
      (hx : x.val ∈ (Q i).val) : φ x ∈ (e i).val := by
    simpa only [e, hidx] using hA.nearRootImage_contains (Nat.succ_pos r) φ i x hx
  have hsize (i : ℕ) (_hi : i < q.choose (r + 1)) :
      c * (n : ℝ) ^ (-γ) * (n : ℝ) ^ (q - (r + 1)) ≤ (C i).card :=
    good_edge_rooted_count_lower_of_half_error_paper_threshold hqr hn K G D hd hcount
      (σ (colour (idx i))) (e i) (hcolour (idx i))
  have hbnd := frameCandidateExtensions_card_lower φ Q e C hqr
    (hA.nearPattern_private_pairwise (Nat.succ_pos r))
    (hA.nearPattern_private_card (Nat.succ_pos r)) hφ heB hC
    (by dsimp only [c]; positivity) hsize
    (by simpa only [S.base.property, Fintype.card_fin] using
      near_frame_collision_bound_paper_threshold hqr hn hsq hH)
    (by simpa only [Fintype.card_fin] using paper_small_carrier_completion_size hqr hn hw)
  simp only [Fintype.card_fin] at hbnd
  have hframe : (frameDomain S.base.val Q).card = q + q.choose (r + 1) * (q - (r + 1)) := by
    simpa only [S.base.property, Fintype.card_fin] using frameDomain_card S.base.val Q
      (q - (r + 1)) (hA.nearPattern_private_pairwise (Nat.succ_pos r))
        (hA.nearPattern_private_card (Nat.succ_pos r))
  have hfw := card_le_univ (frameDomain S.base.val Q)
  have hexp : (q - (r + 1)) * q.choose (r + 1) +
      (Fintype.card W - (frameDomain S.base.val Q).card) = Fintype.card W - q := by
    rw [Nat.mul_comm (q - (r + 1))]
    omega
  rw [frame_completion_scale hn0 c γ (q - (r + 1)) (q.choose (r + 1)), hexp] at hbnd
  have hcoeff : (3 / 4 : ℝ) * (c / 2) ^ q.choose (r + 1) =
      nearFrameDensityConstant (1 / 2) q (r + 1) := by
    dsimp only [c, nearFrameDensityConstant]
    congr 1
    congr 1
    ring
  rw [hcoeff] at hbnd
  have hc := near_frame_density_constant_paper_threshold hqr hn hsq hH
  have hscaled := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hn0.le (-(γ * q.choose (r + 1)))))
      (pow_nonneg hn0.le (Fintype.card W - q))
  have heq : ((3 / 4 : ℝ) * (n : ℝ) ^ (-(1 / 40 : ℝ))) *
      (n : ℝ) ^ (-(γ * q.choose (r + 1))) =
        (3 / 4 : ℝ) * (n : ℝ) ^ (-(γ * q.choose (r + 1) + 1 / 40)) := by
    rw [mul_assoc, ← Real.rpow_add hn0]
    congr 2
    ring
  rw [heq] at hscaled
  refine ⟨frameCandidateExtensions φ Q (fun i => C i), hscaled.trans hbnd, ?_⟩
  intro f hf i
  have hfi := ((mem_frameCandidateExtensions φ Q (fun j => C j) f).mp hf) i
  have hmem := (mem_filter.mp hfi).1
  simpa only [C, hidx] using hmem

theorem near_frame_candidates_paper_threshold (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K G : Hypergraph (Fin n) (r + 1)) (D : Finset (Block (Fin n) q))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hcount : ∀ e ∈ G, |((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) -
      cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
          cliqueMainTerm n (density K) q (r + 1) (r + 1))
    (σ : J → Equiv.Perm (Fin n)) (φ : S.base.val ↪ Fin n)
    (colour : Fin (q.choose (r + 1)) → J)
    (hcolour : ∀ i, hA.nearRootImage (Nat.succ_pos r) φ i ∈
      mapGraph (σ (colour i)).toEmbedding G) :
    ∃ T : Finset (EmbeddingExtension φ),
      ((3 / 4 : ℝ) * (n : ℝ) ^ (-(paperAlpha q (r + 1) *
        ((q.choose (r + 1) - 1 : ℕ) : ℝ) * q.choose (r + 1) + 1 / 40))) *
          (n : ℝ) ^ (Fintype.card W - q) ≤ T.card ∧
      ∀ f ∈ T, ∀ i, mapBlock f.val (hA.nearPattern (Nat.succ_pos r) i) ∈
        mapGraph (σ (colour i)).toEmbedding D := by
  exact near_frame_candidates_of_half_error_paper_threshold hA hqr hn hw hSh hH K G D hd
    (fun e he => (hcount e he).trans (mul_le_mul_of_nonneg_right
      (paper_generator_count_error_le_half hqr hn)
      (cliqueMainTerm_nonneg (Nat.cast_nonneg n) (density_nonneg K) _ _ _))) σ φ colour hcolour

theorem rainbow_near_candidates_of_half_error_paper_threshold [Fintype J]
    (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K G : Hypergraph (Fin n) (r + 1)) (D : Finset (Block (Fin n) q))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hcount : ∀ e ∈ G, |((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) -
      cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
        (1 / 2 : ℝ) *
          cliqueMainTerm n (density K) q (r + 1) (r + 1))
    (σ : J → Equiv.Perm (Fin n)) (φ : S.base.val ↪ Fin n) :
    ∃ T : Finset (EmbeddingExtension φ),
      ((3 / 4 : ℝ) * (n : ℝ) ^ (-(paperAlpha q (r + 1) *
        ((q.choose (r + 1) - 1 : ℕ) : ℝ) * q.choose (r + 1) + 1 / 40))) *
          (n : ℝ) ^ (Fintype.card W - q) ≤ T.card ∧
      (IsRainbow (fun j => mapGraph (σ j).toEmbedding G)
        (cliqueEdges (r + 1) (rootImage φ S.base Subset.rfl)) →
        ∀ f ∈ T, ∀ P ∈ S.nearCliques, mapBlock f.val P ∈ permutedUnion σ D) := by
  classical
  by_cases hR : IsRainbow (fun j => mapGraph (σ j).toEmbedding G)
      (cliqueEdges (r + 1) (rootImage φ S.base Subset.rfl))
  · obtain ⟨colour, hcolour⟩ := hR
    let c (i : Fin (q.choose (r + 1))) : J := colour
      ⟨hA.nearRootImage (Nat.succ_pos r) φ i, hA.nearRootImage_mem_base (Nat.succ_pos r) φ i⟩
    obtain ⟨T, hT, hnearT⟩ := near_frame_candidates_of_half_error_paper_threshold
      hA hqr hn hw hSh hH
      K G D hd hcount σ φ c (fun i => hcolour _)
    refine ⟨T, hT, fun _ f hf P hP => ?_⟩
    let i := (hA.nearEnumeration (Nat.succ_pos r)).symm ⟨P, hP⟩
    have hi : hA.nearPattern (Nat.succ_pos r) i = P :=
      congrArg Subtype.val ((hA.nearEnumeration (Nat.succ_pos r)).apply_symm_apply ⟨P, hP⟩)
    exact mapGraph_subset_permutedUnion σ D (c i) (hi ▸ hnearT f hf i)
  · refine ⟨univ, ?_, fun h => (hR h).elim⟩
    have hn1 : (1 : ℝ) ≤ n := by
      exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
    have hα := (paperAlpha_pos hqr).le
    have hpow : (n : ℝ) ^ (-(paperAlpha q (r + 1) *
        ((q.choose (r + 1) - 1 : ℕ) : ℝ) * q.choose (r + 1) + 1 / 40)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hn1 (neg_nonpos.mpr (by positivity))
    have hext := card_embeddingExtension_three_quarters φ
      (by simpa only [Fintype.card_fin] using paper_small_carrier_completion_size hqr hn hw)
    rw [Fintype.card_fin, S.base.property] at hext
    rw [card_univ]
    have hc := mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 3 / 4)
    rw [mul_one] at hc
    exact (mul_le_mul_of_nonneg_right hc (by positivity)).trans hext

theorem rainbow_near_candidates_paper_threshold [Fintype J] (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K G : Hypergraph (Fin n) (r + 1)) (D : Finset (Block (Fin n) q))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hcount : ∀ e ∈ G, |((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) -
      cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
        (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
          cliqueMainTerm n (density K) q (r + 1) (r + 1))
    (σ : J → Equiv.Perm (Fin n)) (φ : S.base.val ↪ Fin n) :
    ∃ T : Finset (EmbeddingExtension φ),
      ((3 / 4 : ℝ) * (n : ℝ) ^ (-(paperAlpha q (r + 1) *
        ((q.choose (r + 1) - 1 : ℕ) : ℝ) * q.choose (r + 1) + 1 / 40))) *
          (n : ℝ) ^ (Fintype.card W - q) ≤ T.card ∧
      (IsRainbow (fun j => mapGraph (σ j).toEmbedding G)
        (cliqueEdges (r + 1) (rootImage φ S.base Subset.rfl)) →
        ∀ f ∈ T, ∀ P ∈ S.nearCliques, mapBlock f.val P ∈ permutedUnion σ D) := by
  exact rainbow_near_candidates_of_half_error_paper_threshold hA hqr hn hw hSh hH K G D hd
    (fun e he => (hcount e he).trans (mul_le_mul_of_nonneg_right
      (paper_generator_count_error_le_half hqr hn)
      (cliqueMainTerm_nonneg (Nat.cast_nonneg n) (density_nonneg K) _ _ _))) σ φ

end Arxiv2411_18291
