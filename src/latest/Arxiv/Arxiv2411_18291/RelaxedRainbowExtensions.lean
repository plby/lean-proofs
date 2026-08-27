import Arxiv.Arxiv2411_18291.RelaxedColourExtensions
import Arxiv.Arxiv2411_18291.FiniteRainbowExtensions
import Arxiv.Arxiv2411_18291.EdgeCappedAtThreshold

/-! # Constructed rainbow extensions for the edge-capped good host

Logarithmically many independent trials supply one palette working for every
root. Its union of modular generators retains both the face bound and the
edge cap, each multiplied by the actual number of colours.
-/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem exists_many_rainbow_extensions_relaxed_paper_threshold {W : Type*} [Fintype W]
    {q r n h : ℕ} (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (F : Finset W)
    (E : Hypergraph W (r + 1)) (hEh : E.card ≤ h) (hroot : ∀ e ∈ E, ¬e.val ⊆ F)
    (K G : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) * K.card) :
    ∃ σ : Option (Fin (logarithmicColourTrialCount n F.card) × E) → Equiv.Perm (Fin n),
      ∀ φ : F ↪ Fin n,
        (3 / 8 : ℝ) * density G ^ E.card * (n : ℝ) ^ (Fintype.card W - F.card) <
          (rainbowExtensions φ E σ G).card := by
  classical
  let : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  have hnsize := paper_small_carrier_completion_size hqr hn hw
  have hroot' : ∀ e ∈ (univ : Finset E), (e.val.val ∩ F).card < r + 1 :=
    fun e _ => block_root_inter_card_lt e.val (hroot e.val e.property)
  have hsize (φ : F ↪ Fin n) : (3 / 4 : ℝ) *
      (n : ℝ) ^ (Fintype.card W - F.card) ≤ (univ : Finset (EmbeddingExtension φ)).card := by
    simpa only [card_univ, Fintype.card_fin] using card_embeddingExtension_three_quarters φ
      (by simpa only [Fintype.card_fin] using hnsize)
  have hprob := uniform_coloured_extensions_relaxed_failure_paper_threshold hqr hn hqh hH
    F hw univ (fun e : E => e.val) (by simpa only [card_univ, Fintype.card_coe] using hEh)
    hroot' K G hT hd hGK hloss (fun _ => univ) hsize
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (paperSizeThreshold_one_lt hqr).trans_le hn
  obtain ⟨ω, hω⟩ := IndependentTrials.exists_of_failure_lt_one _
    (hprob.trans_lt (Real.rpow_lt_one_of_one_lt_of_neg hn1 (by norm_num)))
  refine ⟨groupedPermutation ω, fun φ => ?_⟩
  obtain ⟨j, hj⟩ := hω φ
  simp only [card_univ, Fintype.card_coe] at hj
  have hs := hsize φ
  rw [card_univ] at hs
  have hm := mul_le_mul_of_nonneg_right hs (pow_nonneg (density_nonneg G) E.card)
  have hmean : (3 / 8 : ℝ) * density G ^ E.card *
      (n : ℝ) ^ (Fintype.card W - F.card) ≤
        (Fintype.card (EmbeddingExtension φ) : ℝ) * density G ^ E.card / 2 := by
    nlinarith only [hm]
  exact (hmean.trans_lt hj).trans_le (extensionColourCount_le_rainbow_card φ E G ω j)

theorem exists_edge_capped_rainbow_host_paper_threshold {W : Type*} [Fintype W]
    {q r n h N : ℕ} (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hN : 0 < N) (hNb : N ≤ (r + 1).factorial * q.choose (r + 1))
    (hqh : q.choose (r + 1) ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (F : Finset W)
    (E : Hypergraph W (r + 1)) (hEh : E.card ≤ h) (hroot : ∀ e ∈ E, ¬e.val ⊆ F) :
    ∃ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h ∧
      |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
        (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ∧
      ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
        IsCliqueFamilyBounded r C.generators
          (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
        (∀ e : Block (Fin n) (r + 1),
          ((C.generators.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
            (n : ℝ) ^ (paperAlpha q (r + 1) / 20)) ∧
        C.generators.card ≤ N * K.card ∧
        (C.saturated.card : ℝ) ≤
          ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 60))) ^ 2 * (cliqueFamily K q).card ∧
        ((K \ C.good).card : ℝ) ≤
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) * K.card ∧
        (∀ e ∈ C.good,
          |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
            cliqueMainTerm n (density K) q (r + 1) (r + 1)| <
            (n : ℝ) ^ (-(paperAlpha q (r + 1) / 60)) *
              cliqueMainTerm n (density K) q (r + 1) (r + 1)) ∧
        ∃ σ : Option (Fin (logarithmicColourTrialCount n F.card) × E) → Equiv.Perm (Fin n),
          (∀ φ : F ↪ Fin n,
            (3 / 8 : ℝ) * density C.good ^ E.card * (n : ℝ) ^ (Fintype.card W - F.card) <
              (rainbowExtensions φ E σ C.good).card) ∧
          IsCliqueFamilyBounded r (permutedUnion σ C.generators)
            ((logarithmicColourTrialCount n F.card * E.card + 1 : ℕ) *
              (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)))) ∧
          ∀ e : Block (Fin n) (r + 1),
            (((permutedUnion σ C.generators).filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
              (logarithmicColourTrialCount n F.card * E.card + 1 : ℕ) *
                (n : ℝ) ^ (paperAlpha q (r + 1) / 20) := by
  classical
  obtain ⟨K, hT, hd, C, hF, hcap, hcard, hsat, hgood, hcount⟩ :=
    exists_sparse_edge_capped_modular_generators_paper_threshold hqr hn hN hNb hqh hH
  obtain ⟨σ, hσ⟩ := exists_many_rainbow_extensions_relaxed_paper_threshold
    hqr hn hqh hH hw F E hEh hroot K C.good hT hd C.good_subset hgood
  refine ⟨K, hT, hd, C, hF, hcap, hcard, hsat, hgood, hcount, σ, hσ, ?_, ?_⟩
  · simpa only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_coe] using hF.permutedUnion σ
  · intro e
    simpa only [Fintype.card_option, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_coe] using containing_permutedUnion_le σ C.generators hcap e

end Arxiv2411_18291
