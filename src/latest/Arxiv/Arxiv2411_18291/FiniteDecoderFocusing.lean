import Arxiv.Arxiv2411_18291.FiniteGeneratorAssemblyThreshold
import Arxiv.Arxiv2411_18291.FiniteFocusingFamily

/-! # Finite assembly of generators, focusing cliques, and local decoders -/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_decoder_focusing_augmentation_paper_threshold {I : Type*} [Fintype I]
    {q r n : ℕ} (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    {C : ℝ} (hC : 0 ≤ C) (hCb : C + 1 ≤ (4 * q : ℝ) ^ (6 * q))
    (K G : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (σ : I → Equiv.Perm (Fin n))
    (hcount : ∀ e : Block (Fin n) (r + 1),
      ((3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) *
        (n : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial ≤
          (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card)
    (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1))))
    (F₀ : Finset (Block (Fin n) q))
    (hF₀ : IsCliqueFamilyBounded r F₀
      (C * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)))) :
    ∃ D : Finset (Block (Fin n) q), F₀ ⊆ D ∧
      IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) / 2) ∧
      (∀ J : Block (Fin n) (r + 1) → ℤ,
        (∀ e, e ∉ cliqueSupport (r + 1) F₀ → J e = 0) →
        (∀ e, (((r + 1).factorial * q.choose (r + 1) : ℕ) : ℤ) ∣ J e) → GeneratedBy D J) ∧
      ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
        IntegrallyDecomposable q J →
        ∃ J' : Block (Fin n) (r + 1) → ℤ, GeneratedBy D (J - J') ∧
          (∀ e, e ∉ permutedUnion σ G → J' e = 0) ∧ IntegrallyDecomposable q J' := by
  obtain ⟨F, hF, hfocus⟩ := exists_sparse_coloured_focusing_paper_threshold hqr hn
    K G hd hGK hloss σ hcount B hB
  have hsum : IsCliqueFamilyBounded r (F₀ ∪ F)
      ((C + 1) * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) := by
    simpa only [add_mul, one_mul] using hF₀.union hF
  obtain ⟨D, hsub, hD, hdecode⟩ := augment_with_local_decoders_paper_threshold hqr hn
    (by linarith only [hC] : 1 ≤ C + 1) hCb (F₀ ∪ F) hsum
  have hsupport : cliqueSupport (r + 1) F₀ ⊆ cliqueSupport (r + 1) (F₀ ∪ F) := by
    intro e he
    obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨Q, mem_union_left _ hQ, heQ⟩
  refine ⟨D, subset_union_left.trans hsub, hD, ?_, ?_⟩
  · intro J hs hdiv
    exact hdecode J (fun e he => hs e (fun he₀ => he (hsupport he₀))) hdiv
  · intro J hs hInt
    obtain ⟨J', hJ', hs', hInt'⟩ := hfocus J hs hInt
    exact ⟨J', hJ'.mono (subset_union_right.trans hsub), hs', hInt'⟩

/-- Any fixed input coefficient is allowed above an explicit larger threshold. -/
theorem exists_decoder_focusing_augmentation_explicit {I : Type*} [Fintype I]
    {q r n : ℕ} {C : ℝ} (hqr : r + 1 < q)
    (hn : finiteGeneratorAssemblyThreshold q r C ≤ n)
    (K G : Hypergraph (Fin n) (r + 1))
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (hGK : G ⊆ K)
    (hloss : ((K \ G).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (σ : I → Equiv.Perm (Fin n))
    (hcount : ∀ e : Block (Fin n) (r + 1),
      ((3 / 8 : ℝ) * density G ^ (q.choose (r + 1) - 1) *
        (n : ℝ) ^ (q - (r + 1))) / (q - (r + 1)).factorial ≤
          (rainbowPuncturedCliques (fun i => mapGraph (σ i).toEmbedding G) e q).card)
    (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1))))
    (F₀ : Finset (Block (Fin n) q))
    (hF₀ : IsCliqueFamilyBounded r F₀
      (C * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)))) :
    ∃ D : Finset (Block (Fin n) q), F₀ ⊆ D ∧
      IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))) ∧
      (∀ J : Block (Fin n) (r + 1) → ℤ,
        (∀ e, e ∉ cliqueSupport (r + 1) F₀ → J e = 0) →
        (∀ e, (((r + 1).factorial * q.choose (r + 1) : ℕ) : ℤ) ∣ J e) → GeneratedBy D J) ∧
      ∀ J : Block (Fin n) (r + 1) → ℤ, (∀ e, e ∉ B → J e = 0) →
        IntegrallyDecomposable q J →
        ∃ J' : Block (Fin n) (r + 1) → ℤ, GeneratedBy D (J - J') ∧
          (∀ e, e ∉ permutedUnion σ G → J' e = 0) ∧ IntegrallyDecomposable q J' := by
  have hnPaper : paperSizeThreshold q (r + 1) ≤ n := (le_max_left _ _).trans hn
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hnPaper
  have hα := paperAlpha_pos hqr
  have hα1 := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  obtain ⟨F, hF, hfocus⟩ := exists_sparse_coloured_focusing_paper_threshold hqr hnPaper
    K G hd hGK hloss σ hcount B hB
  have hF₀n := hF₀.mono (generator_input_normalization_explicit hqr hn)
  have hFn := hF.mono (Real.rpow_le_rpow_of_exponent_le hn1
    (by linarith only [hα] : -(7 * paperAlpha q (r + 1) / 10) ≤
      -(13 * paperAlpha q (r + 1) / 20)))
  have hsum : IsCliqueFamilyBounded r (F₀ ∪ F)
      (2 * (n : ℝ) ^ (-(13 * paperAlpha q (r + 1) / 20))) := by
    simpa only [two_mul] using hF₀n.union hFn
  have hC24 : (2 : ℝ) ≤ (4 * q : ℝ) ^ (24 * q) := by
    calc
      _ ≤ (4 * q : ℝ) ^ 1 := by simp only [pow_one]; linarith only [hq]
      _ ≤ _ := pow_le_pow_right₀ (by linarith only [hq]) (by omega)
  obtain ⟨D, hsub, hDb, hdecode⟩ := augment_with_local_decoders_at_exponent hqr hnPaper
    (by norm_num : (1 : ℝ) ≤ 2) hC24
    (by linarith only [hα] : paperAlpha q (r + 1) / 3 ≤ 13 * paperAlpha q (r + 1) / 20)
    (by linarith only [hα1] : 13 * paperAlpha q (r + 1) / 20 ≤ 1 / 2) (F₀ ∪ F) hsum
  have hD := hDb.mono (normalized_decoder_cost_paper_threshold hqr hnPaper)
  have hsupport : cliqueSupport (r + 1) F₀ ⊆ cliqueSupport (r + 1) (F₀ ∪ F) := by
    intro e he
    obtain ⟨Q, hQ, heQ⟩ := mem_biUnion.mp he
    exact mem_biUnion.mpr ⟨Q, mem_union_left _ hQ, heQ⟩
  refine ⟨D, subset_union_left.trans hsub, hD, ?_, ?_⟩
  · intro J hs hdiv
    exact hdecode J (fun e he => hs e (fun he₀ => he (hsupport he₀))) hdiv
  · intro J hs hInt
    obtain ⟨J', hJ', hs', hInt'⟩ := hfocus J hs hInt
    exact ⟨J', hJ'.mono (subset_union_right.trans hsub), hs', hInt'⟩

end Arxiv2411_18291
