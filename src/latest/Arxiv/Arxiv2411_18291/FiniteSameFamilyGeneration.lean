import Arxiv.Arxiv2411_18291.FiniteRainbowReplacements
import Arxiv.Arxiv2411_18291.PermutationColourConditioning
import Arxiv.Arxiv2411_18291.FiniteColourPaletteBudget

/-! # Rainbow generation using unused colours of the same family -/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem exists_colour_extension {I T : Type*} [Fintype I] [Fintype T]
    (E : Finset I) (hroom : E.card + Fintype.card T ≤ Fintype.card I) :
    ∃ e : E ⊕ T ↪ I, ∀ i : E, e (.inl i) = i := by
  classical
  have hc : Fintype.card T ≤ Fintype.card ↥((E : Set I)ᶜ) := by
    rw [Fintype.card_compl_set]
    simpa using (show Fintype.card T ≤ Fintype.card I - E.card by omega)
  obtain ⟨t⟩ := Function.Embedding.nonempty_of_card_le hc
  let e : E ⊕ T ↪ I :=
    (Function.Embedding.sumMap (Function.Embedding.refl E) t).trans
      (Equiv.Set.sumCompl (E : Set I)).toEmbedding
  exact ⟨e, fun _ => rfl⟩

theorem IsRainbow.exists_palette {I V : Type*} {k : ℕ}
    {colour : I → Hypergraph V k} {H : Hypergraph V k} (hH : IsRainbow colour H) :
    ∃ E : Finset I, E.card = H.card ∧ IsRainbow (fun i : E => colour i) H := by
  classical
  obtain ⟨c, hc⟩ := hH
  let E : Finset I := univ.map c
  have hm (x : H) : c x ∈ E := mem_map.mpr ⟨x, mem_univ _, rfl⟩
  let d : H ↪ E := ⟨fun x => ⟨c x, hm x⟩,
    fun _ _ h => c.injective (congrArg Subtype.val h)⟩
  refine ⟨E, ?_, d, hc⟩
  simp only [E, card_map, card_univ, Fintype.card_coe]

variable {I J W : Type*} [Fintype I] [Finite J] [Fintype W] [DecidableEq W]
variable {q r n h : ℕ} {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)}

theorem palette_rainbow_generation_failure_square_paper_threshold {N : ℕ}
    [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))] (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (hqh : q.choose (r + 1) ≤ h)
    (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (C : ModularGeneratingData K (cliqueFamily K q) N)
    (hsat : (C.saturated.card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * (cliqueFamily K q).card)
    (hcount : ∀ e ∈ C.good,
      |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
            cliqueMainTerm n (density K) q (r + 1) (r + 1))
    (e : J ⊕ (Fin (paperColourTrialCount q (r + 1) S.base.val.card) × S.farCliques) ↪ I) :
    (RandomPermutation.probability I (Fin n)).real
      {σ | ¬ ∀ Q : Block (Fin n) q,
        IsRainbow (fun j => mapGraph (σ (e (.inl j))).toEmbedding C.good)
          (cliqueEdges (r + 1) Q) →
        modularCliqueVector N (r + 1) Q ∈
          generatedSubgroup (modularCliqueVector N (r + 1))
            (permutedUnion σ C.generators)} ≤ (n : ℝ) ^ (-2 : ℝ) := by
  classical
  let := Fintype.ofFinite J
  let T := Fin (paperColourTrialCount q (r + 1) S.base.val.card) × S.farCliques
  let B : Set (RandomPermutation.Sample J (Fin n) × RandomPermutation.Sample T (Fin n)) :=
    {z | ¬ ∀ Q : Block (Fin n) q,
      IsRainbow (fun j => mapGraph (z.1 j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
      modularCliqueVector N (r + 1) Q ∈
        generatedSubgroup (modularCliqueVector N (r + 1))
          (permutedUnion z.1 C.generators ∪ permutedUnion z.2 C.generators)}
  have hB (σ : RandomPermutation.Sample J (Fin n)) :
      (RandomPermutation.probability T (Fin n)).real {τ | (σ, τ) ∈ B} ≤
        (n : ℝ) ^ (-2 : ℝ) := by
    rw [RandomPermutation.probability_real_uncurry]
    exact sparse_host_rainbow_generation_failure_square_paper_threshold hA hqr hn
      hw hqh hSh hH K hT hd C hsat hcount σ
  have hb := RandomPermutation.probability_sections_le e B (by positivity) hB
  refine (measureReal_mono ?_ (by finiteness)).trans hb
  intro σ hbad hgood
  apply hbad
  intro Q hQ
  apply generatedSubgroup_mono _ ?_ (hgood Q hQ)
  intro P hP
  rcases mem_union.mp hP with hleft | hright
  · obtain ⟨j, P', hP', hPP'⟩ := (mem_permutedUnion _ _ _).mp hleft
    exact (mem_permutedUnion _ _ _).mpr ⟨e (.inl j), P', hP', hPP'⟩
  · obtain ⟨j, P', hP', hPP'⟩ := (mem_permutedUnion _ _ _).mp hright
    exact (mem_permutedUnion _ _ _).mpr ⟨e (.inr j), P', hP', hPP'⟩

theorem same_family_rainbow_generation_failure_bound {N : ℕ}
    [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))] (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (hqh : q.choose (r + 1) ≤ h)
    (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (C : ModularGeneratingData K (cliqueFamily K q) N)
    (hsat : (C.saturated.card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * (cliqueFamily K q).card)
    (hcount : ∀ e ∈ C.good,
      |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
            cliqueMainTerm n (density K) q (r + 1) (r + 1))
    (hroom : q.choose (r + 1) +
      paperColourTrialCount q (r + 1) S.base.val.card * S.farCliques.card ≤ Fintype.card I) :
    (RandomPermutation.probability I (Fin n)).real
      {σ | ¬ ∀ Q : Block (Fin n) q,
        IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
        modularCliqueVector N (r + 1) Q ∈
          generatedSubgroup (modularCliqueVector N (r + 1))
            (permutedUnion σ C.generators)} ≤
      ((Fintype.card I).choose (q.choose (r + 1)) : ℝ) * (n : ℝ) ^ (-2 : ℝ) := by
  classical
  let B (E : Finset I) : Set (RandomPermutation.Sample I (Fin n)) :=
    {σ | ¬ ∀ Q : Block (Fin n) q,
      IsRainbow (fun j : E => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
      modularCliqueVector N (r + 1) Q ∈
        generatedSubgroup (modularCliqueVector N (r + 1)) (permutedUnion σ C.generators)}
  let tests := (univ : Finset I).powersetCard (q.choose (r + 1))
  have hB (E : Finset I) (hE : E ∈ tests) :
      (RandomPermutation.probability I (Fin n)).real (B E) ≤ (n : ℝ) ^ (-2 : ℝ) := by
    have hcard := (mem_powersetCard.mp hE).2
    obtain ⟨e, he⟩ := exists_colour_extension
      (T := Fin (paperColourTrialCount q (r + 1) S.base.val.card) × S.farCliques) E
      (by simpa only [Fintype.card_prod, Fintype.card_fin, Fintype.card_coe, hcard] using hroom)
    have hb := palette_rainbow_generation_failure_square_paper_threshold hA hqr hn
      hw hqh hSh hH K hT hd C hsat hcount e
    simpa only [he, B] using hb
  have hsub : {σ : RandomPermutation.Sample I (Fin n) | ¬ ∀ Q : Block (Fin n) q,
      IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
      modularCliqueVector N (r + 1) Q ∈
        generatedSubgroup (modularCliqueVector N (r + 1)) (permutedUnion σ C.generators)} ⊆
      ⋃ E ∈ tests, B E := by
    intro σ hbad
    by_contra hnone
    apply hbad
    intro Q hQ
    obtain ⟨E, hcard, hrain⟩ := hQ.exists_palette
    have hE : E ∈ tests := mem_powersetCard.mpr
      ⟨subset_univ _, hcard.trans (card_cliqueEdges Q)⟩
    have hgood : σ ∉ B E := fun hh =>
      hnone (Set.mem_iUnion.mpr ⟨E, Set.mem_iUnion.mpr ⟨hE, hh⟩⟩)
    exact (not_not.mp hgood) Q hrain
  calc
    _ ≤ (RandomPermutation.probability I (Fin n)).real (⋃ E ∈ tests, B E) :=
      measureReal_mono hsub (measure_ne_top _ _)
    _ ≤ ∑ E ∈ tests, (RandomPermutation.probability I (Fin n)).real (B E) :=
      measureReal_biUnion_finset_le tests B
    _ ≤ ∑ _E ∈ tests, (n : ℝ) ^ (-2 : ℝ) := sum_le_sum hB
    _ = _ := by simp only [sum_const, nsmul_eq_mul, tests, card_powersetCard, card_univ]

theorem same_family_rainbow_generation_failure_five_thirds_paper_threshold {N : ℕ}
    [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))] (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (hqh : q.choose (r + 1) ≤ h)
    (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (C : ModularGeneratingData K (cliqueFamily K q) N)
    (hsat : (C.saturated.card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * (cliqueFamily K q).card)
    (hcount : ∀ e ∈ C.good,
      |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
            cliqueMainTerm n (density K) q (r + 1) (r + 1))
    (hroom : q.choose (r + 1) +
      paperColourTrialCount q (r + 1) S.base.val.card * S.farCliques.card ≤ Fintype.card I)
    (hu : Fintype.card I ≤ correctedColourPaletteSize q (r + 1) S.graph.card) :
    (RandomPermutation.probability I (Fin n)).real
      {σ | ¬ ∀ Q : Block (Fin n) q,
        IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
        modularCliqueVector N (r + 1) Q ∈
          generatedSubgroup (modularCliqueVector N (r + 1))
            (permutedUnion σ C.generators)} ≤ (n : ℝ) ^ (-(5 / 3 : ℝ)) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hc : ((Fintype.card I).choose (q.choose (r + 1)) : ℝ) ≤
      (n : ℝ) ^ (1 / 3 : ℝ) := by
    have hp : ((Fintype.card I).choose (q.choose (r + 1)) : ℝ) ≤
        (Fintype.card I : ℝ) ^ q.choose (r + 1) := by
      exact_mod_cast Nat.choose_le_pow (Fintype.card I) (q.choose (r + 1))
    exact hp.trans (colour_palette_power_le_cuberoot_paper_threshold hqr hn (hSh.trans hH) hu)
  calc
    _ ≤ ((Fintype.card I).choose (q.choose (r + 1)) : ℝ) * (n : ℝ) ^ (-2 : ℝ) :=
      same_family_rainbow_generation_failure_bound hA hqr hn hw hqh hSh hH
        K hT hd C hsat hcount hroom
    _ ≤ (n : ℝ) ^ (1 / 3 : ℝ) * (n : ℝ) ^ (-2 : ℝ) :=
      mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

theorem same_family_rainbow_generation_failure_paper_threshold {N : ℕ}
    [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))] (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (hqh : q.choose (r + 1) ≤ h)
    (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (C : ModularGeneratingData K (cliqueFamily K q) N)
    (hsat : (C.saturated.card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * (cliqueFamily K q).card)
    (hcount : ∀ e ∈ C.good,
      |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
            cliqueMainTerm n (density K) q (r + 1) (r + 1))
    (hroom : q.choose (r + 1) +
      paperColourTrialCount q (r + 1) S.base.val.card * S.farCliques.card ≤ Fintype.card I)
    (hu : Fintype.card I ≤ correctedColourPaletteSize q (r + 1) S.graph.card) :
    (RandomPermutation.probability I (Fin n)).real
      {σ | ¬ ∀ Q : Block (Fin n) q,
        IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
        modularCliqueVector N (r + 1) Q ∈
          generatedSubgroup (modularCliqueVector N (r + 1))
            (permutedUnion σ C.generators)} ≤ (n : ℝ) ^ (-1 : ℝ) := by
  have hn1 : (1 : ℝ) ≤ n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).le.trans hn
  exact (same_family_rainbow_generation_failure_five_thirds_paper_threshold hA hqr hn
    hw hqh hSh hH K hT hd C hsat hcount hroom hu).trans
      (Real.rpow_le_rpow_of_exponent_le hn1 (by norm_num))

theorem paper_same_family_rainbow_generation_failure_paper_threshold {N : ℕ}
    [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))] (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (hqh : q.choose (r + 1) ≤ h)
    (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (C : ModularGeneratingData K (cliqueFamily K q) N)
    (hsat : (C.saturated.card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * (cliqueFamily K q).card)
    (hcount : ∀ e ∈ C.good,
      |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
            cliqueMainTerm n (density K) q (r + 1) (r + 1))
    (hq : 3 ≤ q) :
    (RandomPermutation.probability (Fin (paperColourCount q (r + 1) S.graph.card)) (Fin n)).real
      {σ | ¬ ∀ Q : Block (Fin n) q,
        IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
        modularCliqueVector N (r + 1) Q ∈
          generatedSubgroup (modularCliqueVector N (r + 1))
            (permutedUnion σ C.generators)} ≤ (n : ℝ) ^ (-1 : ℝ) := by
  apply same_family_rainbow_generation_failure_paper_threshold hA hqr hn hw hqh hSh hH
    K hT hd C hsat hcount
  · simpa only [Fintype.card_fin] using (paper_colour_palette_room hqr hq S)
  · simpa only [Fintype.card_fin] using
      (paperColourCount_le_correctedColourPaletteSize q (r + 1) S.graph.card)

theorem corrected_same_family_rainbow_generation_failure_paper_threshold {N : ℕ}
    [MeasurableSpace (Equiv.Perm (Fin n))]
    [MeasurableSingletonClass (Equiv.Perm (Fin n))] (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (hqh : q.choose (r + 1) ≤ h)
    (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (C : ModularGeneratingData K (cliqueFamily K q) N)
    (hsat : (C.saturated.card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * (cliqueFamily K q).card)
    (hcount : ∀ e ∈ C.good,
      |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
            cliqueMainTerm n (density K) q (r + 1) (r + 1)) :
    (RandomPermutation.probability
      (Fin (correctedColourPaletteSize q (r + 1) S.graph.card)) (Fin n)).real
      {σ | ¬ ∀ Q : Block (Fin n) q,
        IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
        modularCliqueVector N (r + 1) Q ∈
          generatedSubgroup (modularCliqueVector N (r + 1))
            (permutedUnion σ C.generators)} ≤ (n : ℝ) ^ (-1 : ℝ) := by
  apply same_family_rainbow_generation_failure_paper_threshold hA hqr hn hw hqh hSh hH
    K hT hd C hsat hcount
  · simpa only [Fintype.card_fin] using (corrected_colour_palette_room hqr S)
  · simpa only [Fintype.card_fin] using le_rfl

theorem exists_paper_same_family_rainbow_generators {N : ℕ}
    (hA : IsExchangeFamily S A)
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (hqh : q.choose (r + 1) ≤ h)
    (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (C : ModularGeneratingData K (cliqueFamily K q) N)
    (hsat : (C.saturated.card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * (cliqueFamily K q).card)
    (hcount : ∀ e ∈ C.good,
      |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
            cliqueMainTerm n (density K) q (r + 1) (r + 1))
    (hq : 3 ≤ q) :
    ∃ σ : Fin (paperColourCount q (r + 1) S.graph.card) → Equiv.Perm (Fin n),
      ∀ Q : Block (Fin n) q,
        IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
        modularCliqueVector N (r + 1) Q ∈
          generatedSubgroup (modularCliqueVector N (r + 1))
            (permutedUnion σ C.generators) := by
  classical
  let : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  have hb := paper_same_family_rainbow_generation_failure_paper_threshold hA hqr hn
    hw hqh hSh hH K hT hd C hsat hcount hq
  have hn1 : (1 : ℝ) < n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).trans_le hn
  exact IndependentTrials.exists_of_failure_lt_one _
    (hb.trans_lt (Real.rpow_lt_one_of_one_lt_of_neg hn1 (by norm_num)))

end Arxiv2411_18291
