import Arxiv.Arxiv2411_18291.FiniteRootPatternProbability
import Arxiv.Arxiv2411_18291.FiniteSameFamilyGeneration
import Arxiv.Arxiv2411_18291.FiniteSparseModularGenerators
import Arxiv.Arxiv2411_18291.RainbowGeneratingSystem

/-!
# Simultaneous rainbow extensions and generation in the paper's palette

The punctured-clique count retains its factorial divisor. The two exchange
properties and generation use the same random colours, with total failure
at most n^(-1) for q >= 3 at the printed threshold.
-/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

theorem probability_failure_and_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {P Q : Ω → Prop} {a b : ℝ}
    (hP : μ.real {ω | ¬ P ω} ≤ a) (hQ : μ.real {ω | ¬ Q ω} ≤ b) :
    μ.real {ω | ¬ (P ω ∧ Q ω)} ≤ a + b := by
  have heq : {ω | ¬ (P ω ∧ Q ω)} = {ω | ¬ P ω} ∪ {ω | ¬ Q ω} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Set.mem_union, not_and_or]
  rw [heq]
  exact (measureReal_union_le _ _).trans (add_le_add hP hQ)

variable {U W : Type*} [Fintype U] [Fintype W] [DecidableEq W] {q r n h N : ℕ}
variable {S : ExchangeSystem W q (r + 1)} {A : Finset (Block W q)}
variable {P₀ : Block W q} {e₀ : Block W (r + 1)}
variable [MeasurableSpace (Equiv.Perm (Fin n))]
variable [MeasurableSingletonClass (Equiv.Perm (Fin n))]

theorem joint_rainbow_generation_failure_paper_threshold
    (hqr : r + 1 < q) (hq : 3 ≤ q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (F₀ : Block U (r + 1)) (hU : Fintype.card U = q)
    (hA : IsExchangeFamily S A) (hpair : IsEliminationPair S P₀ e₀)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (hqh : q.choose (r + 1) ≤ h) (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (C : ModularGeneratingData K (cliqueFamily K q) N)
    (hgood : ((K \ C.good).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (hsat : (C.saturated.card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * (cliqueFamily K q).card)
    (hcount : ∀ e ∈ C.good,
      |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
            cliqueMainTerm n (density K) q (r + 1) (r + 1)) :
    (RandomPermutation.probability (Fin (paperColourCount q (r + 1) S.graph.card)) (Fin n)).real
      {σ | ¬ (RainbowExtensionProperties S P₀ σ C.good ∧
        ∀ Q : Block (Fin n) q,
          IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
          modularCliqueVector N (r + 1) Q ∈
            generatedSubgroup (modularCliqueVector N (r + 1))
              (permutedUnion σ C.generators))} ≤ (n : ℝ) ^ (-1 : ℝ) := by
  classical
  let I := Fin (paperColourCount q (r + 1) S.graph.card)
  let μ := RandomPermutation.probability I (Fin n)
  have hroom : paperCommonColourTrialCount q (r + 1) * S.graph.card ≤ Fintype.card I := by
    simpa only [I, Fintype.card_fin] using common_colour_trials_fit_paper_palette
      (r := r + 1) (M := S.graph.card) hq le_rfl
  have hkm : q.choose (r + 1) ≤ S.graph.card := by
    simpa only [card_cliqueEdges] using
      card_le_card (S.positive_decomposition.clique_subset S.base_mem)
  have h1 := rainbow_punctured_cliques_failure_paper_threshold hqr hq hn hqh hH
    F₀ hU K C.good hT hd C.good_subset hgood
    ((Nat.mul_le_mul_left _ ((Nat.sub_le _ _).trans hkm)).trans hroom)
  have h2 := rainbow_clique_roots_failure_paper_threshold hqr hq hn hqh hH hw
    S.graph hSh S.base K C.good hT hd C.good_subset hgood hroom
  have h3 := rainbow_pair_roots_failure_paper_threshold hqr hq hn hqh hH hw
    hpair hSh K C.good hT hd C.good_subset hgood hroom
  have h4 := same_family_rainbow_generation_failure_five_thirds_paper_threshold
    (I := I) hA hqr hn hw hqh hSh hH K hT hd C hsat hcount
    (by simpa only [I, Fintype.card_fin] using paper_colour_palette_room hqr hq S)
    (by simpa only [I, Fintype.card_fin] using
      paperColourCount_le_correctedColourPaletteSize q (r + 1) S.graph.card)
  have hall := probability_failure_and_le μ h1
    (probability_failure_and_le μ h2 (probability_failure_and_le μ h3 h4))
  have hb : μ.real {σ | ¬ (RainbowExtensionProperties S P₀ σ C.good ∧
      ∀ Q : Block (Fin n) q,
        IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
        modularCliqueVector N (r + 1) Q ∈
          generatedSubgroup (modularCliqueVector N (r + 1)) (permutedUnion σ C.generators))} ≤
      (n : ℝ) ^ (-(5 / 3 : ℝ)) + ((n : ℝ) ^ (-(5 / 3 : ℝ)) +
        ((n : ℝ) ^ (-(5 / 3 : ℝ)) + (n : ℝ) ^ (-(5 / 3 : ℝ)))) := by
    refine (measureReal_mono ?_ (measure_ne_top _ _)).trans hall
    intro σ hbad hsuccess
    apply hbad
    refine ⟨⟨?_, hsuccess.2.1, hsuccess.2.2.1⟩, hsuccess.2.2.2⟩
    simpa only [Fintype.card_fin] using hsuccess.1
  calc
    _ ≤ 4 * (n : ℝ) ^ (-(5 / 3 : ℝ)) := by convert hb using 1; ring
    _ ≤ _ := four_colour_failures_le_paper_threshold hqr hn

omit [MeasurableSpace (Equiv.Perm (Fin n))]
  [MeasurableSingletonClass (Equiv.Perm (Fin n))] in
theorem exists_joint_rainbow_generating_family_paper_threshold
    (hqr : r + 1 < q) (hq : 3 ≤ q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (F₀ : Block U (r + 1)) (hU : Fintype.card U = q)
    (hA : IsExchangeFamily S A) (hpair : IsEliminationPair S P₀ e₀)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (hqh : q.choose (r + 1) ≤ h) (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (K : Hypergraph (Fin n) (r + 1))
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)))
    (C : ModularGeneratingData K (cliqueFamily K q) N)
    (hgood : ((K \ C.good).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card)
    (hsat : (C.saturated.card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * (cliqueFamily K q).card)
    (hcount : ∀ e ∈ C.good,
      |((((cliqueFamily K q) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        cliqueMainTerm n (density K) q (r + 1) (r + 1)| ≤
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) *
            cliqueMainTerm n (density K) q (r + 1) (r + 1)) :
    ∃ σ : Fin (paperColourCount q (r + 1) S.graph.card) → Equiv.Perm (Fin n),
      RainbowExtensionProperties S P₀ σ C.good ∧
      ∀ Q : Block (Fin n) q,
        IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
        modularCliqueVector N (r + 1) Q ∈
          generatedSubgroup (modularCliqueVector N (r + 1)) (permutedUnion σ C.generators) := by
  classical
  let : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  have hb := joint_rainbow_generation_failure_paper_threshold hqr hq hn F₀ hU hA hpair
    hw hqh hSh hH K hT hd C hgood hsat hcount
  have hn1 : (1 : ℝ) < n := by
    exact_mod_cast (paperSizeThreshold_one_lt hqr).trans_le hn
  exact IndependentTrials.exists_of_failure_lt_one _
    (hb.trans_lt (Real.rpow_lt_one_of_one_lt_of_neg hn1 (by norm_num)))

omit [MeasurableSpace (Equiv.Perm (Fin n))]
  [MeasurableSingletonClass (Equiv.Perm (Fin n))] in
theorem exists_sparse_joint_rainbow_system_paper_threshold
    (hqr : r + 1 < q) (hq : 3 ≤ q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (F₀ : Block U (r + 1)) (hU : Fintype.card U = q)
    (hA : IsExchangeFamily S A) (hpair : IsEliminationPair S P₀ e₀)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (hqh : q.choose (r + 1) ≤ h) (hSh : S.graph.card ≤ h)
    (hH : h ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (hN : 0 < N) (hNb : N ≤ (r + 1).factorial * q.choose (r + 1)) :
    ∃ K : Hypergraph (Fin n) (r + 1),
      IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h ∧
      |density K - (n : ℝ) ^ (-paperAlpha q (r + 1))| ≤
        (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha q (r + 1)) ∧
      ∃ C : ModularGeneratingData K (cliqueFamily K q) N,
        IsCliqueFamilyBounded r C.generators
          (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10))) ∧
        ((K \ C.good).card : ℝ) ≤
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 10)) * K.card ∧
        ∃ σ : Fin (paperColourCount q (r + 1) S.graph.card) → Equiv.Perm (Fin n),
          RainbowExtensionProperties S P₀ σ C.good ∧
          IsCliqueFamilyBounded r (permutedUnion σ C.generators)
            ((paperColourCount q (r + 1) S.graph.card : ℝ) *
              (2 ^ q * (n : ℝ) ^ (-(7 * paperAlpha q (r + 1) / 10)))) ∧
          ∀ Q : Block (Fin n) q,
            IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges (r + 1) Q) →
            modularCliqueVector N (r + 1) Q ∈
              generatedSubgroup (modularCliqueVector N (r + 1)) (permutedUnion σ C.generators) := by
  classical
  obtain ⟨K, hT, hd, C, hCb, _, hsat, hgood, hcount⟩ :=
    exists_sparse_modular_generators_paper_threshold hqr hn hN hNb hqh hH
  obtain ⟨σ, hext, hgen⟩ := exists_joint_rainbow_generating_family_paper_threshold
    hqr hq hn F₀ hU hA hpair hw hqh hSh hH K hT hd C hgood hsat
    (fun e he => (hcount e he).le)
  have hM : 0 < S.graph.card := by
    have hkm : q.choose (r + 1) ≤ S.graph.card := by
      simpa only [card_cliqueEdges] using
        card_le_card (S.positive_decomposition.clique_subset S.base_mem)
    exact (Nat.choose_pos hqr.le).trans_le hkm
  have hu : 0 < paperColourCount q (r + 1) S.graph.card := by
    have hA := paperInverseAlpha_pos hqr
    unfold paperColourCount
    positivity
  have : Nonempty (Fin (paperColourCount q (r + 1) S.graph.card)) := ⟨⟨0, hu⟩⟩
  refine ⟨K, hT, hd, C, hCb, hgood, σ, hext, ?_, hgen⟩
  simpa only [Fintype.card_fin] using hCb.permutedUnion σ

end Arxiv2411_18291
