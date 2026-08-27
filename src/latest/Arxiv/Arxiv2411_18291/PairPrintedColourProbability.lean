import Arxiv.Arxiv2411_18291.PairColourExchange
import Arxiv.Arxiv2411_18291.AllRanksColourProbability
import Arxiv.Arxiv2411_18291.PrintedJointColourProbability

/-!
# All four colour conclusions in the printed palette for pairs

The four-vertex exchange uses two new edges over one base pair, one over
two opposite pairs, and one far clique for modular generation. The exact
counts allow the existing finite probability estimates in the smaller
printed palette, including the source punctured-clique coefficient one half.
-/

open Finset MeasureTheory

noncomputable section

namespace Arxiv2411_18291

def PairPrintedColourSuccess {n N : ℕ} {I : Type*} [Fintype I]
    {K : Hypergraph (Fin n) 1} (C : ModularGeneratingData K (cliqueFamily K 2) N)
    (σ : I → Equiv.Perm (Fin n)) : Prop :=
  PaperRainbowExtensionProperties pairColourExchange pairColourNearZero σ C.good ∧
    ∀ Q : Block (Fin n) 2,
      IsRainbow (fun j => mapGraph (σ j).toEmbedding C.good) (cliqueEdges 1 Q) →
      modularCliqueVector N 1 Q ∈
        generatedSubgroup (modularCliqueVector N 1) (permutedUnion σ C.generators)

variable {n h N : ℕ}
variable [MeasurableSpace (Equiv.Perm (Fin n))]
variable [MeasurableSingletonClass (Equiv.Perm (Fin n))]

theorem pair_printed_joint_colour_failure_paper_threshold
    (hn : paperSizeThreshold 2 1 ≤ n) (hh : 4 ≤ h) (hH : h ≤ 48)
    (K : Hypergraph (Fin n) 1)
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha 2 1)| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha 2 1))
    (C : ModularGeneratingData K (cliqueFamily K 2) N)
    (hgood : ((K \ C.good).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha 2 1 / 10)) * K.card)
    (hsat : (C.saturated.card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha 2 1 / 10)) * (cliqueFamily K 2).card)
    (hcount : ∀ e ∈ C.good,
      |((((cliqueFamily K 2) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        cliqueMainTerm n (density K) 2 1 1| ≤
          (n : ℝ) ^ (-(paperAlpha 2 1 / 10)) * cliqueMainTerm n (density K) 2 1 1) :
    (RandomPermutation.probability
      (Fin (paperColourCount 2 1 pairColourExchange.graph.card)) (Fin n)).real
      {σ | ¬ PairPrintedColourSuccess C σ} ≤ (n : ℝ) ^ (-1 : ℝ) := by
  classical
  let I := Fin (paperColourCount 2 1 pairColourExchange.graph.card)
  let μ := RandomPermutation.probability I (Fin n)
  let F₀ : Block (Fin 2) 1 := ⟨{0}, by decide⟩
  have hqr : 0 + 1 < 2 := by decide
  have hqh : Nat.choose 2 (0 + 1) ≤ h := by norm_num; omega
  have hH' : h ≤ 3 * (2 * 2) ^ (0 + 1) * (Nat.choose 2 (0 + 1)) ^ 2 := by
    norm_num
    exact hH
  have hw : Fintype.card (Fin 4) ≤ (4 * 2) ^ (2 * 2) := by decide
  have hSh : pairColourExchange.graph.card ≤ h := by
    simpa only [pairColourExchange_card] using hh
  have h1 := all_ranks_rainbow_punctured_cliques_failure_paper_threshold (I := I)
    hqr hn hqh hH' F₀ (Fintype.card_fin _) K C.good hT hd C.good_subset hgood
    (by simpa only [I, Fintype.card_fin] using pairColourExchange_punctured_palette)
  have h2 := all_ranks_rainbow_clique_roots_failure_of_new_edges (I := I)
    hqr hn hqh hH' hw pairColourExchange.graph hSh pairColourExchange.base
    K C.good hT hd C.good_subset hgood
    (by simpa only [I, Fintype.card_fin] using pairColourExchange_clique_palette)
  have h3 := all_ranks_rainbow_pair_roots_failure_of_new_edges (I := I)
    hqr hn hqh hH' hw pairColourExchange_elimination_pair hSh
    K C.good hT hd C.good_subset hgood
    (by simpa only [I, Fintype.card_fin] using pairColourExchange_pair_palette)
  have h4 := same_family_rainbow_generation_failure_five_thirds_paper_threshold (I := I)
    pairColourExchange_exchange_family hqr hn hw hqh hSh hH' K hT hd C hsat hcount
    (by simpa only [I, Fintype.card_fin] using pairColourExchange_generation_palette)
    (by simpa only [I, Fintype.card_fin] using
      paperColourCount_le_correctedColourPaletteSize 2 1 pairColourExchange.graph.card)
  have hall := probability_failure_and_le μ h1
    (probability_failure_and_le μ h2 (probability_failure_and_le μ h3 h4))
  have hb : μ.real {σ | ¬ PairPrintedColourSuccess C σ} ≤
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
theorem exists_pair_printed_joint_colour_family_paper_threshold
    (hn : paperSizeThreshold 2 1 ≤ n) (hh : 4 ≤ h) (hH : h ≤ 48)
    (K : Hypergraph (Fin n) 1)
    (hT : IsTypical K ((n : ℝ) ^ (-(1 / 10 : ℝ))) h)
    (hd : |density K - (n : ℝ) ^ (-paperAlpha 2 1)| ≤
      (n : ℝ) ^ (-(1 / 10 : ℝ)) * (n : ℝ) ^ (-paperAlpha 2 1))
    (C : ModularGeneratingData K (cliqueFamily K 2) N)
    (hgood : ((K \ C.good).card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha 2 1 / 10)) * K.card)
    (hsat : (C.saturated.card : ℝ) ≤
      (n : ℝ) ^ (-(paperAlpha 2 1 / 10)) * (cliqueFamily K 2).card)
    (hcount : ∀ e ∈ C.good,
      |((((cliqueFamily K 2) \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) -
        cliqueMainTerm n (density K) 2 1 1| ≤
          (n : ℝ) ^ (-(paperAlpha 2 1 / 10)) * cliqueMainTerm n (density K) 2 1 1) :
    ∃ σ : Fin (paperColourCount 2 1 pairColourExchange.graph.card) → Equiv.Perm (Fin n),
      PairPrintedColourSuccess C σ := by
  classical
  let : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤
  have hb := pair_printed_joint_colour_failure_paper_threshold hn hh hH K hT hd C
    hgood hsat hcount
  have hn1 : (1 : ℝ) < n := by
    exact_mod_cast (paperSizeThreshold_one_lt (show 0 + 1 < 2 by decide)).trans_le hn
  exact IndependentTrials.exists_of_failure_lt_one _
    (hb.trans_lt (Real.rpow_lt_one_of_one_lt_of_neg hn1 (by norm_num)))

end Arxiv2411_18291
