import Arxiv.Arxiv2411_18291.CappedWeightedDecoderAtThreshold
import Arxiv.Arxiv2411_18291.SharpVariableSplittingNumerics
import Arxiv.Arxiv2411_18291.CappedVariableSplitting

/-! # Fixed capped splitting with enough degree margin for cancellation

The constant-deviation decoders have capacity density n^(-17*alpha/30).
Splitting gives graph density n^(-alpha/2) and clique-boundary density
n^(-89*alpha/180), retaining edge multiplicity n^(7*alpha/60).
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_sharp_variable_splitting_paper_threshold
    {W : Type*} [Fintype W] [DecidableEq W] {q r n : ℕ}
    (S : ExchangeSystem W q (r + 1)) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q)) (hS : S.graph.card ≤ (4 * q) ^ (2 * q))
    (D : Finset (Block (Fin n) q)) (C : Block (Fin n) q → ℕ)
    (B : Hypergraph (Fin n) (r + 1))
    (hD : IsCliqueCapacityBounded r D C ((n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 30))))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-(17 * paperAlpha q (r + 1) / 30))))
    (hDB : cliqueSupport (r + 1) D ⊆ B) :
    Nonempty (VariableSplittingFamily S D B C ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 2)))) := by
  have hα := paperAlpha_pos hqr
  have hαmax := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  obtain ⟨d, hconflict, hnpos, hsize, hfree, hsmall, hfailure⟩ :=
    variable_splitting_finite_conditions_at_exponent hqr hn hw hS
      (s := 17 * paperAlpha q (r + 1) / 30)
      (by linarith only [hα]) (by linarith only [hαmax])
  obtain ⟨F⟩ := exists_variable_splitting_family S hqr.le D C B (by positivity) hD hB hDB d
    (by simpa only [Fintype.card_fin] using hconflict)
    (by simpa only [Fintype.card_fin] using hnpos)
    (by simpa only [Fintype.card_fin] using hsize)
    (by simpa only [Fintype.card_fin] using hfree) hsmall
    (by simpa only [Block, Fintype.card_finset_len, Fintype.card_fin] using hfailure)
  exact ⟨{ F with bounded := F.bounded.mono (sharp_variable_splitting_output_density hqr hn hS) }⟩

theorem exists_constructed_sharp_capped_variable_splitting_output {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (hDB : cliqueSupport (r + 1) D ⊆ B)
    (hD : IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))))
    (hcap : ∀ e : Block (Fin n) (r + 1),
      ((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
        (n : ℝ) ^ (paperAlpha q (r + 1) / 10)) :
    ∃ T : FiniteExchangeSystem q (r + 1), ∃ A : Finset (Block T.Vertex q),
      IsExchangeFamily T.system A ∧ IsCrossSimple (r + 1) T.system.positive T.system.negative ∧
      IsPositiveFrameLocal T.system A ∧
      ∃ Z : B → Block (Fin n) (q + (r + 1)),
        IsCliqueCover (complete (Fin n) (r + 1) \ B) (fun e : B => e.val) Z ∧
        ∃ F : VariableSplittingFamily T.system (D ∪ cliqueRefinement q (univ.image Z))
            (cliqueCoverGraph (r := r) Z) (edgewiseDecoderCapacity D Z)
            ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))),
          IsCliqueFamilyBounded r F.cliques ((n : ℝ) ^ (-(89 * paperAlpha q (r + 1) / 180))) ∧
          (∀ e : Block (Fin n) (r + 1),
            ((F.cliques.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
              (n : ℝ) ^ (7 * paperAlpha q (r + 1) / 60)) ∧
          ∀ L : Hypergraph (Fin n) (r + 1), L ⊆ B → GeneratedBy D (indicator L) →
            ∃ P N : Finset (Block (Fin n) q),
              P ⊆ F.positiveCliques ∧ N ⊆ F.negativeCliques ∧ Disjoint P N ∧
              boundary (r + 1) (indicator P - indicator N) = indicator L ∧
              Nonempty (VariableNearMatching F P N) := by
  classical
  obtain ⟨T, A, hsize, hA, hcross, hlocal, hw⟩ :=
    exists_small_carrier_clique_exchange q (r + 1) (Nat.succ_pos r) hqr
  obtain ⟨Z, hZ, hgraph, hcapacity⟩ :=
    exists_capped_weighted_decoder_paper_threshold hqr hn D B hD hB hcap
  obtain ⟨F⟩ := exists_sharp_variable_splitting_paper_threshold T.system hqr hn hw
    (hsize.trans (paper_exchange_graph_bound (Nat.succ_pos r) hqr))
    (D ∪ cliqueRefinement q (univ.image Z)) (edgewiseDecoderCapacity D Z)
    (cliqueCoverGraph (r := r) Z) hcapacity hgraph (hZ.decoder_support_subset hDB)
  refine ⟨T, A, hA, hcross, hlocal, Z, hZ, F,
    (F.cliques_bounded hcapacity).mono (sharp_variable_splitting_clique_density hqr hn), ?_, ?_⟩
  · intro e
    exact (F.decoder_clique_multiplicity hqr.le D hZ (by positivity) hcap e).trans
      (decoder_splitting_cap_paper_threshold hqr hn)
  intro L hLB hgen
  obtain ⟨Φ, hΦ, hs, hcap⟩ :=
    edgewise_representation_of_local_decoders hqr D B L hDB hLB Z hZ hgen
  obtain ⟨P, N, hP, hN, hdis, hb⟩ := F.signed_representation_with_signs hqr.le Φ hcap hs
  have hboundary := hb.trans hΦ
  refine ⟨P, N, hP, hN, hdis, hboundary, F.exists_nearMatching hA P N hP hN ?_⟩
  intro e _
  rw [hboundary]
  unfold indicator
  split_ifs <;> norm_num

theorem exists_unconditional_sharp_capped_variable_splitting_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hq : 3 ≤ q) (hn : paperSizeThreshold q (r + 1) ≤ n)
    (B : Hypergraph (Fin n) (r + 1))
    (hB : IsGraphBounded B ((n : ℝ) ^ (-paperRho q (r + 1)))) :
    ∃ D : Finset (Block (Fin n) q),
      IsCliqueFamilyBounded r D ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))) ∧
      IsGraphBounded (B ∪ cliqueSupport (r + 1) D)
        ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))) ∧
      ∃ T : FiniteExchangeSystem q (r + 1), ∃ A : Finset (Block T.Vertex q),
        IsExchangeFamily T.system A ∧
        IsCrossSimple (r + 1) T.system.positive T.system.negative ∧
        IsPositiveFrameLocal T.system A ∧
        ∃ Z : ↥(B ∪ cliqueSupport (r + 1) D) → Block (Fin n) (q + (r + 1)),
          IsCliqueCover (complete (Fin n) (r + 1) \ (B ∪ cliqueSupport (r + 1) D))
            (fun e : ↥(B ∪ cliqueSupport (r + 1) D) => e.val) Z ∧
          ∃ F : VariableSplittingFamily T.system (D ∪ cliqueRefinement q (univ.image Z))
              (cliqueCoverGraph (r := r) Z) (edgewiseDecoderCapacity D Z)
              ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))),
            IsCliqueFamilyBounded r F.cliques
              ((n : ℝ) ^ (-(89 * paperAlpha q (r + 1) / 180))) ∧
            (∀ e : Block (Fin n) (r + 1),
              ((F.cliques.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
                (n : ℝ) ^ (7 * paperAlpha q (r + 1) / 60)) ∧
            ∀ L : Hypergraph (Fin n) (r + 1), L ⊆ B →
              IntegrallyDecomposable q (indicator L) →
              ∃ P N : Finset (Block (Fin n) q),
                P ⊆ F.positiveCliques ∧ N ⊆ F.negativeCliques ∧ Disjoint P N ∧
                boundary (r + 1) (indicator P - indicator N) = indicator L ∧
                Nonempty (VariableNearMatching F P N) := by
  obtain ⟨D, hDhalf, hcap, hgen⟩ :=
    exists_capped_integral_generators_paper_threshold hqr hq hn B hB
  have hθ : 0 ≤ (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) := by positivity
  have hD := hDhalf.mono (show (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) / 2 ≤
      (n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5)) by linarith only [hθ])
  have hsupport : IsGraphBounded (B ∪ cliqueSupport (r + 1) D)
      ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 5))) := by
    have hh := (hB.mono (paper_source_half_generator_density hqr hn)).union
      hDhalf.support_graphBounded
    simpa only [add_halves] using hh
  obtain ⟨T, A, hA, hcross, hlocal, Z, hZ, F, hF, hFcap, hout⟩ :=
    exists_constructed_sharp_capped_variable_splitting_output hqr hn D (B ∪ cliqueSupport (r + 1) D)
      subset_union_right hD hsupport hcap
  refine ⟨D, hD, hsupport, T, A, hA, hcross, hlocal, Z, hZ, F, hF, hFcap, ?_⟩
  intro L hLB hInt
  apply hout L (hLB.trans subset_union_left)
  exact hgen (indicator L)
    (fun e he => indicator_apply_of_notMem (fun heL => he (hLB heL))) hInt

end Arxiv2411_18291
