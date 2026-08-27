import Arxiv.Arxiv2411_18291.CappedSplittingNumerics
import Arxiv.Arxiv2411_18291.VariableSplittingOutput
import Arxiv.Arxiv2411_18291.IntegralGeneratorSupportAtThreshold
import Arxiv.Arxiv2411_18291.CappedIntegralGeneratorsAtThreshold

/-! # One fixed splitting family with a growing edge cap at n0

The decoder regions, capacities, and signed splitting family are chosen
before the leave. Their edge multiplicity grows by only a fixed decoder
coefficient, so the constructed cap is n^(7*alpha/60).
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_constructed_capped_variable_splitting_output {q r n : ℕ}
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
            ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))),
          IsCliqueFamilyBounded r F.cliques ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 10))) ∧
          (∀ e : Block (Fin n) (r + 1),
            ((F.cliques.filter fun Q => e.val ⊆ Q.val).card : ℝ) ≤
              (n : ℝ) ^ (7 * paperAlpha q (r + 1) / 60)) ∧
          ∀ L : Hypergraph (Fin n) (r + 1), L ⊆ B → GeneratedBy D (indicator L) →
            ∃ P N : Finset (Block (Fin n) q),
              P ⊆ F.positiveCliques ∧ N ⊆ F.negativeCliques ∧ Disjoint P N ∧
              boundary (r + 1) (indicator P - indicator N) = indicator L ∧
              Nonempty (VariableNearMatching F P N) := by
  obtain ⟨T, A, hA, hcross, hlocal, Z, hZ, F, hF, hout⟩ :=
    exists_constructed_variable_splitting_output hqr hn D B hDB hD hB
  refine ⟨T, A, hA, hcross, hlocal, Z, hZ, F, hF, ?_, hout⟩
  intro e
  exact (F.decoder_clique_multiplicity hqr.le D hZ (by positivity) hcap e).trans
    (decoder_splitting_cap_paper_threshold hqr hn)

theorem exists_unconditional_capped_variable_splitting_paper_threshold {q r n : ℕ}
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
              ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 3))),
            IsCliqueFamilyBounded r F.cliques
              ((n : ℝ) ^ (-(3 * paperAlpha q (r + 1) / 10))) ∧
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
    exists_constructed_capped_variable_splitting_output hqr hn D (B ∪ cliqueSupport (r + 1) D)
      subset_union_right hD hsupport hcap
  refine ⟨D, hD, hsupport, T, A, hA, hcross, hlocal, Z, hZ, F, hF, hFcap, ?_⟩
  intro L hLB hInt
  apply hout L (hLB.trans subset_union_left)
  exact hgen (indicator L)
    (fun e he => indicator_apply_of_notMem (fun heL => he (hLB heL))) hInt

end Arxiv2411_18291
