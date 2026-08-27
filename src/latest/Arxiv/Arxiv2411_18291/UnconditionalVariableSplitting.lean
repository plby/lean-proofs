import Arxiv.Arxiv2411_18291.IntegralGeneratorSupportAtThreshold
import Arxiv.Arxiv2411_18291.VariableSplittingOutput

/-! # Unconditional variable splitting at the paper's threshold

Starting from the sparse source graph alone, construct the integral
generators, their supporting graph, weighted decoders, exchange pattern,
and one fixed splitting family. Every integrally decomposable leave then
has a signed representation in the fixed families and a near matching.
Cancellation gadgets for all possible leaves are not asserted here.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

theorem exists_unconditional_variable_splitting_paper_threshold {q r n : ℕ}
    (hqr : r + 1 < q) (hn : paperSizeThreshold q (r + 1) ≤ n)
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
            ∀ L : Hypergraph (Fin n) (r + 1), L ⊆ B →
              IntegrallyDecomposable q (indicator L) →
              ∃ P N : Finset (Block (Fin n) q),
                P ⊆ F.positiveCliques ∧ N ⊆ F.negativeCliques ∧ Disjoint P N ∧
                boundary (r + 1) (indicator P - indicator N) = indicator L ∧
                Nonempty (VariableNearMatching F P N) := by
  obtain ⟨D, hD, hsupport, hgen⟩ :=
    exists_paper_integral_generators_with_support hqr hn B hB
  obtain ⟨T, A, hA, hcross, hlocal, Z, hZ, F, hF, hout⟩ :=
    exists_constructed_variable_splitting_output hqr hn D (B ∪ cliqueSupport (r + 1) D)
      subset_union_right hD hsupport
  refine ⟨D, hD, hsupport, T, A, hA, hcross, hlocal, Z, hZ, F, hF, ?_⟩
  intro L hLB hInt
  apply hout L (hLB.trans subset_union_left)
  exact hgen (indicator L)
    (fun e he => indicator_apply_of_notMem (fun heL => he (hLB heL))) hInt

end Arxiv2411_18291
