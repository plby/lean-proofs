import Arxiv.Arxiv2411_18291.ExplicitEliminationStages
import Arxiv.Arxiv2411_18291.AbsorberFactorBounds

/-! # Finite cancellation at the normalized multiplicity-16 parameters -/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {W U : Type*} [Fintype W] [Fintype U] [DecidableEq W] [DecidableEq U]
variable {q r n : ℕ}

theorem normalized_elimination_constant_bounds (T : ExchangeSystem U q (r + 1))
    (hqr : r + 1 < q) (hT : T.graph.card ≤ absorberExchangeEdges q (r + 1))
    {A : ℝ} (hA : 0 ≤ A) (hAb : A ≤ 2 * absorberSplittingConstant q (r + 1)) :
    let C := absorberCoefficientCap q (r + 1)
    let M := absorberGeneratorMultiplicity q (r + 1)
    let K₀ := absorberFirstMultiplicity q (r + 1)
    let K₁ := absorberSecondMultiplicity q (r + 1)
    ((q.choose (r + 1) * K₀ : ℕ) : ℝ) * ((K₀ : ℝ) * A) ≤
        (4 * q : ℝ) ^ (24 * q) ∧
      ((q.choose (r + 1) * K₁ : ℕ) : ℝ) *
        ((K₁ : ℝ) * firstEliminationFactor T C M A) ≤ (4 * q : ℝ) ^ (24 * q) ∧
      secondEliminationFactor T C M A ≤ 2 * absorberFinalConstant q (r + 1) := by
  dsimp only
  let C := absorberCoefficientCap q (r + 1)
  let M := absorberGeneratorMultiplicity q (r + 1)
  let K₀ := absorberFirstMultiplicity q (r + 1)
  let K₁ := absorberSecondMultiplicity q (r + 1)
  have hscaled : (K₀ : ℝ) * A ≤ ((K₀ * (2 * absorberSplittingConstant q (r + 1)) : ℕ) : ℝ) := by
    push_cast
    exact mul_le_mul_of_nonneg_left hAb (Nat.cast_nonneg _)
  have hfirst : firstEliminationFactor T C M A ≤ 2 * absorberFirstConstant q (r + 1) := by
    have h := eliminationFactor_le_nat T (absorberExchangeEdges q (r + 1))
      (K₀ * (2 * absorberSplittingConstant q (r + 1))) K₀ hT (by positivity) hscaled
    convert h using 1
    · rfl
    · unfold absorberFirstConstant
      push_cast
      ring
  have hfirst0 : 0 ≤ firstEliminationFactor T C M A := by
    unfold firstEliminationFactor eliminationFactor
    positivity
  have hscaled' : (K₁ : ℝ) * firstEliminationFactor T C M A ≤
      ((K₁ * (2 * absorberFirstConstant q (r + 1)) : ℕ) : ℝ) := by
    push_cast
    exact mul_le_mul_of_nonneg_left hfirst (Nat.cast_nonneg _)
  have hfinal : secondEliminationFactor T C M A ≤ 2 * absorberFinalConstant q (r + 1) := by
    have h := eliminationFactor_le_nat T (absorberExchangeEdges q (r + 1))
      (K₁ * (2 * absorberFirstConstant q (r + 1))) K₁ hT (by positivity) hscaled'
    convert h using 1
    · rfl
    · unfold absorberFinalConstant
      push_cast
      ring
  obtain ⟨hb₀, hb₁⟩ := absorber_elimination_density_constants (Nat.succ_pos r) hqr
  refine ⟨?_, ?_, hfinal⟩
  · have hb : (2 * (q.choose (r + 1) * K₀ ^ 2 *
        absorberSplittingConstant q (r + 1)) : ℝ) ≤ (4 * q : ℝ) ^ (24 * q) := by
      exact_mod_cast hb₀
    calc
      _ ≤ ((q.choose (r + 1) * K₀ : ℕ) : ℝ) *
          ((K₀ : ℝ) * (2 * absorberSplittingConstant q (r + 1))) := by gcongr
      _ = 2 * (q.choose (r + 1) * (K₀ : ℝ) ^ 2 *
          absorberSplittingConstant q (r + 1)) := by push_cast; ring
      _ ≤ _ := hb
  · have hb : (2 * (q.choose (r + 1) * K₁ ^ 2 *
        absorberFirstConstant q (r + 1)) : ℝ) ≤ (4 * q : ℝ) ^ (24 * q) := by
      exact_mod_cast hb₁
    calc
      _ ≤ ((q.choose (r + 1) * K₁ : ℕ) : ℝ) *
          ((K₁ : ℝ) * (2 * absorberFirstConstant q (r + 1))) := by gcongr
      _ = 2 * (q.choose (r + 1) * (K₁ : ℝ) ^ 2 *
          absorberFirstConstant q (r + 1)) := by push_cast; ring
      _ ≤ _ := hb

/-- Once splitting is performed at exponent `alpha/2`, both cancellation
stages and the final `n^(-alpha/4)` host bound hold at the printed threshold.
The factor two includes the original reserve and the generator support. -/
theorem exists_normalized_two_stage_elimination_paper_threshold
    (S : ExchangeSystem W q (r + 1)) {A₀ : Finset (Block W q)}
    (hA₀ : IsExchangeFamily S A₀)
    (T : ExchangeSystem U q (r + 1)) (N : Block U q) (e₀ : Block U (r + 1))
    (hpair : IsEliminationPair T N e₀) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card U ≤ (4 * q) ^ (2 * q))
    (hS : S.graph.card ≤ absorberExchangeEdges q (r + 1))
    (hT : T.graph.card ≤ absorberExchangeEdges q (r + 1))
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (hmult : ∀ f : Block (Fin n) (r + 1), (D.filter fun Q => f.val ⊆ Q.val).card ≤
      absorberGeneratorMultiplicity q (r + 1)) :
    let C := absorberCoefficientCap q (r + 1)
    let M := absorberGeneratorMultiplicity q (r + 1)
    let A := 2 * splittingFactor S C (absorberNormalizationFactor q (r + 1))
    ∀ F : SplittingFamily S D B C (A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))),
      ∃ E : EliminationFamily T N F.graph F.pairPositive F.pairNegative
          (firstEliminationFactor T C M A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))),
        ∃ L : FurtherEliminationPairs F E,
          ∃ G : EliminationFamily T N E.graph L.positive (fun i : E.badNegative => i.val)
              (secondEliminationFactor T C M A * (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))),
            IsDecomposition (cliqueSupport (r + 1) (finalNegative F E L G))
              (finalNegative F E L G) ∧
            Disjoint (cliqueSupport (r + 1) (finalNegative F E L G)) B ∧
            IsGraphBounded (cliqueSupport (r + 1) (finalNegative F E L G))
              ((n : ℝ) ^ (-(paperAlpha q (r + 1) / 4))) := by
  dsimp only
  intro F
  let C := absorberCoefficientCap q (r + 1)
  let M := absorberGeneratorMultiplicity q (r + 1)
  let A := 2 * splittingFactor S C (absorberNormalizationFactor q (r + 1))
  have hA : 1 ≤ A := by
    have hh := one_le_splittingFactor S C
      (by exact_mod_cast absorberNormalizationFactor_pos q (r + 1) :
        (1 : ℝ) ≤ absorberNormalizationFactor q (r + 1))
    dsimp only [A]
    linarith only [hh]
  have hA0 : 0 ≤ A := le_trans zero_le_one hA
  have hAb : A ≤ 2 * absorberSplittingConstant q (r + 1) :=
    mul_le_mul_of_nonneg_left (splittingFactor_le_absorberSplittingConstant S hS) (by norm_num)
  obtain ⟨hc₀, hc₁, hfinal⟩ := normalized_elimination_constant_bounds T hqr hT hA0 hAb
  have hα := paperAlpha_pos hqr
  have hαupper := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  obtain ⟨E, L, G, hdecomp, hdis, hbound⟩ := exists_two_stage_elimination_paper_threshold
    S hA₀ T N e₀ hpair hqr hn hw
    (hT.trans (paper_exchange_graph_bound (Nat.succ_pos r) hqr)) C M hA hc₀ hc₁
    (by linarith only [hα]) (by linarith only [hαupper]) D B F hmult
  refine ⟨E, L, G, hdecomp, hdis, hbound.mono ?_⟩
  exact (mul_le_mul_of_nonneg_right hfinal (Real.rpow_nonneg (Nat.cast_nonneg n) _)).trans
    (absorber_final_density_paper_threshold (Nat.succ_pos r) hqr hn)

end Arxiv2411_18291
