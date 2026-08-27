import Arxiv.Arxiv2411_18291.SplittingFamilyProbability
import Arxiv.Arxiv2411_18291.HalfAlphaSplitting

/-! # The actual normalized splitting law at exponent alpha/2 -/

noncomputable section

namespace Arxiv2411_18291

theorem splittingFamilyOutputLaw_half_alpha_failure_lt
    {W : Type*} [Fintype W] [DecidableEq W] {q r n : ℕ}
    (S : ExchangeSystem W q (r + 1)) (hqr : r + 1 < q)
    (hn : paperSizeThreshold q (r + 1) ≤ n)
    (hw : Fintype.card W ≤ (4 * q) ^ (2 * q))
    (hS : S.graph.card ≤ 3 * (2 * q) ^ (r + 1) * (q.choose (r + 1)) ^ 2)
    (D : Finset (Block (Fin n) q)) (B : Hypergraph (Fin n) (r + 1))
    (hD : IsCliqueFamilyBounded r D (2 * absorberNormalizationFactor q (r + 1) *
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))))
    (hB : IsGraphBounded B (2 * absorberNormalizationFactor q (r + 1) *
      (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))))
    (hDB : cliqueSupport (r + 1) D ⊆ B)
    (hmult : ∀ e : Block (Fin n) (r + 1),
      (D.filter fun P => e.val ⊆ P.val).card ≤ absorberGeneratorMultiplicity q (r + 1))
    (Q₀ : Block (Fin n) q) :
    (splittingFamilyOutputLaw S D B (absorberCoefficientCap q (r + 1)) Q₀
      (2 * splittingFactor S (absorberCoefficientCap q (r + 1))
        (absorberNormalizationFactor q (r + 1)) *
          (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))) none).toReal <
            Real.exp (-((n : ℝ) ^ (2 / 5 : ℝ))) := by
  let C := absorberCoefficientCap q (r + 1)
  let A : ℝ := absorberNormalizationFactor q (r + 1)
  let x := (n : ℝ) ^ (-(paperAlpha q (r + 1) / 2))
  have hA1 : 1 ≤ A := by
    dsimp only [A]
    exact_mod_cast absorberNormalizationFactor_pos q (r + 1)
  have hA : 1 ≤ 2 * A := by linarith only [hA1]
  have hAb0 : 4 * (C : ℝ) * A ≤ (4 * q : ℝ) ^ (8 * q) := by
    dsimp only [C, A]
    exact_mod_cast absorber_splitting_density_constant (Nat.succ_pos r) hqr
  have hAb : 2 * (C : ℝ) * (2 * A) ≤ (4 * q : ℝ) ^ (24 * q) := by
    calc
      _ = 4 * (C : ℝ) * A := by ring
      _ ≤ (4 * q : ℝ) ^ (8 * q) := hAb0
      _ ≤ _ := pow_le_pow_right₀
        (by exact_mod_cast (show 1 ≤ 4 * q by omega)) (by omega)
  have hα := paperAlpha_pos hqr
  have hαupper := (paperAlpha_le_rho hqr).trans (paperRho_le_one_div_36 hqr)
  have hF := splitting_family_output_probability_at_exponent S hqr hn hw
    (hS.trans (paper_exchange_graph_bound (Nat.succ_pos r) hqr)) C
    (absorberGeneratorMultiplicity q (r + 1)) (absorberCoefficientCap_pos _ _)
    (absorber_splitting_conflict_constant (Nat.succ_pos r) hqr) hA hAb
    (by linarith only [hα]) (by linarith only [hαupper]) D B hD hB hDB hmult Q₀
  change (splittingFamilyOutputLaw S D B C Q₀ (2 * splittingFactor S C A * x)
    none).toReal < _
  have heq : 2 * splittingFactor S C A * x = (2 * A) * x + S.graph.card *
      (8 * (r + 1).factorial * (((2 * C : ℕ) : ℝ) * (2 * A) * x)) := by
    unfold splittingFactor
    ring
  rw [heq]
  rw [splittingFamilyOutputLaw_failure_real]
  linarith only [hF]

end Arxiv2411_18291
