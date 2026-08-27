import Arxiv.Arxiv2411_18291.AbsorberCoefficientBounds
import Arxiv.Arxiv2411_18291.SparseSignedAbsorber
import Arxiv.Arxiv2411_18291.PaperAlphaGrowth

/-! # Constant bounds for the actual embedded absorber configurations -/

noncomputable section

namespace Arxiv2411_18291

variable {W U : Type*} [Fintype W] [Fintype U] [DecidableEq W] [DecidableEq U]
variable {q r : ℕ}

theorem eliminationFactor_le_nat (T : ExchangeSystem U q (r + 1)) (e a M : ℕ)
    (hT : T.graph.card ≤ e) {A : ℝ} (hA : 0 ≤ A) (hAa : A ≤ a) :
    eliminationFactor T M A ≤
      ((a * (1 + 8 * e * (r + 1).factorial * q.choose (r + 1) * M) : ℕ) : ℝ) := by
  have he : (T.graph.card : ℝ) ≤ e := by exact_mod_cast hT
  have heq : ((a * (1 + 8 * e * (r + 1).factorial * q.choose (r + 1) * M) : ℕ) : ℝ) =
      (a : ℝ) + e * (8 * (r + 1).factorial *
        (((q.choose (r + 1) * M : ℕ) : ℝ) * a)) := by push_cast; ring
  rw [heq, eliminationFactor]
  exact add_le_add hAa (mul_le_mul he
    (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hAa (Nat.cast_nonneg _)) (by positivity))
    (by positivity) (Nat.cast_nonneg _))

theorem splittingFactor_le_absorberSplittingConstant (S : ExchangeSystem W q (r + 1))
    (hS : S.graph.card ≤ absorberExchangeEdges q (r + 1)) :
    splittingFactor S (absorberCoefficientCap q (r + 1))
      (absorberNormalizationFactor q (r + 1)) ≤ absorberSplittingConstant q (r + 1) := by
  let C := absorberCoefficientCap q (r + 1)
  let A := absorberNormalizationFactor q (r + 1)
  have he : (S.graph.card : ℝ) ≤ absorberExchangeEdges q (r + 1) := by exact_mod_cast hS
  calc
    _ = (A : ℝ) * (1 + 16 * S.graph.card * (r + 1).factorial * C) := by
      unfold splittingFactor
      push_cast
      ring
    _ ≤ (A : ℝ) * (1 + 16 * absorberExchangeEdges q (r + 1) * (r + 1).factorial * C) := by
      gcongr
    _ = _ := by unfold absorberSplittingConstant; push_cast; rfl

theorem firstEliminationFactor_le_absorberFirstConstant
    (S : ExchangeSystem W q (r + 1)) (T : ExchangeSystem U q (r + 1))
    (hS : S.graph.card ≤ absorberExchangeEdges q (r + 1))
    (hT : T.graph.card ≤ absorberExchangeEdges q (r + 1)) :
    firstEliminationFactor T (absorberCoefficientCap q (r + 1))
      (absorberGeneratorMultiplicity q (r + 1))
      (splittingFactor S (absorberCoefficientCap q (r + 1))
        (absorberNormalizationFactor q (r + 1))) ≤ absorberFirstConstant q (r + 1) := by
  have hs := splittingFactor_le_absorberSplittingConstant S hS
  have hs0 : 0 ≤ splittingFactor S (absorberCoefficientCap q (r + 1))
      (absorberNormalizationFactor q (r + 1)) := by unfold splittingFactor; positivity
  apply eliminationFactor_le_nat T (absorberExchangeEdges q (r + 1))
    (absorberFirstMultiplicity q (r + 1) * absorberSplittingConstant q (r + 1))
    (absorberFirstMultiplicity q (r + 1)) hT (by positivity)
  rw [Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)

theorem secondEliminationFactor_le_absorberFinalConstant
    (S : ExchangeSystem W q (r + 1)) (T : ExchangeSystem U q (r + 1))
    (hS : S.graph.card ≤ absorberExchangeEdges q (r + 1))
    (hT : T.graph.card ≤ absorberExchangeEdges q (r + 1)) :
    secondEliminationFactor T (absorberCoefficientCap q (r + 1))
      (absorberGeneratorMultiplicity q (r + 1))
      (splittingFactor S (absorberCoefficientCap q (r + 1))
        (absorberNormalizationFactor q (r + 1))) ≤ absorberFinalConstant q (r + 1) := by
  have hs := firstEliminationFactor_le_absorberFirstConstant S T hS hT
  have hs0 : 0 ≤ splittingFactor S (absorberCoefficientCap q (r + 1))
      (absorberNormalizationFactor q (r + 1)) := by unfold splittingFactor; positivity
  have hf0 : 0 ≤ firstEliminationFactor T (absorberCoefficientCap q (r + 1))
      (absorberGeneratorMultiplicity q (r + 1))
      (splittingFactor S (absorberCoefficientCap q (r + 1))
        (absorberNormalizationFactor q (r + 1))) := by
    unfold firstEliminationFactor eliminationFactor
    positivity
  apply eliminationFactor_le_nat T (absorberExchangeEdges q (r + 1))
    (absorberSecondMultiplicity q (r + 1) * absorberFirstConstant q (r + 1))
    (absorberSecondMultiplicity q (r + 1)) hT (by positivity)
  rw [Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg _)

/-- The factor from adjoining a sparse generator support is included in the
final density estimate; no further unspecified threshold is required. -/
theorem absorber_final_density_paper_threshold {q r n : ℕ}
    (hr : 1 ≤ r) (hqr : r < q) (hn : paperSizeThreshold q r ≤ n) :
    (2 * absorberFinalConstant q r : ℝ) * (n : ℝ) ^ (-(paperAlpha q r / 2)) ≤
      (n : ℝ) ^ (-(paperAlpha q r / 4)) := by
  have hn0 : (0 : ℝ) < n := by
    exact_mod_cast Nat.zero_lt_one.trans ((paperSizeThreshold_one_lt hqr).trans_le hn)
  have hq : (2 : ℝ) ≤ q := by exact_mod_cast (show 2 ≤ q by omega)
  have hbound : (2 * absorberFinalConstant q r : ℝ) ≤ (4 * q : ℝ) ^ (22 * q + 1) := by
    exact_mod_cast twice_absorber_final_constant_le hr hqr
  have hgrowth : (4 * q : ℝ) ^ (22 * q + 1) ≤ (n : ℝ) ^ (paperAlpha q r / 4) := by
    have h := paper_threshold_alpha_rpow_lower hqr hn (s := 22 * q + 1)
      (t := (1 / 4 : ℝ)) (by norm_num) (by push_cast; nlinarith only [hq])
    convert h using 1
    congr 1
    ring
  calc
    _ ≤ (n : ℝ) ^ (paperAlpha q r / 4) * (n : ℝ) ^ (-(paperAlpha q r / 2)) :=
      mul_le_mul_of_nonneg_right (hbound.trans hgrowth) (Real.rpow_nonneg hn0.le _)
    _ = _ := by rw [← Real.rpow_add hn0]; congr 1; ring

end Arxiv2411_18291
