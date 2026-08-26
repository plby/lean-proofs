import ErdosProblems.Erdos747.CoordinateResidualLayerBounds
import ErdosProblems.Erdos747.CoordinateExceptionBounds

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

attribute [local instance] Classical.propDecidable

def standardCodegreeCap (n M : ℕ) : ℕ := relativeCodegreeCap n M (codegreeRelativeTolerance n)

def standardResidualDegreeTolerance (n : ℕ) : ℝ :=
  residualDegreeTolerance n 32 (aggregateDegreeTolerance n) (codegreeRelativeError n)

lemma standardResidualDegreeTolerance_nonneg (n : ℕ) : 0 ≤ standardResidualDegreeTolerance n := by
  have hq := aggregateDegreeTolerance_nonneg n
  have hg : 0 ≤ codegreeRelativeError n := by
    unfold codegreeRelativeError
    have hlog : 0 ≤ Real.log ((3 * n : ℕ) : ℝ) := by
      cases n with
      | zero => simp
      | succ n => exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ 3 * (n + 1) by omega))
    have ht := codegreeRelativeTolerance_nonneg n
    positivity
  unfold standardResidualDegreeTolerance residualDegreeTolerance
  positivity

lemma standardResidualDegreeTolerance_tendsto_zero :
    Tendsto standardResidualDegreeTolerance atTop (𝓝 0) :=
  residualDegreeTolerance_tendsto_zero 32 aggregateDegreeTolerance codegreeRelativeError
    aggregateDegreeTolerance_tendsto_zero codegreeRelativeError_tendsto_zero

lemma standardCodegreeCap_pos (n M : ℕ) (hn : 3 ≤ n) (hM : 0 < M) :
    0 < standardCodegreeCap n M := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlog : 0 < Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have ht : 0 < codegreeRelativeTolerance n := by unfold codegreeRelativeTolerance; positivity
  have hprod : 0 < codegreeRelativeTolerance n * ((M : ℝ) / n) := by positivity
  have hceil := hprod.trans_le (Nat.le_ceil (codegreeRelativeTolerance n * ((M : ℝ) / n)))
  exact_mod_cast hceil

lemma eventually_upper_count_lower_positive (epsilon : ℝ) (C : ℕ → ℝ)
    (hepsilon : 0 ≤ epsilon) (hC : Tendsto C atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ M : ℕ, upperEdgeCount epsilon n ≤ M →
      0 < (n : ℝ) * Real.log ((M : ℝ) / n) - 2 * n - C n * n := by
  have hCsmall := (tendsto_order.mp hC).2 1 (by norm_num : (0 : ℝ) < 1)
  filter_upwards [hCsmall, eventually_upperLayer_log_mean_ge epsilon 4 hepsilon,
    eventually_ge_atTop 1] with n hCn hlog hn
  intro M hM
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfactor : 0 < Real.log ((M : ℝ) / n) - 2 - C n := by linarith only [hlog M hM, hCn]
  nlinarith only [mul_pos hnR hfactor]

lemma eventually_standardAggregateLayer_insertion_and_residual
    (epsilon a c : ℝ) (C : ℕ → ℝ)
    (hepsilon : 0 ≤ epsilon) (ha : 0 < a) (hc : 0 < c) (hC : Tendsto C atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ M : ℕ, upperEdgeCount epsilon n ≤ M →
      ∀ H ∈ sample n M, StandardAggregateLayerRegular n M a H → KahnCountLower H (C n) →
        KahnAggregateInsertionGood n M (standardCodegreeCap n M) (C n)
          (aggregateDegreeTolerance n) (aggregateDegreeTolerance n) 32 H ∧
        ResidualAggregateInheritanceGood n M (coordinateDegreeFloor n M a) (coordinateDegreeCeil n M)
          (standardCodegreeCap n M) c (C n) (residualCountError n (C n) c)
          (standardResidualDegreeTolerance n) (2 * aggregateDegreeTolerance n) 64 H := by
  have hgsmall := (tendsto_order.mp codegreeRelativeError_tendsto_zero).2 (a / 6) (by positivity)
  have hqsmall := (tendsto_order.mp standardResidualDegreeTolerance_tendsto_zero).2 1 (by norm_num : (0 : ℝ) < 1)
  filter_upwards [eventually_upper_count_lower_positive epsilon C hepsilon hC, hgsmall, hqsmall,
    eventually_codegreeRelativeError_pos, log_vertexCount_tendsto_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop 200] with n hpositive hgsmalln hqsmalln hgpos hlog hn
  intro M hM H hHs hreg hcount
  have hpos := hpositive M hM
  have hmean : 1 ≤ (M : ℝ) / n :=
    hlog.trans ((upperEdgeCount_mean_ge epsilon hepsilon n (by omega)).trans
      (div_le_div_of_nonneg_right (by exact_mod_cast hM) (by positivity)))
  have hrelative : (standardCodegreeCap n M : ℝ) / ((M : ℝ) / n) ≤ codegreeRelativeError n :=
    relativeCodegreeCap_ratio_le_error epsilon hepsilon n M (by omega) hM
  have hgood := kahnAggregateInsertionGood_of_aggregateLayerRegular hHs hreg hpos hcount
  have hsize : (6 : ℝ) * (32 + 1) ≤ n := by
    norm_num
    exact_mod_cast (show 198 ≤ n by omega)
  refine ⟨hgood, ?_⟩
  rw [show (64 : ℝ) = 2 * 32 by norm_num]
  apply residualAggregateInheritanceGood_explicit (by omega : 2 ≤ n) hc
    (by norm_num : (0 : ℝ) ≤ 32) (aggregateDegreeTolerance_nonneg n) (aggregateDegreeTolerance_nonneg n)
    hgpos.le hmean hsize hrelative hqsmalln.le hHs hreg hpos hcount
  · exact coordinate_degree_lower_budget n M (standardCodegreeCap n M) a (codegreeRelativeError n)
      ha.le hrelative (lt_of_lt_of_le zero_lt_one hmean) hgsmalln.le
  · exact Nat.le_ceil (32 * ((M : ℝ) / n))

end

end Erdos747
