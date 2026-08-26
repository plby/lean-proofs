import ErdosProblems.Erdos747.StandardStructuralBounds

open Filter Real
open scoped BigOperators Topology

namespace Erdos747

noncomputable section

def levelFailureBound (n : ℕ) : ℝ :=
  Real.exp (-12 * Real.log ((3 * n : ℕ) : ℝ)) + structuralFailureBound n

lemma levelFailureBound_nonneg (n : ℕ) : 0 ≤ levelFailureBound n :=
  add_nonneg (Real.exp_pos _).le (structuralFailureBound_nonneg n)

lemma predecessor_exp_log_le (n : ℕ) (kappa : ℝ) (hn : 2 ≤ n) (hkappa : 0 ≤ kappa) :
    Real.exp (-kappa * Real.log ((3 * (n - 1) : ℕ) : ℝ)) ≤
      Real.exp (kappa * Real.log 2) * Real.exp (-kappa * Real.log ((3 * n : ℕ) : ℝ)) := by
  have hN : (0 : ℝ) < ((3 * n : ℕ) : ℝ) := by exact_mod_cast (show 0 < 3 * n by omega)
  have hpred : (0 : ℝ) < ((3 * (n - 1) : ℕ) : ℝ) := by exact_mod_cast (show 0 < 3 * (n - 1) by omega)
  have hcomp : ((3 * n : ℕ) : ℝ) ≤ 2 * ((3 * (n - 1) : ℕ) : ℝ) := by
    exact_mod_cast (show 3 * n ≤ 2 * (3 * (n - 1)) by omega)
  have hlog := Real.log_le_log hN hcomp
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) hpred.ne'] at hlog
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := mul_le_mul_of_nonneg_left hlog hkappa
  nlinarith only [h]

lemma all_levels_failure_bound_tendsto_zero :
    Tendsto (fun n ↦ ((allEdges n).card + 1 : ℝ) * levelFailureBound n) atTop (𝓝 0) := by
  have h1 := allEdges_polynomial_exp_log_tendsto_zero 0 1 12 (by norm_num)
  have h2 := allEdges_polynomial_exp_log_tendsto_zero 0 1 41 (by norm_num)
  have h3 := allEdges_polynomial_exp_log_tendsto_zero 0 2 41 (by norm_num)
  have h4 := allEdges_polynomial_exp_log_tendsto_zero 1 2 32 (by norm_num)
  simp only [pow_zero, one_mul, pow_one] at h1 h2 h3 h4
  have hlim := ((h1.add (h2.const_mul 4)).add (h3.const_mul (4 * Real.exp (41 * Real.log 2)))).add
    (h4.const_mul 3)
  norm_num only [mul_zero, add_zero] at hlim
  apply squeeze_zero' (Eventually.of_forall fun n ↦ mul_nonneg (by positivity) (levelFailureBound_nonneg n)) _ hlim
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hp := predecessor_exp_log_le n 41 hn (by norm_num)
  have hK : (0 : ℝ) ≤ (allEdges n).card := by positivity
  have hK1 : ((allEdges n).card : ℝ) ≤ (allEdges n).card + 1 := by linarith only [hK]
  have hres : ((allEdges n).card + 1 : ℝ) * ((allEdges n).card *
      (4 * Real.exp (-41 * Real.log ((3 * (n - 1) : ℕ) : ℝ)))) ≤
      4 * Real.exp (41 * Real.log 2) * (((allEdges n).card + 1 : ℝ)^2 *
        Real.exp (-41 * Real.log ((3 * n : ℕ) : ℝ))) := by
    calc
      _ ≤ ((allEdges n).card + 1 : ℝ) * (((allEdges n).card + 1 : ℝ) *
          (4 * (Real.exp (41 * Real.log 2) * Real.exp (-41 * Real.log ((3 * n : ℕ) : ℝ))))) := by
        gcongr
      _ = _ := by ring
  have hcoord : ((allEdges n).card + 1 : ℝ) *
      ((3 : ℝ) * (allEdges n).card * ((3 * n : ℕ) : ℝ) * Real.exp (-32 * Real.log ((3 * n : ℕ) : ℝ))) ≤
      3 * ((3 * n : ℝ) * ((allEdges n).card + 1 : ℝ)^2 * Real.exp (-32 * Real.log ((3 * n : ℕ) : ℝ))) := by
    calc
      _ ≤ ((allEdges n).card + 1 : ℝ) *
          ((3 : ℝ) * ((allEdges n).card + 1 : ℝ) * ((3 * n : ℕ) : ℝ) *
            Real.exp (-32 * Real.log ((3 * n : ℕ) : ℝ))) := by gcongr
      _ = _ := by norm_num only [Nat.cast_mul, Nat.cast_ofNat]; ring
  dsimp only [levelFailureBound, structuralFailureBound]
  nlinarith only [hres, hcoord]

lemma deletion_levels_failure_bound_tendsto_zero (M : ℕ → ℕ) :
    Tendsto (fun n ↦ (((allEdges n).card - M n + 1 : ℕ) : ℝ) * levelFailureBound n)
      atTop (𝓝 0) := by
  apply squeeze_zero (fun n ↦ mul_nonneg (by positivity) (levelFailureBound_nonneg n)) _
    all_levels_failure_bound_tendsto_zero
  intro n
  apply mul_le_mul_of_nonneg_right _ (levelFailureBound_nonneg n)
  exact_mod_cast (show (allEdges n).card - M n + 1 ≤ (allEdges n).card + 1 by omega)

end

end Erdos747
