import ErdosProblems.Erdos1148.RealDirichletValue
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Uniform convergence and continuity for real Dirichlet-series values -/

namespace Erdos1148.DukeArithmetic

open Filter Topology

theorem realDirichletPartialSum_continuous {q : ℕ} (χ : DirichletCharacter ℝ q) (n : ℕ) :
    Continuous (fun s => realDirichletPartialSum χ s n) := by
  unfold realDirichletPartialSum
  apply continuous_finsetSum
  intro k hk
  exact ((Real.continuous_const_rpow (by positivity : ((k + 1 : ℕ) : ℝ) ≠ 0)).comp
    continuous_neg).mul_const _

theorem realDirichletPartialSum_tendstoUniformlyOn {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {σ : ℝ} (hσ : 0 < σ) :
    TendstoUniformlyOn (fun n s => realDirichletPartialSum χ s n)
      (realDirichletValue χ) atTop (Set.Ici σ) := by
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have hzero : Tendsto (fun n : ℕ => (2 : ℝ) * q * ((n + 1 : ℕ) : ℝ) ^ (-σ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, Function.comp_apply] using ((tendsto_rpow_neg_atTop hσ).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))).const_mul ((2 : ℝ) * q)
  filter_upwards [hzero.eventually (gt_mem_nhds hε)] with n hn s hs
  have hpow : ((n + 1 : ℕ) : ℝ) ^ (-s) ≤ ((n + 1 : ℕ) : ℝ) ^ (-σ) := by
    apply Real.rpow_le_rpow_of_exponent_le
    · exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
    · exact neg_le_neg hs
  have hb := (realDirichletValue_sub_partialSum_norm_le χ hχ (hσ.trans_le hs) n).trans
    (mul_le_mul_of_nonneg_left hpow (by positivity))
  simpa only [dist_eq_norm] using hb.trans_lt hn

theorem realDirichletValue_continuousAt {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 0 < s) :
    ContinuousAt (realDirichletValue χ) s := by
  have hcont := (realDirichletPartialSum_tendstoUniformlyOn χ hχ (half_pos hs)).continuousOn
    (Frequently.of_forall (fun n => (realDirichletPartialSum_continuous χ n).continuousOn))
  exact hcont.continuousAt (Ici_mem_nhds (by linarith : s / 2 < s))

end Erdos1148.DukeArithmetic
