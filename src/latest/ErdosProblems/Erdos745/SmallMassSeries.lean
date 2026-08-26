import ErdosProblems.Erdos745.FixedTreeMean
import ErdosProblems.Erdos745.ComponentExponential
import Mathlib.Analysis.Normed.Group.FunctionSeries

/-! # Continuity of the supercritical small-component mass series -/

open Filter
open scoped BigOperators Topology

namespace Erdos745

noncomputable section

theorem logarithmicDecay_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    logarithmicDecay a ≤ logarithmicDecay b := by
  have ha0 : 0 < a := by linarith
  have hb0 : 0 < b := ha0.trans_le hab
  have hlog := Real.log_le_sub_one_of_pos (div_pos hb0 ha0)
  rw [Real.log_div hb0.ne' ha0.ne'] at hlog
  have hm := mul_le_mul_of_nonneg_left hlog ha0.le
  have he : a * (b / a - 1) = b - a := by field_simp
  rw [he] at hm
  have hld : 0 ≤ Real.log b - Real.log a := sub_nonneg.mpr (Real.log_le_log ha0 hab)
  unfold logarithmicDecay
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) hld]

theorem treeDensity_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (k : ℕ) : 0 ≤ treeDensity lam k := by
  unfold treeDensity
  positivity

theorem treeDensity_le_exp {lam : ℝ} (hlam : 0 < lam) {k : ℕ} (hk : 0 < k) :
    treeDensity lam k ≤ (1 / lam) * Real.exp (-logarithmicDecay lam * k) := by
  have hτ : (labelledTreeCount k : ℝ) / k.factorial ≤ Real.exp k := by
    apply (div_le_div_of_nonneg_right
      (show (labelledTreeCount k : ℝ) ≤ (k : ℝ) ^ k by
        exact_mod_cast labelledTreeCount_upper hk) (by positivity)).trans
    exact Real.pow_div_factorial_le_exp (k : ℝ) (Nat.cast_nonneg _) k
  have hpre := component_prefactor_identity (n := 1) (by omega) hk hlam
  simp only [Nat.cast_one, one_pow, one_mul, div_one] at hpre
  unfold treeDensity
  calc
    _ = ((labelledTreeCount k : ℝ) / k.factorial) * lam ^ (k - 1) * Real.exp (-lam * k) := by ring
    _ ≤ Real.exp k * lam ^ (k - 1) * Real.exp (-lam * k) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hτ (pow_nonneg hlam.le _)) (Real.exp_nonneg _)
    _ = (1 / lam) * Real.exp (((1 + Real.log lam) * k) + (-lam * k)) := by
      rw [hpre, mul_assoc, Real.exp_add]
    _ = _ := by congr 2; unfold logarithmicDecay; ring

def smallMassTerm (lam : ℝ) (k : ℕ) : ℝ := (k : ℝ) * treeDensity lam k

def smallMassLimit (lam : ℝ) : ℝ := ∑' k : ℕ, smallMassTerm lam k

theorem continuous_smallMassTerm (k : ℕ) : Continuous (fun lam ↦ smallMassTerm lam k) := by
  unfold smallMassTerm treeDensity
  fun_prop

theorem smallMassTerm_nonneg {lam : ℝ} (hlam : 0 ≤ lam) (k : ℕ) :
    0 ≤ smallMassTerm lam k := mul_nonneg (Nat.cast_nonneg _) (treeDensity_nonneg hlam k)

theorem smallMassTerm_le {a lam : ℝ} (ha : 1 < a) (halam : a ≤ lam) (k : ℕ) :
    smallMassTerm lam k ≤ (k : ℝ) * Real.exp (-logarithmicDecay a * k) := by
  have hlam1 : 1 ≤ lam := ha.le.trans halam
  have hlam0 : 0 < lam := by linarith
  by_cases hk : k = 0
  · subst k
    simp [smallMassTerm]
  · apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg k)
    apply (treeDensity_le_exp hlam0 (Nat.pos_of_ne_zero hk)).trans
    have hcoeff : 1 / lam ≤ 1 := (div_le_one hlam0).mpr hlam1
    have hdecay := logarithmicDecay_mono ha.le halam
    have hexp : Real.exp (-logarithmicDecay lam * k) ≤ Real.exp (-logarithmicDecay a * k) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (neg_le_neg hdecay) (Nat.cast_nonneg k)
    exact (mul_le_mul hcoeff hexp (Real.exp_nonneg _) (by norm_num)).trans_eq (one_mul _)

theorem summable_geometric_mass {a : ℝ} (ha : 1 < a) :
    Summable (fun k : ℕ ↦ (k : ℝ) * Real.exp (-logarithmicDecay a * k)) := by
  have hdecay := logarithmicDecay_pos (zero_lt_one.trans ha) (ne_of_gt ha)
  have hr : ‖Real.exp (-logarithmicDecay a)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    linarith
  have h := (hasSum_coe_mul_geometric_of_norm_lt_one hr).summable
  convert! h using 1
  funext k
  rw [mul_comm (-logarithmicDecay a), Real.exp_nat_mul]

theorem continuousOn_smallMassLimit {a : ℝ} (ha : 1 < a) :
    ContinuousOn smallMassLimit (Set.Ici a) := by
  apply continuousOn_tsum (fun k ↦ (continuous_smallMassTerm k).continuousOn)
    (summable_geometric_mass ha)
  intro k lam hlam
  rw [Real.norm_eq_abs, abs_of_nonneg
    (smallMassTerm_nonneg (by have := hlam; change a ≤ lam at this; linarith) k)]
  exact smallMassTerm_le ha hlam k

theorem continuousAt_smallMassLimit {lam : ℝ} (hlam : 1 < lam) :
    ContinuousAt smallMassLimit lam := by
  have ha : 1 < (1 + lam) / 2 := by linarith
  apply (continuousOn_smallMassLimit ha).continuousAt
  exact Ici_mem_nhds (by linarith)

theorem summable_smallMassTerm {lam : ℝ} (hlam : 1 < lam) :
    Summable (smallMassTerm lam) := by
  apply (summable_geometric_mass hlam).of_norm_bounded
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (smallMassTerm_nonneg (by linarith) k)]
  exact smallMassTerm_le hlam le_rfl k

theorem tendsto_smallMass_partialSums {lam : ℝ} (hlam : 1 < lam) :
    Tendsto (fun K ↦ ∑ k ∈ Finset.range K, smallMassTerm lam k) atTop (𝓝 (smallMassLimit lam)) :=
  (summable_smallMassTerm hlam).hasSum.tendsto_sum_nat

end

end Erdos745
