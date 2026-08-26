/- Adapted from the checked repository proof in Erdos1148/DirichletWeightedSums.lean. -/
import ErdosProblems.Erdos941.WeightedPartialSums
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Normed

/-! # Real Dirichlet series: weighted tails and ordered convergence -/

namespace Erdos941.Analytic

open Filter Topology

theorem dirichlet_norm_sum_Ico_rpow_le {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {a b : ℕ} (ha : 0 < a)
    {s : ℝ} (hs : 0 ≤ s) :
    ‖∑ k ∈ Finset.Ico a b, (k : ℝ) ^ (-s) * χ k‖ ≤ 2 * q * (a : ℝ) ^ (-s) := by
  let f : ℕ → ℝ := fun i => ((a + i : ℕ) : ℝ) ^ (-s)
  let z : ℕ → ℝ := fun i => χ (a + i)
  have hf : Antitone f := by
    intro i j hij
    apply Real.rpow_le_rpow_of_nonpos
    · exact_mod_cast (Nat.add_pos_left ha i)
    · exact_mod_cast Nat.add_le_add_left hij a
    · exact neg_nonpos.mpr hs
  have hz : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ (2 : ℝ) * q := by
    intro n
    have h := dirichlet_norm_sum_Ico_le χ hχ a (a + n)
    simpa only [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left, z, Nat.cast_add] using h
  have h := norm_sum_range_smul_le_of_antitone f z hf
    (fun n => Real.rpow_nonneg (Nat.cast_nonneg _) _) hz (b - a)
  simpa only [Finset.sum_Ico_eq_sum_range, f, z, smul_eq_mul, Nat.add_zero, Nat.cast_add,
    Nat.cast_zero, add_zero] using h

theorem dirichlet_real_series_converges {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℝ q) (hχ : χ ≠ 1) {s : ℝ} (hs : 0 < s) :
    ∃ L : ℝ, Tendsto
      (fun n => ∑ k ∈ Finset.range n, ((k + 1 : ℕ) : ℝ) ^ (-s) * χ (k + 1))
      atTop (𝓝 L) := by
  let f : ℕ → ℝ := fun i => ((i + 1 : ℕ) : ℝ) ^ (-s)
  let z : ℕ → ℝ := fun i => χ (i + 1)
  have hf : Antitone f := by
    intro i j hij
    apply Real.rpow_le_rpow_of_nonpos
    · positivity
    · exact_mod_cast Nat.add_le_add_right hij 1
    · exact neg_nonpos.mpr hs.le
  have hfzero : Tendsto f atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hs).comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hz : ∀ n, ‖∑ i ∈ Finset.range n, z i‖ ≤ (2 : ℝ) * q := by
    intro n
    have h := dirichlet_norm_sum_Ico_le χ hχ 1 (1 + n)
    simpa [z, Finset.sum_Ico_eq_sum_range, Nat.add_comm] using h
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete
    (hf.cauchySeq_series_mul_of_tendsto_zero_of_bounded hfzero hz)
  exact ⟨L, by simpa only [smul_eq_mul] using hL⟩

end Erdos941.Analytic
