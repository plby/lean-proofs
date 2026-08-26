import ErdosProblems.Erdos1123.OrdinaryBlocks
import Mathlib.NumberTheory.Harmonic.Bounds

/-! # The logarithmic density ideal as a finite-block null ideal -/

namespace Erdos1123

open Filter
open scoped Topology Classical

def logarithmicCut (n : ℕ) : ℕ := 2 ^ (2 ^ n)

theorem logarithmicCut_strictMono : StrictMono logarithmicCut :=
  dyadicCut_strictMono.comp dyadicCut_strictMono

theorem logarithmicCut_log (n : ℕ) :
    Real.log (logarithmicCut n) = (2 : ℝ) ^ n * Real.log 2 := by
  simp [logarithmicCut, Real.log_pow]

theorem logarithmicCut_log_pos (n : ℕ) : 0 < Real.log (logarithmicCut n) := by
  rw [logarithmicCut_log]
  exact mul_pos (pow_pos (by norm_num) n) (Real.log_pos (by norm_num))

theorem logarithmicCut_double (n : ℕ) :
    Real.log (logarithmicCut (n + 1)) = 2 * Real.log (logarithmicCut n) := by
  rw [logarithmicCut_log, logarithmicCut_log, pow_succ]
  ring

theorem nat_log_monotone : Monotone (fun n : ℕ => Real.log n) := by
  intro n m hnm
  by_cases hn : n = 0
  · subst n
    simpa using Real.log_natCast_nonneg m
  · exact Real.log_le_log (by exact_mod_cast Nat.pos_of_ne_zero hn) (Nat.cast_le.mpr hnm)

theorem nat_log_tendsto_atTop : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
  Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop

theorem nat_inv_nonneg (n : ℕ) : 0 ≤ (n : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg n)

theorem nat_inv_le_one (n : ℕ) : (n : ℝ)⁻¹ ≤ 1 := by
  cases n with
  | zero => norm_num
  | succ n =>
    apply inv_le_one_of_one_le₀
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)

noncomputable def logarithmicBlocks : WeightSequence ℕ :=
  geometricBlocks (fun x => (x : ℝ)⁻¹) (fun n => Real.log n) logarithmicCut
    nat_inv_nonneg Real.log_natCast_nonneg

theorem cumulative_inv_univ (n : ℕ) :
    cumulative (fun x => (x : ℝ)⁻¹) Set.univ n = (harmonic n : ℝ) := by
  simp [cumulative_eq_sum_filter, harmonic_eq_sum_Icc]

theorem log_le_harmonic (n : ℕ) : Real.log n ≤ (harmonic n : ℝ) := by
  simpa using log_le_harmonic_floor (n : ℝ) (Nat.cast_nonneg n)

theorem logarithmicBlocks_mass_bounds (n : ℕ) :
    1 - 1 / Real.log (logarithmicCut n) ≤ logarithmicBlocks.mass Set.univ n ∧
      logarithmicBlocks.mass Set.univ n ≤ 1 + 1 / Real.log (logarithmicCut n) := by
  rw [logarithmicBlocks, geometricBlocks_mass _ _ _ _ _ logarithmicCut_strictMono.monotone]
  rw [cumulative_inv_univ, cumulative_inv_univ]
  have hM₀ := log_le_harmonic (logarithmicCut n)
  have hM₁ := harmonic_le_one_add_log (logarithmicCut n)
  have hN₀ := log_le_harmonic (logarithmicCut (n + 1))
  have hN₁ := harmonic_le_one_add_log (logarithmicCut (n + 1))
  have hdouble := logarithmicCut_double n
  have hpos := logarithmicCut_log_pos n
  constructor
  · apply (le_div_iff₀ hpos).2
    rw [sub_mul, one_mul, div_mul_cancel₀ _ hpos.ne']
    linarith
  · apply (div_le_iff₀ hpos).2
    rw [add_mul, one_mul, div_mul_cancel₀ _ hpos.ne']
    linarith

noncomputable def logarithmicBlockStructure : BlockStructure logarithmicBlocks where
  disjoint := geometricBlocks_disjoint _ _ _ _ _ logarithmicCut_strictMono
  atomBound n := 1 / Real.log (logarithmicCut n)
  atomBound_nonneg n := div_nonneg zero_le_one (logarithmicCut_log_pos n).le
  atomBound_tendsto :=
    (nat_log_tendsto_atTop.comp logarithmicCut_strictMono.tendsto_atTop).const_div_atTop 1
  weight_le n x _ := div_le_div_of_nonneg_right (nat_inv_le_one x) (logarithmicCut_log_pos n).le
  normalized := by
    have hδ := (nat_log_tendsto_atTop.comp logarithmicCut_strictMono.tendsto_atTop).const_div_atTop 1
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (g := fun n => 1 - 1 / Real.log (logarithmicCut n))
      (h := fun n => 1 + 1 / Real.log (logarithmicCut n))
    · simpa only [sub_zero, Function.comp_apply] using (tendsto_const_nhds (x := (1 : ℝ))).sub hδ
    · simpa only [add_zero, Function.comp_apply] using (tendsto_const_nhds (x := (1 : ℝ))).add hδ
    · exact fun n => (logarithmicBlocks_mass_bounds n).1
    · exact fun n => (logarithmicBlocks_mass_bounds n).2

theorem logarithmic_mass_cumulative (A : Set ℕ) (n : ℕ) :
    logarithmicWeights.mass A n = cumulative (fun x => (x : ℝ)⁻¹) A n / Real.log n := by
  rw [logarithmic_mass, cumulative_eq_sum_filter]

theorem logarithmicBlocks_null_iff (A : Set ℕ) :
    logarithmicBlocks.IsNull A ↔ logarithmicWeights.IsNull A := by
  have h := geometricBlocks_null_iff (fun x => (x : ℝ)⁻¹) (fun n => Real.log n) logarithmicCut
    nat_inv_nonneg Real.log_natCast_nonneg logarithmicCut_strictMono nat_log_monotone
    nat_log_tendsto_atTop logarithmicCut_log_pos logarithmicCut_double A
  change logarithmicBlocks.IsNull A ↔ Tendsto (logarithmicWeights.mass A) atTop (𝓝 0)
  rw [funext (logarithmic_mass_cumulative A)]
  exact h

end Erdos1123
