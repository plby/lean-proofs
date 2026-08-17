/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos294.SharpDensity
import ErdosProblems.Erdos297.FiniteHoeffding

/-! # Off-lattice tail for the constant-width good set -/

open Filter Finset Real
open scoped BigOperators Topology

namespace Erdos294.SharpTail

open Erdos297 Erdos297.FiniteHoeffding Erdos297.GoodFactorization
open Erdos294.SharpParameters Erdos294.SharpSupply

noncomputable section

attribute [local instance] Classical.propDecidable

lemma eventually_sharp_hoeffding_scale :
    ∀ᶠ N : ℕ in atTop,
      (24 : ℝ) * (N : ℝ) * (sharpS N : ℝ) ≤ (sharpM N : ℝ) ^ 2 := by
  filter_upwards [eventually_sharpS_le_KSafe, eventually_nat_KSafe_upper,
      eventually_pos_scales, eventually_ge_atTop (200 : ℕ)]
      with N hSK hK hpos hN
  have hL : 0 < logScale N := zero_lt_one.trans hpos.2.1
  have hSupper : (sharpS N : ℝ) ≤ (N : ℝ) / (10 : ℝ) ^ 7 := by
    calc
      (sharpS N : ℝ) ≤ (KSafe N : ℝ) := by exact_mod_cast hSK
      _ ≤ (N : ℝ) / ((10 : ℝ) ^ 7 * logScale N) := hK
      _ ≤ (N : ℝ) / (10 : ℝ) ^ 7 := by
        apply div_le_div_of_nonneg_left (Nat.cast_nonneg _)
        · positivity
        · nlinarith [hpos.2.1]
  have hMlowerNat : N ≤ 200 * sharpM N := by simp [sharpM]; omega
  have hMlower : (N : ℝ) / 200 ≤ (sharpM N : ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 200)]
    exact_mod_cast (by simpa [Nat.mul_comm] using hMlowerNat)
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hleft : (24 : ℝ) * N * sharpS N ≤
      24 * N * (N / (10 : ℝ) ^ 7) := by gcongr
  have hright : ((N : ℝ) / 200) ^ 2 ≤ (sharpM N : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hMlower 2
  exact hleft.trans (by
    apply (show (24 : ℝ) * N * (N / (10 : ℝ) ^ 7) ≤
        (N / 200) ^ 2 by
      field_simp
      nlinarith [sq_nonneg (N : ℝ)]) |>.trans hright)

theorem eventually_tail_bound :
    ∀ᶠ N : ℕ in atTop, ∀ (I : Finset ℕ) (p : ℕ → ℝ),
      I ⊆ Icc (sharpM N) N →
      (∀ n ∈ I, 0 ≤ p n) → (∀ n ∈ I, p n ≤ 1) →
      Erdos297.FiniteHoeffding.eventMass I p (fun B ↦
        1 ≤ |Erdos297.FiniteHoeffding.subsetSum B
              (fun n : ℕ ↦ ((n : ℝ)⁻¹)) -
          Erdos297.FiniteHoeffding.subsetMean I p
              (fun n : ℕ ↦ ((n : ℝ)⁻¹))|) ≤
        1 / (4 * (smoothLcm (sharpS N) : ℝ)) := by
  have hQ := tendsto_sharpS_atTop.eventually
    eventually_smoothLcm_le_exp_five_mul
  filter_upwards [hQ, eventually_sharp_hoeffding_scale,
      eventually_one_le_sharpM_and_sharpM_le_N,
      eventually_two_hundred_le_sharpS] with N hQbound hscale hM hS
  intro I p hI hp0 hp1
  exact abs_reciprocal_sum_sub_mean_tail_le_inv_four_smoothLcm
    p (by omega) hM.2 (by omega) hI hp0 hp1 hscale hQbound

end

end Erdos294.SharpTail
