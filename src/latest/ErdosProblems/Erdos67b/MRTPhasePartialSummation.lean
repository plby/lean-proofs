import ErdosProblems.Erdos67b.MRTRationalShortSums

/-! # Finite summation by parts for averages of modulated short sums -/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

theorem mrtSum_Icc_mul_by_parts (u w : ℕ → ℂ) {H : ℕ} (hH : 1 ≤ H) :
    (∑ j ∈ Finset.Icc 1 H, u j * w j) =
      (∑ j ∈ Finset.Icc 1 H, u j) * w H +
        ∑ k ∈ Finset.Ico 1 H, (∑ j ∈ Finset.Icc 1 k, u j) * (w k - w (k + 1)) := by
  induction H with
  | zero => omega
  | succ H ih =>
    by_cases hH' : 1 ≤ H
    · rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_Ico_succ_top hH', ih hH']
      rw [Finset.sum_Icc_succ_top (by omega)]
      ring
    · have hzero : H = 0 := by omega
      subst H
      simp

theorem mrtNorm_sum_Icc_mul_le (u w : ℕ → ℂ) {H : ℕ} (hH : 1 ≤ H)
    {L : ℝ} (hw : ‖w H‖ ≤ 1)
    (hdiff : ∀ k ∈ Finset.Ico 1 H, ‖w k - w (k + 1)‖ ≤ L) :
    ‖∑ j ∈ Finset.Icc 1 H, u j * w j‖ ≤
      ‖∑ j ∈ Finset.Icc 1 H, u j‖ + L *
        ∑ k ∈ Finset.Ico 1 H, ‖∑ j ∈ Finset.Icc 1 k, u j‖ := by
  rw [mrtSum_Icc_mul_by_parts u w hH]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · rw [norm_mul]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hw (norm_nonneg _)
  · apply (norm_sum_le _ _).trans
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    rw [norm_mul, mul_comm L]
    exact mul_le_mul_of_nonneg_left (hdiff k hk) (norm_nonneg _)

theorem mrtSum_norm_weighted_Icc_le {ι : Type*} (I : Finset ι)
    (u : ι → ℕ → ℂ) (w : ℕ → ℂ) (H : ℕ) {B L : ℝ} (hB : 0 ≤ B) (hL : 0 ≤ L)
    (hw : ‖w H‖ ≤ 1) (hdiff : ∀ k ∈ Finset.Ico 1 H, ‖w k - w (k + 1)‖ ≤ L)
    (hprefix : ∀ k ≤ H, (∑ i ∈ I, ‖∑ j ∈ Finset.Icc 1 k, u i j‖) ≤ B) :
    (∑ i ∈ I, ‖∑ j ∈ Finset.Icc 1 H, u i j * w j‖) ≤ (1 + (H : ℝ) * L) * B := by
  by_cases hzero : H = 0
  · simpa only [hzero, Finset.Icc_eq_empty_of_lt (by omega : 0 < 1), Finset.sum_empty,
      norm_zero, Finset.sum_const_zero, Nat.cast_zero, zero_mul, add_zero, one_mul] using hB
  have hH : 1 ≤ H := by omega
  have hcard : ((H - 1 : ℕ) : ℝ) ≤ H := by exact_mod_cast Nat.sub_le H 1
  have hscale := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcard hL) hB
  calc
    _ ≤ ∑ i ∈ I, (‖∑ j ∈ Finset.Icc 1 H, u i j‖ +
        L * ∑ k ∈ Finset.Ico 1 H, ‖∑ j ∈ Finset.Icc 1 k, u i j‖) :=
      Finset.sum_le_sum fun i _ ↦ mrtNorm_sum_Icc_mul_le (u i) w hH hw hdiff
    _ = (∑ i ∈ I, ‖∑ j ∈ Finset.Icc 1 H, u i j‖) +
        L * ∑ k ∈ Finset.Ico 1 H, ∑ i ∈ I, ‖∑ j ∈ Finset.Icc 1 k, u i j‖ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_comm]
    _ ≤ B + L * ∑ _k ∈ Finset.Ico 1 H, B :=
      add_le_add (hprefix H le_rfl) (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun k hk ↦ hprefix k (Finset.mem_Ico.1 hk).2.le) hL)
    _ = B + L * (H - 1 : ℕ) * B := by
      rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      ring
    _ ≤ _ := by nlinarith only [hscale]

theorem mrtAdditivePhase_frequency_split (α β : ℝ) (n : ℕ) :
    additivePhase α n = additivePhase β n * additivePhase (α - β) n := by
  unfold additivePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem mrtNorm_additivePhase_step_le (θ : ℝ) (k : ℕ) :
    ‖additivePhase θ k - additivePhase θ (k + 1)‖ ≤ 2 * Real.pi * |θ| := by
  rw [additivePhase_add]
  rw [show additivePhase θ k - additivePhase θ k * additivePhase θ 1 =
    additivePhase θ k * (1 - additivePhase θ 1) by ring]
  rw [norm_mul, norm_additivePhase, one_mul, norm_sub_rev]
  simpa [additivePhase] using majorArc_norm_additivePhase_sub_le θ 0 1

theorem mrtSum_norm_typical_phase_transfer (blocks : Finset (ℕ × ℕ)) (Z Y H : ℕ)
    (f : ℕ → ℂ) {α β B : ℝ} (hB : 0 ≤ B)
    (hprefix : ∀ h ≤ H, (∑ n ∈ Finset.Ioc Y (2 * Y),
      ‖typicalModulatedShortSum blocks Z f n h β‖) ≤ B) :
    (∑ n ∈ Finset.Ioc Y (2 * Y), ‖typicalModulatedShortSum blocks Z f n H α‖) ≤
      (1 + 2 * Real.pi * (H : ℝ) * |α - β|) * B := by
  classical
  let u := fun n j ↦ if n + j ∈ typicalFactorizationSet blocks Z
    then f (n + j) * additivePhase β j else 0
  have heq (n : ℕ) : (∑ j ∈ Finset.Icc 1 H, u n j * additivePhase (α - β) j) =
      typicalModulatedShortSum blocks Z f n H α := by
    unfold typicalModulatedShortSum
    apply Finset.sum_congr rfl
    intro j _
    dsimp only [u]
    split_ifs
    · rw [mrtAdditivePhase_frequency_split α β j]
      ring
    · exact zero_mul _
  have hmain := mrtSum_norm_weighted_Icc_le (Finset.Ioc Y (2 * Y)) u
    (additivePhase (α - β)) H hB (by positivity : 0 ≤ 2 * Real.pi * |α - β|)
    (norm_additivePhase _ _).le (fun k _ ↦ mrtNorm_additivePhase_step_le _ k)
    (fun k hk ↦ hprefix k hk)
  simp_rw [heq] at hmain
  calc
    _ ≤ (1 + (H : ℝ) * (2 * Real.pi * |α - β|)) * B := hmain
    _ = _ := by ring

end

end Erdos67b
