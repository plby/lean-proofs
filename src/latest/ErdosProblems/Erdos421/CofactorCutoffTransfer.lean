import ErdosProblems.Erdos421.ClippedWindowTransfer
import ErdosProblems.Erdos421.WindowTransferParameters
import ErdosProblems.Erdos421.ClippedErrorLogSaving
import ErdosProblems.Erdos421.LogarithmicCofactorVariance

/-! # Unconditional transfer of the prime-cofactor window to an intermediate cutoff -/

namespace Erdos421

open MeasureTheory Filter Topology

theorem logarithmicPrimeCofactorWindow_transferred_l1 {k : ℕ} (hk : 0 < k)
    {β θ e ε τ : ℝ} (hβ : 0 < β) (hθ : θ < 1 / 5) (he : 0 < e) (he' : e < 9 / 10)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hτ : 0 < τ) :
    ∃ L : ℝ, 2 ≤ L ∧ ∀ᶠ X : ℕ in atTop,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ (Real.log X) ^ (-L) ∧
      ∀ Q D W Z B w : ℕ, 0 < Q → 0 < D → W ≤ Z → 3 * X ≤ B → B ≤ 4 * X → Q ≤ B →
      0 < w → B < w ^ k → Q * (W * D ^ 2) < w ^ k →
      (X : ℝ) ^ β ≤ (W - 1 : ℕ) → (Z : ℝ) ≤ (X : ℝ) ^ θ →
      ((Q * (W * D ^ 2) : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) →
      16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log W →
      ∀ P : Finset ℕ, (∀ p ∈ P, p.Prime ∧ w ≤ p ∧ p ≤ Q) → ∀ δ₁ δ₂ : ℝ,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ δ₁ → δ₁ ≤ (Real.log X) ^ (-L) →
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ δ₂ → δ₂ ≤ (Real.log X) ^ (-L) →
      (∫ y in Real.log (X : ℝ)..Real.log (2 * X : ℝ),
        |logarithmicPrimeCofactorWindow P B Z δ₁ y -
          logarithmicPrimeCofactorWindow P B Z δ₂ y|) ≤
        6 * (ε * (∑ p ∈ P, (p : ℝ)⁻¹) * roughEulerProduct W) + 4 * τ / Real.log X := by
  have hτsq : 0 < τ ^ 2 := sq_pos_of_pos hτ
  obtain ⟨L, hL, hfrozen⟩ := frozenCofactorBuchstabWindow_log_saving hk hβ hθ he he'
    (by norm_num : (0 : ℝ) ≤ 2) hτsq
  refine ⟨L, hL, ?_⟩
  have hloglarge : ∀ᶠ X : ℕ in atTop, max 1 τ ≤ Real.log X :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hfrozen, clipped_errors_log_saving hβ hτsq,
    logarithmicPrimeCofactorWindow_variance hk hε hε1 hτsq,
    hloglarge, eventually_ge_atTop 2] with X hfX heX hbX hlog hX
  refine ⟨hfX.1, ?_⟩
  intro Q D W Z B w hQ hD hWZ hB hBX hQB hw hBw hcut hW hZ hlevelX hlevel
    P hP δ₁ δ₂ hδ₁lo hδ₁hi hδ₂lo hδ₂hi
  have hXone : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hXp : (0 : ℝ) < X := by linarith
  have hlog1 : 1 ≤ Real.log X := (le_max_left _ _).trans hlog
  have hτlog : τ ≤ Real.log X := (le_max_right _ _).trans hlog
  have hlogp := Real.log_pos hXone
  obtain ⟨hδ₁, hδ₁L, hY₁⟩ := prime_transfer_window_scales hXone.le hlog1 he.le hL hδ₁lo hδ₁hi
  obtain ⟨hδ₂, hδ₂L, hY₂⟩ := prime_transfer_window_scales hXone.le hlog1 he.le hL hδ₂lo hδ₂hi
  have hW2 : 2 ≤ W := by
    have hwp : 0 < W - 1 := by exact_mod_cast (Real.rpow_pos_of_pos hXp β).trans_le hW
    omega
  have hWpow : (X : ℝ) ^ β ≤ W :=
    hW.trans (by exact_mod_cast (Nat.sub_le W 1))
  have hZB : Z ≤ B + 1 := by
    have hZX : (Z : ℝ) ≤ X := hZ.trans
      (Real.rpow_le_self_of_one_le hXone.le (by linarith))
    have hZXnat : Z ≤ X := by exact_mod_cast hZX
    omega
  have hcover : Z ≤ 2 ^ primePartitionDepth Z + 1 := by
    have hc := primePartitionDepth_cover Z
    omega
  have hPB : P ⊆ Finset.Icc 1 B := by
    intro p hp
    exact Finset.mem_Icc.mpr ⟨(hP p hp).1.pos, ((hP p hp).2.2).trans hQB⟩
  have hbase := hbX Q D W w hQ hD hW2 hw hcut hlevelX hlevel P hP B δ₁ δ₂
    hBw hB hδ₁ hδ₂ hδ₁L hδ₂L hY₁ hY₂
  have hbaseL1 := logarithmic_abs_integral_le_two_errors
    ((logarithmicPrimeCofactorWindow_continuous P B W δ₁).sub
      (logarithmicPrimeCofactorWindow_continuous P B W δ₂)) hXone
    (mul_nonneg (mul_nonneg hε.le (Finset.sum_nonneg (fun p _ ↦ by positivity)))
      (roughEulerProduct_pos W).le) hτ hbase
  have hf := hfX.2 W Z B w hWZ hB hw hBw hW hZ P
    (fun p hp ↦ ⟨(hP p hp).1, (hP p hp).2.1⟩) δ₁ δ₂ hδ₁lo hδ₁hi hδ₂lo hδ₂hi
  norm_num only [Real.rpow_ofNat] at hf
  have hfL1 := logarithmic_abs_integral_le_one_error
    ((frozenCofactorBuchstabWindow_continuous P W Z (primePartitionDepth Z)
      (primePartitionCount X) B δ₁).sub
      (frozenCofactorBuchstabWindow_continuous P W Z (primePartitionDepth Z)
        (primePartitionCount X) B δ₂)) hXone hτ hf
  have he₁ := (heX W Z (primePartitionDepth Z) B hWpow hB hBX hZB δ₁ hδ₁).2 P hPB
  have he₂ := (heX W Z (primePartitionDepth Z) B hWpow hB hBX hZB δ₂ hδ₂).2 P hPB
  have herr := cutoff_l1_error_absorption hτ hlogp hτlog
  have htransfer := logarithmicPrimeCofactorWindow_cutoff_l1 P hWZ hW2 hcover
    (primePartitionCount_pos hlog1) B hδ₁ hδ₂ hXp
  simp only [Pi.sub_apply] at hbaseL1 hfL1
  rw [show 4 * τ / Real.log X = 4 * (τ / Real.log X) by ring]
  linarith only [hbaseL1, hfL1, he₁, he₂, herr, htransfer]

end Erdos421
