import ErdosProblems.Erdos239.External.Erdos67.LSeriesLowCutoff
import ErdosProblems.Erdos239.External.Erdos67.ResidueLogPhase

/-!
# Eventual cutoff geometry for the sublinear L-series bound

This file isolates the rounding and growth facts used by the global
fixed-depth assembly.  The depth assumption is `2 ≤ R`: for `R = 1` the
assertion `Q² ceil(T^(1/R)) ≤ floor(T/16)` is false for general positive
`Q`, while every application chooses a large fixed depth.
-/

namespace Erdos67.LSeriesSublinearGeometry

noncomputable section

open Filter
open Erdos67.LSeriesLowCutoff
open Erdos67.ResidueLogPhase

/-- All cutoff comparisons required by the global fixed-depth assembly hold
uniformly once the height is sufficiently large. -/
theorem exists_cutoffGeometry_threshold
    (Q R S₀ : ℕ) (hQ : 0 < Q) (hR : 2 ≤ R) :
    ∃ V₀ : ℕ, 3 ≤ V₀ ∧ ∀ v : ℝ, (V₀ : ℝ) ≤ |v| →
      let T : ℝ := |v|
      let S : ℕ := heightRootCutoff T R
      let M : ℕ := Q ^ 2 * S
      let K : ℕ := ⌊T / 16⌋₊
      let H : ℕ := ⌈T⌉₊
      0 < M ∧ M ≤ K ∧ K < H ∧ S₀ ≤ S ∧
        H - 1 ≤ 64 * (K + 1) ∧
        ((K + 2 : ℕ) : ℝ) ≤ positiveLogCoefficient v ∧
        positiveLogCoefficient v < (S : ℝ) ^ (R + 1) := by
  have hRR : (2 : ℝ) ≤ R := by exact_mod_cast hR
  have hRpos : (0 : ℝ) < R := by positivity
  have hRinvPos : (0 : ℝ) < ((R : ℝ)⁻¹) := inv_pos.mpr hRpos
  have hRinvHalf : ((R : ℝ)⁻¹) ≤ 1 / 2 := by
    simpa only [one_div] using
      (one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hRR)
  have hComplement : 0 < 1 - ((R : ℝ)⁻¹) := by linarith
  have hrootTendsto : Tendsto (fun T : ℝ ↦ T ^ ((R : ℝ)⁻¹)) atTop atTop :=
    tendsto_rpow_atTop hRinvPos
  have hquotTendsto : Tendsto
      (fun T : ℝ ↦ T ^ (1 - ((R : ℝ)⁻¹))) atTop atTop :=
    tendsto_rpow_atTop hComplement
  have hrootLarge : ∀ᶠ T : ℝ in atTop,
      (S₀ : ℝ) ≤ T ^ ((R : ℝ)⁻¹) :=
    hrootTendsto.eventually (eventually_ge_atTop (S₀ : ℝ))
  have hquotLarge : ∀ᶠ T : ℝ in atTop,
      (64 : ℝ) * Q ^ 2 ≤ T ^ (1 - ((R : ℝ)⁻¹)) :=
    hquotTendsto.eventually (eventually_ge_atTop ((64 : ℝ) * Q ^ 2))
  have hlarge : ∀ᶠ T : ℝ in atTop,
      (64 : ℝ) ≤ T ∧
      (S₀ : ℝ) ≤ T ^ ((R : ℝ)⁻¹) ∧
      (64 : ℝ) * Q ^ 2 ≤ T ^ (1 - ((R : ℝ)⁻¹)) := by
    filter_upwards [eventually_ge_atTop (64 : ℝ), hrootLarge, hquotLarge]
      with T hT hroot hquot
    exact ⟨hT, hroot, hquot⟩
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.1 hlarge
  obtain ⟨V₁ : ℕ, hV₁⟩ := exists_nat_ge T₀
  let V₀ : ℕ := max 3 V₁
  refine ⟨V₀, Nat.le_max_left 3 V₁, ?_⟩
  intro v hv
  dsimp only
  let T : ℝ := |v|
  let S : ℕ := heightRootCutoff T R
  let M : ℕ := Q ^ 2 * S
  let K : ℕ := ⌊T / 16⌋₊
  let H : ℕ := ⌈T⌉₊
  have hV₁V₀ : V₁ ≤ V₀ := Nat.le_max_right 3 V₁
  have hT₀T : T₀ ≤ T := by
    calc
      T₀ ≤ V₁ := hV₁
      _ ≤ V₀ := by exact_mod_cast hV₁V₀
      _ ≤ T := by simpa only [T] using hv
  obtain ⟨hT64, hroot, hquot⟩ := hT₀ T hT₀T
  have hTpos : 0 < T := by linarith
  have hTone : 1 ≤ T := by linarith
  have hrootPos : 0 < T ^ ((R : ℝ)⁻¹) := Real.rpow_pos_of_pos hTpos _
  have hSpos : 0 < S := by
    dsimp only [S]
    exact heightRootCutoff_pos hTpos R
  have hMpos : 0 < M := by
    dsimp only [M]
    exact Nat.mul_pos (pow_pos hQ _) hSpos
  have hceilUpper : (S : ℝ) ≤ 2 * T ^ ((R : ℝ)⁻¹) := by
    dsimp only [S, heightRootCutoff]
    exact Erdos1149.AnalyticParameters.natCeil_le_two_mul
      (Real.one_le_rpow hTone hRinvPos.le)
  have hpowerProduct :
      T ^ (1 - ((R : ℝ)⁻¹)) * T ^ ((R : ℝ)⁻¹) = T := by
    rw [← Real.rpow_add hTpos]
    ring_nf
    exact Real.rpow_one T
  have hMreal : (M : ℝ) ≤ T / 32 := by
    have hcastQ : (((Q ^ 2 : ℕ) : ℝ)) = (Q : ℝ) ^ 2 := by norm_cast
    have hfirst : (M : ℝ) ≤
        (Q : ℝ) ^ 2 * (2 * T ^ ((R : ℝ)⁻¹)) := by
      dsimp only [M]
      push_cast
      gcongr
    have hmul := mul_le_mul_of_nonneg_right hquot
      (Real.rpow_nonneg hTpos.le ((R : ℝ)⁻¹))
    calc
      (M : ℝ) ≤ (Q : ℝ) ^ 2 *
          (2 * T ^ ((R : ℝ)⁻¹)) := hfirst
      _ = ((64 : ℝ) * Q ^ 2 * T ^ ((R : ℝ)⁻¹)) / 32 := by ring
      _ ≤ (T ^ (1 - ((R : ℝ)⁻¹)) *
          T ^ ((R : ℝ)⁻¹)) / 32 := by gcongr
      _ = T / 32 := by rw [hpowerProduct]
  have hKlower : T / 32 ≤ K := by
    dsimp only [K]
    have htwo : (2 : ℝ) ≤ T / 16 := by linarith
    convert Erdos1149.AnalyticParameters.half_le_natFloor htwo using 1 <;> ring
  have hMK : M ≤ K := by
    exact_mod_cast hMreal.trans hKlower
  have hKupper : (K : ℝ) ≤ T / 16 := by
    dsimp only [K]
    exact Nat.floor_le (by positivity)
  have hTceil : T ≤ H := by
    dsimp only [H]
    exact Nat.le_ceil T
  have hKH : K < H := by
    have hKT : (K : ℝ) < T := hKupper.trans_lt (by linarith)
    exact_mod_cast hKT.trans_le hTceil
  have hS₀S : S₀ ≤ S := by
    have hrootCeil : T ^ ((R : ℝ)⁻¹) ≤ (S : ℝ) := by
      dsimp only [S, heightRootCutoff]
      exact Nat.le_ceil _
    exact_mod_cast hroot.trans hrootCeil
  have hHsub : ((H - 1 : ℕ) : ℝ) ≤ T := by
    have hHlt : (H : ℝ) < T + 1 := by
      dsimp only [H]
      exact Nat.ceil_lt_add_one hTpos.le
    have hHone : 1 ≤ H := Nat.one_le_iff_ne_zero.mpr (by omega)
    rw [Nat.cast_sub hHone]
    norm_num
    linarith
  have hKadd : T / 16 < (K + 1 : ℕ) := by
    dsimp only [K]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one (T / 16))
  have hHratio : H - 1 ≤ 64 * (K + 1) := by
    have hreal : ((H - 1 : ℕ) : ℝ) ≤ 64 * ((K + 1 : ℕ) : ℝ) := by
      calc
        ((H - 1 : ℕ) : ℝ) ≤ T := hHsub
        _ ≤ 64 * ((K + 1 : ℕ) : ℝ) := by linarith
    exact_mod_cast hreal
  have hKcoefficient : ((K + 2 : ℕ) : ℝ) ≤ positiveLogCoefficient v := by
    have hpi : 2 * Real.pi < 8 := by nlinarith [Real.pi_lt_four]
    have hdenpos : 0 < 2 * Real.pi := by positivity
    have hT8 : T / 8 < T / (2 * Real.pi) := by
      exact (div_lt_div_iff_of_pos_left hTpos (by norm_num) hdenpos).2 hpi
    have hK2 : ((K + 2 : ℕ) : ℝ) ≤ T / 8 := by
      push_cast
      linarith
    exact (calc
      ((K + 2 : ℕ) : ℝ) ≤ T / 8 := hK2
      _ < T / (2 * Real.pi) := hT8
      _ = positiveLogCoefficient v := by
        simp only [positiveLogCoefficient, T]).le
  have hrootPow : (T ^ ((R : ℝ)⁻¹)) ^ R = T :=
    Real.rpow_inv_natCast_pow hTpos.le (by omega)
  have hTSPow : T ≤ (S : ℝ) ^ R := by
    rw [← hrootPow]
    exact pow_le_pow_left₀ (Real.rpow_nonneg hTpos.le _)
      (by
        dsimp only [S, heightRootCutoff]
        exact Nat.le_ceil _) R
  have hSone : (1 : ℝ) ≤ S := by exact_mod_cast hSpos
  have hSPowMono : (S : ℝ) ^ R ≤ (S : ℝ) ^ (R + 1) := by
    exact pow_le_pow_right₀ hSone (by omega)
  have hcoeffT : positiveLogCoefficient v < T := by
    have hdenOne : 1 < 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    simpa only [positiveLogCoefficient, T] using div_lt_self hTpos hdenOne
  exact ⟨hMpos, hMK, hKH, hS₀S, hHratio, hKcoefficient,
    hcoeffT.trans_le (hTSPow.trans hSPowMono)⟩

end

end Erdos67.LSeriesSublinearGeometry
