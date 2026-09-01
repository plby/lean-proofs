/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos294.PrescribedLocalLimit
import ErdosProblems.Erdos294.SharpDensity

/-! # Prescribed major-arc bound for the constant-width good set -/

open Filter Finset Real
open scoped BigOperators Topology

namespace Erdos294.SharpMajor

open Erdos297 Erdos297.ActiveLcm Erdos297.GoodFactorization
open Erdos297.MajorArc Erdos297.SupplyNumerics
open Erdos294.PrescribedLocalLimit Erdos294.SharpDensity
open Erdos294.SharpParameters Erdos294.SharpSupply

noncomputable section

attribute [local instance] Classical.propDecidable

lemma eventually_nineteenTwentiethPower_le_sharpM :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ ((19 : ℝ) / 20) ≤ (sharpM N : ℝ) := by
  have hsmall : ∀ᶠ N : ℕ in atTop,
      (N : ℝ) ^ (-((1 : ℝ) / 20)) ≤ (1 / 200 : ℝ) :=
    ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 20)).comp
      tendsto_natCast_atTop_atTop).eventually_le_const (by norm_num)
  filter_upwards [hsmall, eventually_ge_atTop (200 : ℕ)] with N hsmallN hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpow : (N : ℝ) ^ ((19 : ℝ) / 20) ≤ (N : ℝ) / 200 := by
    calc
      (N : ℝ) ^ ((19 : ℝ) / 20) =
          (N : ℝ) ^ (1 : ℝ) * (N : ℝ) ^ (-((1 : ℝ) / 20)) := by
        rw [← Real.rpow_add hNpos]
        congr 1
        norm_num
      _ = (N : ℝ) * (N : ℝ) ^ (-((1 : ℝ) / 20)) := by rw [Real.rpow_one]
      _ ≤ (N : ℝ) * (1 / 200 : ℝ) := by gcongr
      _ = (N : ℝ) / 200 := by ring
  have hNM : N ≤ 200 * sharpM N := by simp [sharpM]; omega
  have hfloor : (N : ℝ) / 200 ≤ (sharpM N : ℝ) := by
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 200)]
    exact_mod_cast (by simpa [Nat.mul_comm] using hNM)
  exact hpow.trans hfloor

lemma eventually_central_budgets :
    ∀ᶠ N : ℕ in atTop,
      2 * Real.pi * (centralCutoff N : ℝ) ≤ (sharpM N : ℝ) ∧
      2 * ((sharpGoodSet N).card : ℝ) *
        (2 * Real.pi * (centralCutoff N : ℝ) / (sharpM N : ℝ)) ^ 3 ≤
          (1 / 7 : ℝ) := by
  have hconst : ∀ᶠ N : ℕ in atTop, 2 * Real.pi ≤ (N : ℝ) ^ ((7 : ℝ) / 20) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (7 : ℝ) / 20)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (2 * Real.pi)
  have hcubicLimit : Tendsto (fun N : ℕ ↦
      16 * Real.pi ^ 3 * (N : ℝ) ^ (-((1 : ℝ) / 20))) atTop (nhds 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 20)).comp
        tendsto_natCast_atTop_atTop).const_mul (16 * Real.pi ^ 3)
  have hcubicSmall : ∀ᶠ N : ℕ in atTop,
      16 * Real.pi ^ 3 * (N : ℝ) ^ (-((1 : ℝ) / 20)) ≤ (1 / 7 : ℝ) :=
    (hcubicLimit.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 7)).mono
      fun _ h ↦ h.le
  filter_upwards [hconst, hcubicSmall,
      eventually_nineteenTwentiethPower_le_sharpM,
      eventually_ge_atTop (100 : ℕ)] with N hconstN hsmall hMlower hN
  have hx : (1 : ℝ) ≤ N := by
    exact_mod_cast (show 1 ≤ N by omega)
  have hxpos : (0 : ℝ) < N := zero_lt_one.trans_le hx
  have hcut := centralCutoff_le_rpow N
  have hMone : 1 ≤ sharpM N := by simp [sharpM]; omega
  have hcardNat : (sharpGoodSet N).card ≤ N := by
    calc
      (sharpGoodSet N).card ≤ (Icc 1 N).card :=
        card_le_card ((sharpGoodSet_subset_Icc N).trans
          (Icc_subset_Icc_left hMone))
      _ = N := by simp
  have hcard : ((sharpGoodSet N).card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcardNat
  constructor
  · calc
      2 * Real.pi * (centralCutoff N : ℝ) ≤
          2 * Real.pi * (N : ℝ) ^ ((3 : ℝ) / 5) := by gcongr
      _ ≤ (N : ℝ) ^ ((7 : ℝ) / 20) * (N : ℝ) ^ ((3 : ℝ) / 5) := by
        gcongr
      _ = (N : ℝ) ^ ((19 : ℝ) / 20) := by
        rw [← Real.rpow_add hxpos]
        norm_num
      _ ≤ (sharpM N : ℝ) := hMlower
  · exact (central_cubic_power_bound hx hMlower (Nat.cast_nonneg _)
      hcut hcard).trans hsmall

lemma eventually_intermediate_budget :
    ∀ᶠ N : ℕ in atTop,
      (((sharpM N + 1 : ℕ) : ℝ) *
        Real.exp (-(4 * (logLogScale N)⁻¹ * ((sharpGoodSet N).card : ℝ) *
          (centralCutoff N : ℝ) ^ 2 / (N : ℝ) ^ 2)) ≤ (1 / 4 : ℝ)) := by
  have hsmall : ∀ᶠ N : ℕ in atTop,
      2 * (N : ℝ) * Real.exp (-((N : ℝ) ^ ((1 : ℝ) / 10))) ≤ (1 / 4 : ℝ) :=
    (tendsto_intermediate_majorant.eventually_lt_const
      (by norm_num : (0 : ℝ) < 1 / 4)).mono fun _ h ↦ h.le
  filter_upwards [hsmall, eventually_half_rpow_le_centralCutoff,
      eventually_logLog_inv_ge_small_rpow,
      eventually_nineteenTwentiethPower_le_sharpGoodSet_card,
      eventually_one_le_sharpM_and_sharpM_le_N, eventually_ge_atTop (1 : ℕ)]
      with N hsmallN hcut hdelta hcard hM hN
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hexponent := intermediate_exponent_power_bound hx hcut hdelta hcard
  have hpower : (N : ℝ) ^ ((1 : ℝ) / 10) ≤ (N : ℝ) ^ ((7 : ℝ) / 50) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hexp : Real.exp (-(4 * (logLogScale N)⁻¹ *
        ((sharpGoodSet N).card : ℝ) * (centralCutoff N : ℝ) ^ 2 /
          (N : ℝ) ^ 2)) ≤ Real.exp (-((N : ℝ) ^ ((1 : ℝ) / 10))) :=
    Real.exp_le_exp.mpr (neg_le_neg (hpower.trans hexponent))
  have hpref : (((sharpM N + 1 : ℕ) : ℝ)) ≤ 2 * (N : ℝ) := by
    push_cast
    exact_mod_cast (by omega : sharpM N + 1 ≤ 2 * N)
  calc
    ((sharpM N + 1 : ℕ) : ℝ) *
        Real.exp (-(4 * (logLogScale N)⁻¹ * ((sharpGoodSet N).card : ℝ) *
          (centralCutoff N : ℝ) ^ 2 / (N : ℝ) ^ 2)) ≤
        2 * (N : ℝ) * Real.exp (-((N : ℝ) ^ ((1 : ℝ) / 10))) :=
      mul_le_mul hpref hexp (Real.exp_nonneg _) (by positivity)
    _ ≤ 1 / 4 := hsmallN

def prescribedMajorBlock (N : ℕ) (p : ℕ → ℝ) (z : ℕ) : ℂ :=
  let A := sharpGoodSet N
  let Q := activeLcm A
  let _ : NeZero Q := ⟨activeLcm_ne_zero A⟩
  MajorArc.fourierBlock (majorFrequencies Q (sharpM N)) A
    (fun n ↦ (Q / n : ZMod Q)) p (z : ZMod Q)

theorem eventually_prescribed_majorArc_lower :
    ∀ᶠ N : ℕ in atTop, ∀ (p : ℕ → ℝ) (z : ℕ),
      (∀ n ∈ sharpGoodSet N, 1 / logLogScale N ≤ p n) →
      (∀ n ∈ sharpGoodSet N, p n ≤ 1 / 2) →
      (∑ n ∈ sharpGoodSet N, p n / n =
        (z : ℝ) / activeLcm (sharpGoodSet N)) →
      (3 / 4 : ℝ) ≤ 1 + (prescribedMajorBlock N p z).re := by
  filter_upwards [eventually_central_budgets, eventually_intermediate_budget,
      eventually_one_le_sharpM_and_sharpM_le_N, eventually_pos_scales]
      with N hcentral hintermediate hM hscales
  intro p z hpLower hpUpper hmean
  let A := sharpGoodSet N
  let Q := activeLcm A
  let _ : NeZero Q := ⟨activeLcm_ne_zero A⟩
  have hHM : centralCutoff N ≤ sharpM N / 2 := by
    have hreal := hcentral.1
    have hpi : (2 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have htwice : ((2 * centralCutoff N : ℕ) : ℝ) ≤ (sharpM N : ℝ) := by
      push_cast
      exact (mul_le_mul_of_nonneg_right hpi (Nat.cast_nonneg _)).trans hreal
    have htwiceNat : 2 * centralCutoff N ≤ sharpM N := by exact_mod_cast htwice
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    simpa [Nat.mul_comm] using htwiceNat
  have hAinterval : A ⊆ Icc (sharpM N) N := by
    simpa [A] using sharpGoodSet_subset_Icc N
  have hApos : ∀ n ∈ A, 0 < n := by
    intro n hn
    exact goodDenominator_pos hM.1 (by simpa [A, sharpGoodSet] using hn)
  have hAdvd : ∀ n ∈ A, n ∣ Q := fun n hn ↦
    dvd_activeLcm_of_mem_of_pos hApos hn
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hscales.2.2.1
  have hp0 : ∀ n ∈ A, 0 ≤ p n := by
    intro n hn
    exact (one_div_pos.mpr hLLpos).le.trans (hpLower n (by simpa [A] using hn))
  have hp1 : ∀ n ∈ A, p n ≤ 1 := by
    intro n hn
    exact (hpUpper n (by simpa [A] using hn)).trans (by norm_num)
  have hcentralFinite := reciprocal_central_budgets
    (Q := Q) (M := sharpM N) (N := N) (H := centralCutoff N)
    hM.1 A hAinterval hcentral.1 hcentral.2
  have hintermediateFinite := reciprocal_intermediate_budget
    (Q := Q) (M := sharpM N) (N := N) (H := centralCutoff N)
    hM.1 hM.2 A hAinterval p (logLogScale N)⁻¹ (by positivity)
    (fun n hn ↦ by simpa [one_div, A] using hpLower n (by simpa [A] using hn))
    (fun n hn ↦ by simpa [A] using hpUpper n (by simpa [A] using hn))
    hintermediate
  have hresult := reciprocal_majorArc_lower_of_budgets_target
    (Q := Q) (M := sharpM N) (H := centralCutoff N) (z := z)
    hHM A p hApos hAdvd hp0 hp1 (by simpa [A, Q] using hmean)
    hcentralFinite.1 hcentralFinite.2 hintermediateFinite
  simpa [prescribedMajorBlock, A, Q] using hresult

end

end Erdos294.SharpMajor
