/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos297.MajorArc
import ErdosProblems.Erdos297.GoodSetDensity
import ErdosProblems.Erdos297.LogisticNormalization

/-!
# The eventual normalized major arc for Erdős problem 297

This file applies the finite reciprocal major-arc estimate to the normalized
critical logistic profile on the concrete good denominator set.  The active
LCM is used as the Fourier modulus.  All hypotheses left by the finite lemma
are discharged from the source-scale estimates.
-/

open scoped BigOperators

namespace Erdos297.MajorEventual

open Filter Finset
open Erdos297.MajorArc
open Erdos297.GoodSetDensity
open Erdos297.LogisticNormalization
open Erdos297.ActiveLcm

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Numerical estimates -/

/-- A pointwise power bound for the central cubic error. -/
private lemma central_cubic_power_bound
    {x m h a : ℝ} (hx : 1 ≤ x)
    (hm : x ^ ((19 : ℝ) / 20) ≤ m)
    (hh : 0 ≤ h) (hH : h ≤ x ^ ((3 : ℝ) / 5))
    (ha0 : 0 ≤ a) (ha : a ≤ x) :
    2 * a * (2 * Real.pi * h / m) ^ 3 ≤
      16 * Real.pi ^ 3 * x ^ (-((1 : ℝ) / 20)) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hmpos : 0 < m :=
    (Real.rpow_pos_of_pos hxp _).trans_le hm
  have hnum : 2 * Real.pi * h ≤
      2 * Real.pi * x ^ ((3 : ℝ) / 5) :=
    mul_le_mul_of_nonneg_left hH (by positivity)
  have hfrac : 2 * Real.pi * h / m ≤
      2 * Real.pi * x ^ ((3 : ℝ) / 5) /
        x ^ ((19 : ℝ) / 20) := by
    calc
      2 * Real.pi * h / m ≤
          2 * Real.pi * x ^ ((3 : ℝ) / 5) / m :=
        div_le_div_of_nonneg_right hnum hmpos.le
      _ ≤ 2 * Real.pi * x ^ ((3 : ℝ) / 5) /
          x ^ ((19 : ℝ) / 20) :=
        div_le_div_of_nonneg_left (by positivity)
          (Real.rpow_pos_of_pos hxp _) hm
  have hratio :
      x ^ ((3 : ℝ) / 5) / x ^ ((19 : ℝ) / 20) =
        x ^ (-((7 : ℝ) / 20)) := by
    rw [← Real.rpow_sub hxp]
    congr 1
    norm_num
  calc
    2 * a * (2 * Real.pi * h / m) ^ 3 ≤
        2 * x *
          (2 * Real.pi * x ^ ((3 : ℝ) / 5) /
            x ^ ((19 : ℝ) / 20)) ^ 3 := by
      gcongr
    _ = 2 * x * (2 * Real.pi * x ^ (-((7 : ℝ) / 20))) ^ 3 := by
      rw [show 2 * Real.pi * x ^ ((3 : ℝ) / 5) /
          x ^ ((19 : ℝ) / 20) =
          2 * Real.pi *
            (x ^ ((3 : ℝ) / 5) / x ^ ((19 : ℝ) / 20)) by ring,
        hratio]
    _ = 16 * Real.pi ^ 3 *
        (x * (x ^ (-((7 : ℝ) / 20))) ^ 3) := by ring
    _ = 16 * Real.pi ^ 3 * x ^ (-((1 : ℝ) / 20)) := by
      congr 1
      calc
        x * (x ^ (-((7 : ℝ) / 20))) ^ 3 =
            x ^ (1 : ℝ) * x ^ (-((7 : ℝ) / 20) * 3) := by
          rw [Real.rpow_one, ← Real.rpow_mul_natCast hx0]
          norm_num
        _ = x ^ ((1 : ℝ) + -((7 : ℝ) / 20) * 3) := by
          rw [Real.rpow_add hxp]
        _ = x ^ (-((1 : ℝ) / 20)) := by norm_num

/-- The exponent in the intermediate estimate has a fixed power saving. -/
private lemma intermediate_exponent_power_bound
    {x h delta a : ℝ} (hx : 1 ≤ x)
    (hH : x ^ ((3 : ℝ) / 5) / 2 ≤ h)
    (hdelta : x ^ (-((1 : ℝ) / 100)) ≤ delta)
    (ha : x ^ ((19 : ℝ) / 20) ≤ a) :
    x ^ ((7 : ℝ) / 50) ≤
      4 * delta * a * h ^ 2 / x ^ 2 := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hxne : x ≠ 0 := hxp.ne'
  have hdelta0 : 0 ≤ delta :=
    (Real.rpow_nonneg hx0 _).trans hdelta
  have ha0 : 0 ≤ a := (Real.rpow_nonneg hx0 _).trans ha
  have hh0 : 0 ≤ h :=
    (div_nonneg (Real.rpow_nonneg hx0 _) (by norm_num)).trans hH
  have hH2 : x ^ ((6 : ℝ) / 5) / 4 ≤ h ^ 2 := by
    calc
      x ^ ((6 : ℝ) / 5) / 4 =
          (x ^ ((3 : ℝ) / 5) / 2) ^ 2 := by
        rw [div_pow, ← Real.rpow_mul_natCast hx0]
        norm_num
      _ ≤ h ^ 2 := pow_le_pow_left₀ (by positivity) hH 2
  have hprod :
      x ^ (-((1 : ℝ) / 100)) * x ^ ((19 : ℝ) / 20) *
          (x ^ ((6 : ℝ) / 5) / 4) ≤ delta * a * h ^ 2 := by
    gcongr
  have hid :
      (x ^ (-((1 : ℝ) / 100)) * x ^ ((19 : ℝ) / 20) *
          (x ^ ((6 : ℝ) / 5) / 4)) / x ^ 2 =
        x ^ ((7 : ℝ) / 50) / 4 := by
    calc
      (x ^ (-((1 : ℝ) / 100)) * x ^ ((19 : ℝ) / 20) *
          (x ^ ((6 : ℝ) / 5) / 4)) / x ^ 2 =
          (x ^ (-((1 : ℝ) / 100)) * x ^ ((19 : ℝ) / 20) *
            x ^ ((6 : ℝ) / 5) / x ^ 2) / 4 := by ring
      _ = (x ^ (-((1 : ℝ) / 100) + (19 : ℝ) / 20 + (6 : ℝ) / 5) /
            x ^ 2) / 4 := by
        rw [Real.rpow_add hxp, Real.rpow_add hxp]
      _ = x ^ (-((1 : ℝ) / 100) + (19 : ℝ) / 20 + (6 : ℝ) / 5 - 2) /
            4 := by
        rw [← Real.rpow_sub_natCast hxne]
        norm_num
      _ = x ^ ((7 : ℝ) / 50) / 4 := by norm_num
  have hmain : x ^ ((7 : ℝ) / 50) / 4 ≤
      delta * a * h ^ 2 / x ^ 2 := by
    rw [← hid]
    exact div_le_div_of_nonneg_right hprod (sq_nonneg x)
  calc
    x ^ ((7 : ℝ) / 50) = 4 * (x ^ ((7 : ℝ) / 50) / 4) := by ring
    _ ≤ 4 * (delta * a * h ^ 2 / x ^ 2) :=
      mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = 4 * delta * a * h ^ 2 / x ^ 2 := by ring

private lemma tendsto_intermediate_majorant :
    Tendsto (fun N : ℕ ↦
      2 * (N : ℝ) * Real.exp (-((N : ℝ) ^ ((1 : ℝ) / 10))))
      atTop (nhds 0) := by
  have hy : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ ((1 : ℝ) / 10))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 10)).comp
      tendsto_natCast_atTop_atTop
  have hcore :=
    (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (10 : ℝ) 1 one_pos).comp hy
  have hcore' : Tendsto (fun N : ℕ ↦
      (N : ℝ) * Real.exp (-((N : ℝ) ^ ((1 : ℝ) / 10))))
      atTop (nhds 0) := by
    apply hcore.congr'
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    have hx0 : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    dsimp
    rw [← Real.rpow_mul hx0]
    norm_num
  simpa only [mul_zero, mul_assoc] using hcore'.const_mul 2

/-- Both explicit central Taylor budgets hold eventually at the source
scales. -/
private theorem eventually_central_budgets :
    ∀ᶠ N : ℕ in atTop,
      2 * Real.pi * (centralCutoff N : ℝ) ≤ (M N : ℝ) ∧
      2 * ((goodSet N).card : ℝ) *
        (2 * Real.pi * (centralCutoff N : ℝ) / (M N : ℝ)) ^ 3 ≤
          (1 / 7 : ℝ) := by
  have hconst : ∀ᶠ N : ℕ in atTop,
      2 * Real.pi ≤ (N : ℝ) ^ ((7 : ℝ) / 20) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (7 : ℝ) / 20)).comp
      tendsto_natCast_atTop_atTop).eventually_ge_atTop (2 * Real.pi)
  have hcubicLimit : Tendsto (fun N : ℕ ↦
      16 * Real.pi ^ 3 * (N : ℝ) ^ (-((1 : ℝ) / 20)))
      atTop (nhds 0) := by
    simpa only [Function.comp_apply, mul_zero] using
      ((tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 20)).comp
        tendsto_natCast_atTop_atTop).const_mul (16 * Real.pi ^ 3)
  have hcubicSmall : ∀ᶠ N : ℕ in atTop,
      16 * Real.pi ^ 3 * (N : ℝ) ^ (-((1 : ℝ) / 20)) ≤
        (1 / 7 : ℝ) :=
    (hcubicLimit.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 7)).mono
      fun _ h ↦ h.le
  filter_upwards [hconst, hcubicSmall,
    eventually_nineteenTwentiethPower_le_M,
    eventually_ge_atTop (1 : ℕ)] with N hconstN hsmall hM hN
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hxpos : (0 : ℝ) < N := zero_lt_one.trans_le hx
  have hcut := centralCutoff_le_rpow N
  have hA : goodSet N ⊆ Icc 1 N := by
    simpa [goodSet, sourceGoodDenominators] using
      sourceGoodDenominators_subset_denominators (N := N) (by
        have hmone : (1 : ℝ) ≤ M N :=
          (Real.one_le_rpow hx (by norm_num)).trans hM
        exact_mod_cast hmone)
  have hcardNat : (goodSet N).card ≤ N := by
    calc
      (goodSet N).card ≤ (Icc 1 N).card := card_le_card hA
      _ = N := by simp
  have hcard : ((goodSet N).card : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hcardNat
  constructor
  · calc
      2 * Real.pi * (centralCutoff N : ℝ) ≤
          2 * Real.pi * (N : ℝ) ^ ((3 : ℝ) / 5) :=
        mul_le_mul_of_nonneg_left hcut (by positivity)
      _ ≤ (N : ℝ) ^ ((7 : ℝ) / 20) *
          (N : ℝ) ^ ((3 : ℝ) / 5) :=
        mul_le_mul_of_nonneg_right hconstN
          (Real.rpow_nonneg (zero_le_one.trans hx) _)
      _ = (N : ℝ) ^ ((19 : ℝ) / 20) := by
        rw [← Real.rpow_add hxpos]
        norm_num
      _ ≤ (M N : ℝ) := hM
  · exact (central_cubic_power_bound hx hM (Nat.cast_nonneg _)
      hcut (Nat.cast_nonneg _) hcard).trans hsmall

/-- The explicit intermediate exponential budget holds eventually. -/
private theorem eventually_intermediate_budget :
    ∀ᶠ N : ℕ in atTop,
      (((M N + 1 : ℕ) : ℝ) *
        Real.exp (-(4 * (logLogScale N)⁻¹ * ((goodSet N).card : ℝ) *
          (centralCutoff N : ℝ) ^ 2 / (N : ℝ) ^ 2)) ≤
        (1 / 4 : ℝ)) := by
  have hsmall : ∀ᶠ N : ℕ in atTop,
      2 * (N : ℝ) * Real.exp (-((N : ℝ) ^ ((1 : ℝ) / 10))) ≤
        (1 / 4 : ℝ) :=
    (tendsto_intermediate_majorant.eventually_lt_const
      (by norm_num : (0 : ℝ) < 1 / 4)).mono fun _ h ↦ h.le
  filter_upwards [hsmall, eventually_half_rpow_le_centralCutoff,
    eventually_logLog_inv_ge_small_rpow,
    eventually_nineteenTwentiethPower_le_sourceGoodDenominators_card,
    eventually_nat_scale_chain, eventually_pos_scales,
    eventually_ge_atTop (1 : ℕ)] with
      N hsmallN hcut hdelta hcard hchain hscales hN
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hgoodCard :
      (N : ℝ) ^ ((19 : ℝ) / 20) ≤ ((goodSet N).card : ℝ) := by
    simpa [goodSet, sourceGoodDenominators] using hcard
  have hexponent := intermediate_exponent_power_bound hx hcut hdelta hgoodCard
  have hpower : (N : ℝ) ^ ((1 : ℝ) / 10) ≤
      (N : ℝ) ^ ((7 : ℝ) / 50) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hexp : Real.exp (-(4 * (logLogScale N)⁻¹ *
        ((goodSet N).card : ℝ) * (centralCutoff N : ℝ) ^ 2 /
          (N : ℝ) ^ 2)) ≤
      Real.exp (-((N : ℝ) ^ ((1 : ℝ) / 10))) :=
    Real.exp_le_exp.mpr (neg_le_neg (hpower.trans hexponent))
  have hMleNreal : (M N : ℝ) ≤ (N : ℝ) := by
    have hN0 : (0 : ℝ) ≤ N := by positivity
    linarith [hchain.2.2]
  have hpref : (((M N + 1 : ℕ) : ℝ)) ≤ 2 * (N : ℝ) := by
    push_cast
    linarith
  calc
    ((M N + 1 : ℕ) : ℝ) *
        Real.exp (-(4 * (logLogScale N)⁻¹ * ((goodSet N).card : ℝ) *
          (centralCutoff N : ℝ) ^ 2 / (N : ℝ) ^ 2)) ≤
        2 * (N : ℝ) *
          Real.exp (-((N : ℝ) ^ ((1 : ℝ) / 10))) := by
      exact mul_le_mul hpref hexp (Real.exp_nonneg _) (by positivity)
    _ ≤ 1 / 4 := hsmallN

/-! ## Application to the normalized logistic profile -/

/-- The active-LCM major block of the normalized critical logistic product
measure has the source lower bound for all sufficiently large `N`. -/
theorem eventually_normalized_majorArc_lower {lam : ℝ}
    (hlam : IsUniqueCriticalParameter lam) :
    ∀ᶠ N : ℕ in atTop,
      (3 / 4 : ℝ) ≤ 1 + (normalizedMajorBlock lam N).re := by
  filter_upwards [eventually_centralCutoff_le_half_M,
    eventually_central_budgets, eventually_intermediate_budget,
    eventually_sourceGoodDenominators_pos,
    eventually_normalized_probability_bounds hlam,
    eventually_normalized_reciprocal_mean_eq_one hlam,
    eventually_pos_scales,
    eventually_nineteenTwentiethPower_le_M,
    eventually_nat_scale_chain] with
      N hHM hcentral hintermediate hApos hp hmean hscales hMlower hchain
  let A := goodSet N
  let Q := activeLcm A
  letI : NeZero Q := ⟨activeLcm_ne_zero A⟩
  have hx : (1 : ℝ) ≤ N := by
    have hNnat : 0 < N := by exact_mod_cast hscales.1
    exact_mod_cast hNnat
  have hMoneR : (1 : ℝ) ≤ M N :=
    (Real.one_le_rpow hx (by norm_num)).trans hMlower
  have hMpos : 0 < M N := by
    have : (0 : ℝ) < M N := zero_lt_one.trans_le hMoneR
    exact_mod_cast this
  have hAinterval : A ⊆ Icc (M N) N := by
    simpa [A, goodSet, sourceGoodDenominators] using
      sourceGoodDenominators_subset_Icc N
  have hApos' : ∀ n ∈ A, 0 < n := by
    simpa [A, goodSet, sourceGoodDenominators] using hApos
  have hAdvd : ∀ n ∈ A, n ∣ Q := fun n hn ↦
    dvd_activeLcm_of_mem_of_pos hApos' hn
  have hp0 : ∀ n ∈ A, 0 ≤ normalizedLogisticProbability lam N n := by
    intro n hn
    exact (one_div_pos.mpr (zero_lt_one.trans hscales.2.2.1)).le.trans
      ((hp n (by simpa [A] using hn)).1)
  have hp1 : ∀ n ∈ A, normalizedLogisticProbability lam N n ≤ 1 := by
    intro n hn
    exact (hp n (by simpa [A] using hn)).2.trans (by norm_num)
  have hMNreal : (M N : ℝ) ≤ (N : ℝ) := by
    have hN0 : (0 : ℝ) ≤ N := by positivity
    linarith [hchain.2.2]
  have hMN : M N ≤ N := by exact_mod_cast hMNreal
  have hdeltaNonneg : 0 ≤ (logLogScale N)⁻¹ :=
    inv_nonneg.mpr (zero_lt_one.trans hscales.2.2.1).le
  have hcentralFinite := reciprocal_central_budgets
    (Q := Q) (M := M N) (N := N) (H := centralCutoff N)
    hMpos A hAinterval hcentral.1 hcentral.2
  have hintermediateFinite := reciprocal_intermediate_budget
    (Q := Q) (M := M N) (N := N) (H := centralCutoff N)
    hMpos hMN
    A hAinterval (normalizedLogisticProbability lam N)
    (logLogScale N)⁻¹ hdeltaNonneg
    (fun n hn ↦ by simpa [one_div] using (hp n (by simpa [A] using hn)).1)
    (fun n hn ↦ (hp n (by simpa [A] using hn)).2)
    hintermediate
  have hresult := reciprocal_majorArc_lower_of_budgets
    (Q := Q) (M := M N) (H := centralCutoff N) hHM A
    (normalizedLogisticProbability lam N) hApos' hAdvd hp0 hp1
    (by simpa [A] using hmean) hcentralFinite.1 hcentralFinite.2
    hintermediateFinite
  simpa [normalizedMajorBlock, A, Q] using hresult

end

end Erdos297.MajorEventual

#print axioms Erdos297.MajorEventual.eventually_normalized_majorArc_lower
