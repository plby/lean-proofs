/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos297.LocalLimit

/-!
# The Liu--Sawhney local limit theorem with a prescribed rational target

The development for Erdős Problem 297 proves the local limit estimate only
for expectation one.  Problem 294 needs the same finite Fourier argument at
an arbitrary lattice point `z / Q`.  This file records the target-dependent
phase cancellation and keeps the eventual major/minor estimates uniform in
the Bernoulli probabilities.
-/

open Filter Finset Real
open scoped BigOperators Topology

namespace Erdos294.PrescribedLocalLimit

open Erdos297
open Erdos297.ActiveLcm Erdos297.AuxiliaryEventual
open Erdos297.EntropyTypical Erdos297.FiniteHoeffding
open Erdos297.GoodFactorization Erdos297.GoodSetDensity
open Erdos297.LogisticNormalization Erdos297.MajorArc Erdos297.MinorArc
open Erdos297.MinorEventual Erdos297.NearbyMultiple
open Erdos297.SupplyNumerics Erdos297.WeightedFourier
open Erdos297.LocalLimit

noncomputable section

attribute [local instance] Classical.propDecidable

/-- The character at `z` cancels the linear reciprocal phase when the
expectation is `z / Q`. -/
lemma expectationPhase_reciprocalAngle_of_mean
    {Q z : ℕ} [NeZero Q] (I : Finset ℕ) (p : ℕ → ℝ) (h : ZMod Q)
    (hpos : ∀ n ∈ I, 0 < n)
    (hmean : ∑ n ∈ I, p n / n = (z : ℝ) / Q) :
    ZMod.stdAddChar (h * (z : ZMod Q)) =
      Complex.exp (((-(∑ n ∈ I, p n * reciprocalAngle h n) : ℝ) : ℂ) *
        Complex.I) := by
  have hsum :
      -(∑ n ∈ I, p n * reciprocalAngle h n) =
        (h.valMinAbs : ℝ) * (2 * Real.pi) * ((z : ℝ) / Q) := by
    rw [show (∑ n ∈ I, p n * reciprocalAngle h n) =
        -(2 * Real.pi * (h.valMinAbs : ℝ)) * ∑ n ∈ I, p n / n by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hnI
      dsimp [reciprocalAngle]
      have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (hpos n hnI).ne'
      field_simp [hn0]]
    rw [hmean]
    ring
  have harg :
      h * (z : ZMod Q) =
        ((h.valMinAbs * (z : ℤ) : ℤ) : ZMod Q) := by
    rw [← h.coe_valMinAbs]
    push_cast
    rfl
  rw [harg, ZMod.stdAddChar_coe, hsum]
  apply congrArg Complex.exp
  have hQpos : (0 : ℝ) < Q := by
    exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne Q)
  push_cast
  field_simp [hQpos.ne']

/-- Prescribed-target version of the finite reciprocal major-arc theorem. -/
theorem reciprocal_majorArc_lower_of_budgets_target
    {Q M H z : ℕ} [NeZero Q] (hHM : H ≤ M / 2)
    (A : Finset ℕ) (p : ℕ → ℝ)
    (hApos : ∀ n ∈ A, 0 < n) (hAdvd : ∀ n ∈ A, n ∣ Q)
    (hp0 : ∀ n ∈ A, 0 ≤ p n) (hp1 : ∀ n ∈ A, p n ≤ 1)
    (hmean : ∑ n ∈ A, p n / n = (z : ℝ) / Q)
    (hcentralAngle : ∀ h ∈ centralFrequencies Q H, ∀ n ∈ A,
      |reciprocalAngle h n| ≤ 1)
    (hcentralCubic : ∀ h ∈ centralFrequencies Q H,
      2 * ∑ n ∈ A, |reciprocalAngle h n| ^ 3 ≤ (1 / 7 : ℝ))
    (hintermediate :
      ∑ h ∈ intermediateFrequencies Q M H,
        Real.exp (-(8 * ∑ n ∈ A, p n * (1 - p n) *
          circleDistance (reciprocalAngle h n / (2 * Real.pi)) ^ 2)) ≤
        (1 / 4 : ℝ)) :
    (3 / 4 : ℝ) ≤ 1 +
      (MajorArc.fourierBlock (majorFrequencies Q M) A
        (fun n ↦ (Q / n : ZMod Q)) p (z : ZMod Q)).re := by
  apply weighted_majorArc_lower
    (majorFrequencies Q M) (centralFrequencies Q H)
    (intermediateFrequencies Q M H) A
    (fun n ↦ (Q / n : ZMod Q)) p (z : ZMod Q)
    (fun h n ↦ reciprocalAngle h n)
  · exact (central_union_intermediate Q M H hHM).symm
  · exact disjoint_central_intermediate Q M H
  · exact hp0
  · exact hp1
  · intro h hh n hn
    exact stdAddChar_clearedReciprocal (hApos n hn) (hAdvd n hn) h
  · intro h hh
    exact expectationPhase_reciprocalAngle_of_mean A p h hApos hmean
  · exact hcentralAngle
  · exact hcentralCubic
  · exact hintermediate

/-! ## Eventual major-arc numerical budgets -/

lemma central_cubic_power_bound
    {x m h a : ℝ} (hx : 1 ≤ x)
    (hm : x ^ ((19 : ℝ) / 20) ≤ m)
    (hh : 0 ≤ h) (hH : h ≤ x ^ ((3 : ℝ) / 5))
    (ha0 : 0 ≤ a) (ha : a ≤ x) :
    2 * a * (2 * Real.pi * h / m) ^ 3 ≤
      16 * Real.pi ^ 3 * x ^ (-((1 : ℝ) / 20)) := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hmpos : 0 < m := (Real.rpow_pos_of_pos hxp _).trans_le hm
  have hnum : 2 * Real.pi * h ≤ 2 * Real.pi * x ^ ((3 : ℝ) / 5) :=
    mul_le_mul_of_nonneg_left hH (by positivity)
  have hfrac : 2 * Real.pi * h / m ≤
      2 * Real.pi * x ^ ((3 : ℝ) / 5) / x ^ ((19 : ℝ) / 20) := by
    calc
      2 * Real.pi * h / m ≤ 2 * Real.pi * x ^ ((3 : ℝ) / 5) / m :=
        div_le_div_of_nonneg_right hnum hmpos.le
      _ ≤ 2 * Real.pi * x ^ ((3 : ℝ) / 5) / x ^ ((19 : ℝ) / 20) :=
        div_le_div_of_nonneg_left (by positivity)
          (Real.rpow_pos_of_pos hxp _) hm
  have hratio : x ^ ((3 : ℝ) / 5) / x ^ ((19 : ℝ) / 20) =
      x ^ (-((7 : ℝ) / 20)) := by
    rw [← Real.rpow_sub hxp]
    congr 1
    norm_num
  calc
    2 * a * (2 * Real.pi * h / m) ^ 3 ≤
        2 * x * (2 * Real.pi * x ^ ((3 : ℝ) / 5) /
          x ^ ((19 : ℝ) / 20)) ^ 3 := by gcongr
    _ = 2 * x * (2 * Real.pi * x ^ (-((7 : ℝ) / 20))) ^ 3 := by
      rw [show 2 * Real.pi * x ^ ((3 : ℝ) / 5) / x ^ ((19 : ℝ) / 20) =
          2 * Real.pi * (x ^ ((3 : ℝ) / 5) / x ^ ((19 : ℝ) / 20)) by ring,
        hratio]
    _ = 16 * Real.pi ^ 3 * (x * (x ^ (-((7 : ℝ) / 20))) ^ 3) := by ring
    _ = 16 * Real.pi ^ 3 * x ^ (-((1 : ℝ) / 20)) := by
      congr 1
      calc
        x * (x ^ (-((7 : ℝ) / 20))) ^ 3 =
            x ^ (1 : ℝ) * x ^ (-((7 : ℝ) / 20) * 3) := by
          rw [Real.rpow_one, ← Real.rpow_mul_natCast hx0]
          norm_num
        _ = x ^ ((1 : ℝ) + -((7 : ℝ) / 20) * 3) := by rw [Real.rpow_add hxp]
        _ = x ^ (-((1 : ℝ) / 20)) := by norm_num

lemma intermediate_exponent_power_bound
    {x h delta a : ℝ} (hx : 1 ≤ x)
    (hH : x ^ ((3 : ℝ) / 5) / 2 ≤ h)
    (hdelta : x ^ (-((1 : ℝ) / 100)) ≤ delta)
    (ha : x ^ ((19 : ℝ) / 20) ≤ a) :
    x ^ ((7 : ℝ) / 50) ≤ 4 * delta * a * h ^ 2 / x ^ 2 := by
  have hx0 : 0 ≤ x := zero_le_one.trans hx
  have hxp : 0 < x := zero_lt_one.trans_le hx
  have hxne : x ≠ 0 := hxp.ne'
  have hdelta0 : 0 ≤ delta := (Real.rpow_nonneg hx0 _).trans hdelta
  have ha0 : 0 ≤ a := (Real.rpow_nonneg hx0 _).trans ha
  have hh0 : 0 ≤ h :=
    (div_nonneg (Real.rpow_nonneg hx0 _) (by norm_num)).trans hH
  have hH2 : x ^ ((6 : ℝ) / 5) / 4 ≤ h ^ 2 := by
    calc
      x ^ ((6 : ℝ) / 5) / 4 = (x ^ ((3 : ℝ) / 5) / 2) ^ 2 := by
        rw [div_pow, ← Real.rpow_mul_natCast hx0]
        norm_num
      _ ≤ h ^ 2 := pow_le_pow_left₀ (by positivity) hH 2
  have hprod :
      x ^ (-((1 : ℝ) / 100)) * x ^ ((19 : ℝ) / 20) *
          (x ^ ((6 : ℝ) / 5) / 4) ≤ delta * a * h ^ 2 := by gcongr
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
            x ^ 2) / 4 := by rw [Real.rpow_add hxp, Real.rpow_add hxp]
      _ = x ^ (-((1 : ℝ) / 100) + (19 : ℝ) / 20 + (6 : ℝ) / 5 - 2) /
            4 := by
        rw [← Real.rpow_sub_natCast hxne]
        norm_num
      _ = x ^ ((7 : ℝ) / 50) / 4 := by norm_num
  have hmain : x ^ ((7 : ℝ) / 50) / 4 ≤ delta * a * h ^ 2 / x ^ 2 := by
    rw [← hid]
    exact div_le_div_of_nonneg_right hprod (sq_nonneg x)
  calc
    x ^ ((7 : ℝ) / 50) = 4 * (x ^ ((7 : ℝ) / 50) / 4) := by ring
    _ ≤ 4 * (delta * a * h ^ 2 / x ^ 2) :=
      mul_le_mul_of_nonneg_left hmain (by norm_num)
    _ = 4 * delta * a * h ^ 2 / x ^ 2 := by ring

lemma tendsto_intermediate_majorant :
    Tendsto (fun N : ℕ ↦
      2 * (N : ℝ) * Real.exp (-((N : ℝ) ^ ((1 : ℝ) / 10))))
      atTop (nhds 0) := by
  have hy : Tendsto (fun N : ℕ ↦ (N : ℝ) ^ ((1 : ℝ) / 10)) atTop atTop :=
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

private theorem eventually_central_budgets :
    ∀ᶠ N : ℕ in atTop,
      2 * Real.pi * (centralCutoff N : ℝ) ≤ (Erdos297.M N : ℝ) ∧
      2 * ((goodSet N).card : ℝ) *
        (2 * Real.pi * (centralCutoff N : ℝ) / (Erdos297.M N : ℝ)) ^ 3 ≤
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
    eventually_nineteenTwentiethPower_le_M,
    eventually_ge_atTop (1 : ℕ)] with N hconstN hsmall hMlower hN
  have hx : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hxpos : (0 : ℝ) < N := zero_lt_one.trans_le hx
  have hcut := centralCutoff_le_rpow N
  have hA : goodSet N ⊆ Icc 1 N := by
    simpa [goodSet, sourceGoodDenominators] using
      sourceGoodDenominators_subset_denominators (N := N) (by
        have hmone : (1 : ℝ) ≤ Erdos297.M N :=
          (Real.one_le_rpow hx (by norm_num)).trans hMlower
        exact_mod_cast hmone)
  have hcardNat : (goodSet N).card ≤ N := by
    calc
      (goodSet N).card ≤ (Icc 1 N).card := card_le_card hA
      _ = N := by simp
  have hcard : ((goodSet N).card : ℝ) ≤ (N : ℝ) := by exact_mod_cast hcardNat
  constructor
  · calc
      2 * Real.pi * (centralCutoff N : ℝ) ≤
          2 * Real.pi * (N : ℝ) ^ ((3 : ℝ) / 5) :=
        mul_le_mul_of_nonneg_left hcut (by positivity)
      _ ≤ (N : ℝ) ^ ((7 : ℝ) / 20) * (N : ℝ) ^ ((3 : ℝ) / 5) :=
        mul_le_mul_of_nonneg_right hconstN (Real.rpow_nonneg (zero_le_one.trans hx) _)
      _ = (N : ℝ) ^ ((19 : ℝ) / 20) := by
        rw [← Real.rpow_add hxpos]
        norm_num
      _ ≤ (Erdos297.M N : ℝ) := hMlower
  · exact (central_cubic_power_bound hx hMlower (Nat.cast_nonneg _)
      hcut (Nat.cast_nonneg _) hcard).trans hsmall

private theorem eventually_intermediate_budget :
    ∀ᶠ N : ℕ in atTop,
      (((Erdos297.M N + 1 : ℕ) : ℝ) *
        Real.exp (-(4 * (logLogScale N)⁻¹ * ((goodSet N).card : ℝ) *
          (centralCutoff N : ℝ) ^ 2 / (N : ℝ) ^ 2)) ≤ (1 / 4 : ℝ)) := by
  have hsmall : ∀ᶠ N : ℕ in atTop,
      2 * (N : ℝ) * Real.exp (-((N : ℝ) ^ ((1 : ℝ) / 10))) ≤ (1 / 4 : ℝ) :=
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
  have hpower : (N : ℝ) ^ ((1 : ℝ) / 10) ≤ (N : ℝ) ^ ((7 : ℝ) / 50) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hexp : Real.exp (-(4 * (logLogScale N)⁻¹ *
        ((goodSet N).card : ℝ) * (centralCutoff N : ℝ) ^ 2 /
          (N : ℝ) ^ 2)) ≤ Real.exp (-((N : ℝ) ^ ((1 : ℝ) / 10))) :=
    Real.exp_le_exp.mpr (neg_le_neg (hpower.trans hexponent))
  have hMleNreal : (Erdos297.M N : ℝ) ≤ (N : ℝ) := by
    have hN0 : (0 : ℝ) ≤ N := by positivity
    linarith [hchain.2.2]
  have hpref : (((Erdos297.M N + 1 : ℕ) : ℝ)) ≤ 2 * (N : ℝ) := by
    push_cast
    linarith
  calc
    ((Erdos297.M N + 1 : ℕ) : ℝ) *
        Real.exp (-(4 * (logLogScale N)⁻¹ * ((goodSet N).card : ℝ) *
          (centralCutoff N : ℝ) ^ 2 / (N : ℝ) ^ 2)) ≤
        2 * (N : ℝ) * Real.exp (-((N : ℝ) ^ ((1 : ℝ) / 10))) := by
      exact mul_le_mul hpref hexp (Real.exp_nonneg _) (by positivity)
    _ ≤ 1 / 4 := hsmallN

/-- The prescribed major block with its canonical active-LCM instance. -/
def prescribedMajorBlock (N : ℕ) (p : ℕ → ℝ) (z : ℕ) : ℂ :=
  let A := goodSet N
  let Q := activeLcm A
  letI : NeZero Q := ⟨activeLcm_ne_zero A⟩
  MajorArc.fourierBlock (majorFrequencies Q (Erdos297.M N)) A
    (fun n ↦ (Q / n : ZMod Q)) p (z : ZMod Q)

/-- Uniform prescribed-target major-arc lower bound. -/
theorem eventually_prescribed_majorArc_lower :
    ∀ᶠ N : ℕ in atTop, ∀ (p : ℕ → ℝ) (z : ℕ),
      (∀ n ∈ goodSet N, 1 / logLogScale N ≤ p n) →
      (∀ n ∈ goodSet N, p n ≤ 1 / 2) →
      (∑ n ∈ goodSet N, p n / n =
        (z : ℝ) / activeLcm (goodSet N)) →
      (3 / 4 : ℝ) ≤ 1 + (prescribedMajorBlock N p z).re := by
  filter_upwards [eventually_centralCutoff_le_half_M,
    eventually_central_budgets, eventually_intermediate_budget,
    eventually_sourceGoodDenominators_pos,
    eventually_one_le_M_and_M_le_N, eventually_pos_scales]
      with N hHM hcentral hintermediate hApos hM hscales
  intro p z hpLower hpUpper hmean
  let A := goodSet N
  let Q := activeLcm A
  letI : NeZero Q := ⟨activeLcm_ne_zero A⟩
  have hAinterval : A ⊆ Icc (Erdos297.M N) N := by
    simpa [A, goodSet, sourceGoodDenominators] using
      sourceGoodDenominators_subset_Icc N
  have hApos' : ∀ n ∈ A, 0 < n := by
    simpa [A, goodSet, sourceGoodDenominators] using hApos
  have hAdvd : ∀ n ∈ A, n ∣ Q := fun n hn ↦
    dvd_activeLcm_of_mem_of_pos hApos' hn
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hscales.2.2.1
  have hp0 : ∀ n ∈ A, 0 ≤ p n := by
    intro n hn
    exact (one_div_pos.mpr hLLpos).le.trans
      (hpLower n (by simpa [A] using hn))
  have hp1 : ∀ n ∈ A, p n ≤ 1 := by
    intro n hn
    exact (hpUpper n (by simpa [A] using hn)).trans (by norm_num)
  have hdeltaNonneg : 0 ≤ (logLogScale N)⁻¹ := inv_nonneg.mpr hLLpos.le
  have hcentralFinite := reciprocal_central_budgets
    (Q := Q) (M := Erdos297.M N) (N := N) (H := centralCutoff N)
    hM.1 A hAinterval hcentral.1 hcentral.2
  have hintermediateFinite := reciprocal_intermediate_budget
    (Q := Q) (M := Erdos297.M N) (N := N) (H := centralCutoff N)
    hM.1 hM.2 A hAinterval p (logLogScale N)⁻¹ hdeltaNonneg
    (fun n hn ↦ by simpa [one_div, A] using hpLower n (by simpa [A] using hn))
    (fun n hn ↦ by simpa [A] using hpUpper n (by simpa [A] using hn))
    hintermediate
  have hresult := reciprocal_majorArc_lower_of_budgets_target
    (Q := Q) (M := Erdos297.M N) (H := centralCutoff N) (z := z)
    hHM A p hApos' hAdvd hp0 hp1 (by simpa [A, Q] using hmean)
    hcentralFinite.1 hcentralFinite.2 hintermediateFinite
  simpa [prescribedMajorBlock, A, Q] using hresult

/-! ## Uniform minor arc -/

/-- The prescribed minor block with its canonical active-LCM instance. -/
def prescribedMinorBlock (N : ℕ) (p : ℕ → ℝ) (z : ℕ) : ℂ :=
  let A := goodSet N
  let Q := activeLcm A
  letI : NeZero Q := ⟨activeLcm_ne_zero A⟩
  MajorArc.fourierBlock (minorFrequencies Q (Erdos297.M N)) A
    (fun n ↦ (Q / n : ZMod Q)) p (z : ZMod Q)

/-- The minor-arc estimate is uniform over all probabilities in the source
interval `[1/log log N,1/2]` and over every target residue. -/
theorem eventually_prescribed_minorArc_bound :
    ∀ᶠ N : ℕ in atTop, ∀ (p : ℕ → ℝ) (z : ℕ),
      (∀ n ∈ goodSet N, 1 / logLogScale N ≤ p n) →
      (∀ n ∈ goodSet N, p n ≤ 1 / 2) →
      ‖prescribedMinorBlock N p z‖ ≤ 1 / 4 := by
  filter_upwards [AuxiliaryEventual.eventually_nearbyMultiplePair,
      eventually_minorDecayRate, eventually_one_le_M_and_M_le_N,
      eventually_two_mul_KSafe_lt_M,
      GoodSetDensity.eventually_sourceGoodDenominators_card_ge,
      eventually_pos_scales, eventually_ge_atTop (8 : ℕ)]
      with N hnearSupply hrate hM htwice hcard hscales hNlarge
  intro p z hpLower hpUpper
  let A : Finset ℕ := goodSet N
  let Q : ℕ := activeLcm A
  letI : NeZero Q := ⟨activeLcm_ne_zero A⟩
  let H : Finset (ZMod Q) := minorFrequencies Q (Erdos297.M N)
  let key : ZMod Q → Finset ℕ := fun h ↦
    goodModuliOn (activePrimePowers A) A h.valMinAbs (KSafe N)
      (minorThreshold N)
  let f : ZMod Q → ℝ := fun h ↦
    ‖coefficient A (fun n ↦ (Q / n : ZMod Q)) p h‖
  let decay : ℕ → ℝ := fun s ↦ 1 / (N : ℝ) ^ (10 * s)
  have hAsub : A ⊆ goodDenominators N (Erdos297.M N) (S N) := by
    intro n hn
    simpa [A, goodSet] using hn
  have hApos : ∀ n ∈ A, 0 < n := fun n hn ↦
    goodDenominator_pos hM.1 (hAsub hn)
  have hdiv : ∀ n ∈ A, n ∣ Q := fun n hn ↦ by
    simpa [Q] using dvd_activeLcm_of_mem_of_pos hApos hn
  have hKleN : KSafe N ≤ N := by omega
  have hKleHalfM : KSafe N ≤ Erdos297.M N / 2 := by omega
  have hAnonempty : A.Nonempty := by
    rw [← Finset.card_ne_zero]
    intro hzero
    have hcardZero : ((A.card : ℕ) : ℝ) = 0 := by simp [hzero]
    have hcard' : ((89 : ℝ) / 100) * N ≤ (A.card : ℝ) := by
      simpa [A, goodSet, GoodSetDensity.sourceGoodDenominators] using hcard
    have hNposR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    rw [hcardZero] at hcard'
    nlinarith
  obtain ⟨n₀, hn₀A⟩ := hAnonempty
  have hQlarge : 2 * KSafe N < Q := by
    have hn₀Q : n₀ ∣ Q := hdiv n₀ hn₀A
    have hn₀leQ : n₀ ≤ Q := Nat.le_of_dvd (activeLcm_pos A) hn₀Q
    have hMn₀ : Erdos297.M N ≤ n₀ :=
      (mem_goodDenominators.mp (hAsub hn₀A)).1
    omega
  have hnear : ∀ h ∈ H,
      nearbyMultiplePair (KSafe N) ((key h).lcm id) h.valMinAbs := by
    intro h hh
    simpa [A, key] using hnearSupply h.valMinAbs
  have hproper : ∀ h ∈ H, key h ≠ activePrimePowers A := by
    intro h hh heq
    have hnearFull : nearbyMultiplePair (KSafe N) Q h.valMinAbs := by
      simpa [Q, activeLcm, heq] using hnear h hh
    exact (not_nearby_activeLcm_of_minor hQlarge hKleHalfM
      (by simpa [H] using hh)) hnearFull
  rcases hscales with ⟨hNposR, hLone, hLLone, hLLL⟩
  have hNpos : 0 < N := by exact_mod_cast hNposR
  have hLL : 0 < logLogScale N := zero_lt_one.trans hLLone
  have hF : 0 < factorBound N := by
    rw [factorBound]
    apply Nat.floor_pos.mpr
    have hbound : (1 : ℝ) ≤ 10 * logLogScale N := by nlinarith
    simpa [logLogScale, logScale] using hbound
  have hpoint : ∀ h ∈ H,
      f h ≤ decay (activePrimePowers A \ key h).card := by
    intro h hh
    dsimp [f, decay, key]
    exact coefficient_norm_le_power hM.1 hAsub
      (activePrimePowers_subset_smoothPrimePowers hM.1 hAsub)
      (fun n hn ↦ hpLower n (by simpa [A] using hn))
      (fun n hn ↦ hpUpper n (by simpa [A] using hn))
      (le_refl (factorBound N)) hF (by positivity) hdiv hNpos hrate h
  have hsum : ∑ h ∈ H, f h ≤
      ∑ D ∈ (activePrimePowers A).powerset.erase (activePrimePowers A),
        (((2 * KSafe N + 1) *
          (N ^ (activePrimePowers A \ D).card + 1) : ℕ) : ℝ) *
            decay (activePrimePowers A \ D).card := by
    exact active_minor_sum_le_powerset hM.1 hAsub key f decay
      (fun s ↦ by positivity)
      (fun h hh ↦ by
        simpa [key, goodModuliOn] using
          (Finset.filter_subset (activePrimePowers A)
            (fun q ↦ (farSet A h.valMinAbs (KSafe N) q).card <
              minorThreshold N)))
      hproper hnear hpoint
  have hscalar :
      ∑ D ∈ (activePrimePowers A).powerset.erase (activePrimePowers A),
        (((2 * KSafe N + 1) *
          (N ^ (activePrimePowers A \ D).card + 1) : ℕ) : ℝ) *
            decay (activePrimePowers A \ D).card ≤ 1 / 4 := by
    simpa [decay] using scalar_minor_sum_le_quarter
      (U := activePrimePowers A) hNlarge hKleN
      (activePrimePowers_card_le hM.1 hAsub)
  have hblock :
      ‖MajorArc.fourierBlock H A (fun n ↦ (Q / n : ZMod Q)) p
        (z : ZMod Q)‖ ≤ ∑ h ∈ H, f h := by
    simpa [MajorArc.fourierBlock, A, Q, H, f] using
      norm_fourierBlock_le_sum H A p (z : ZMod Q)
  simpa [prescribedMinorBlock, A, Q, H] using
    hblock.trans (hsum.trans hscalar)

/-! ## Exact prescribed atom -/

/-- The complete prescribed local limit theorem, uniform in the probability
profile and target residue. -/
theorem eventually_prescribed_exactReciprocalMass :
    ∀ᶠ N : ℕ in atTop, ∀ (p : ℕ → ℝ) (z : ℕ),
      (∀ n ∈ goodSet N, 1 / logLogScale N ≤ p n) →
      (∀ n ∈ goodSet N, p n ≤ 1 / 2) →
      (∑ n ∈ goodSet N, p n / n =
        (z : ℝ) / activeLcm (goodSet N)) →
      1 / (4 * (activeLcm (goodSet N) : ℝ)) ≤
        exactReciprocalMass (goodSet N) p
          (z / (activeLcm (goodSet N) : ℚ)) := by
  filter_upwards [eventually_one_le_M,
    eventually_abs_reciprocal_sum_sub_mean_tail_le_inv_four_smoothLcm,
    eventually_prescribed_majorArc_lower,
    eventually_prescribed_minorArc_bound, eventually_pos_scales]
      with N hM htail hmajor hminor hscales
  intro p z hpLower hpUpper hmean
  let I := goodSet N
  let Q := activeLcm I
  letI : NeZero Q := ⟨activeLcm_ne_zero I⟩
  have hI : I ⊆ goodDenominators N (Erdos297.M N) (S N) := by
    simpa [I, goodSet]
  have hIcc : I ⊆ Icc (Erdos297.M N) N :=
    hI.trans (goodDenominators_subset_Icc N (Erdos297.M N) (S N))
  have hIpos : ∀ n ∈ I, 0 < n := fun n hn ↦
    goodDenominator_pos hM (hI hn)
  have hIdiv : ∀ n ∈ I, n ∣ Q := fun n hn ↦ by
    simpa [Q] using dvd_activeLcm_of_mem_of_pos hIpos hn
  have hLLpos : 0 < logLogScale N := zero_lt_one.trans hscales.2.2.1
  have hp0 : ∀ n ∈ I, 0 ≤ p n := by
    intro n hn
    exact (one_div_pos.mpr hLLpos).le.trans
      (hpLower n (by simpa [I] using hn))
  have hp1 : ∀ n ∈ I, p n ≤ 1 := by
    intro n hn
    exact (hpUpper n (by simpa [I] using hn)).trans (by norm_num)
  have hmean' : subsetMean I p (fun n : ℕ ↦ (n : ℝ)⁻¹) =
      (z : ℝ) / Q := by
    simpa [I, Q, subsetMean, div_eq_mul_inv] using hmean
  have htailFull := htail I p hIcc hp0 hp1
  have htailActive :
      offLatticeMass I (fun n ↦ Q / n) p z Q ≤ 1 / (4 * (Q : ℝ)) := by
    have hbridge := offLatticeMass_le_reciprocalEventMass_of_commonMultiple
      (activeLcm_pos I) I hIpos hIdiv p hp0 hp1 (z := z)
    have htoFull :
        offLatticeMass I (fun n ↦ Q / n) p z Q ≤
          1 / (4 * (smoothLcm (S N) : ℝ)) := by
      refine hbridge.trans ?_
      simpa [hmean', Q] using htailFull
    refine htoFull.trans ?_
    apply one_div_le_one_div_of_le
    · exact mul_pos (by norm_num) (by exact_mod_cast activeLcm_pos I)
    · exact mul_le_mul_of_nonneg_left
        (by exact_mod_cast activeLcm_le_smoothLcm hM hI) (by norm_num)
  have hmajor' : (3 / 4 : ℝ) ≤ 1 +
      (MajorArc.fourierBlock (majorFrequencies Q (Erdos297.M N)) I
        (fun n ↦ (Q / n : ZMod Q)) p (z : ZMod Q)).re := by
    simpa [prescribedMajorBlock, I, Q] using
      hmajor p z hpLower hpUpper hmean
  have hminor' :
      ‖MajorArc.fourierBlock (minorFrequencies Q (Erdos297.M N)) I
        (fun n ↦ (Q / n : ZMod Q)) p (z : ZMod Q)‖ ≤ 1 / 4 := by
    simpa [prescribedMinorBlock, I, Q] using
      hminor p z hpLower hpUpper
  have hresult := liuSawhney_proposition_3_2 (activeLcm_pos I)
    (majorFrequencies Q (Erdos297.M N))
    (minorFrequencies Q (Erdos297.M N)) I hIpos hIdiv p hp0 hp1
    (disjoint_major_minor Q (Erdos297.M N))
    (major_union_minor Q (Erdos297.M N))
    (by simpa [LocalLimit.fourierBlock, MajorArc.fourierBlock] using hmajor')
    (by simpa [LocalLimit.fourierBlock, MajorArc.fourierBlock] using hminor')
    htailActive
  simpa [I, Q] using hresult

end

end Erdos294.PrescribedLocalLimit

#print axioms Erdos294.PrescribedLocalLimit.eventually_prescribed_minorArc_bound
