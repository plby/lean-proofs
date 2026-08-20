/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.EndpointBandChoice
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The Page-excluded endpoint estimate on a power scale

We specialize the finite endpoint mean to `Q = n`, `T = n^3`, and
`x = n^L`.  A sufficiently large fixed exponent absorbs the middle zero
bands, while ordinary logarithmic asymptotics absorb the explicit-formula
and far-zero errors.  The result is the small total endpoint mass used in
the nonexceptional branch of Ford--Luca--Pomerance.
-/

namespace Erdos48

open Filter
open scoped Topology
open BoundedGaps.Maynard

noncomputable section

theorem endpointPowerScale_mul_le_pow_five {n : ℕ} (hn : 2 ≤ n) :
    n * (n ^ 3 + 2) ≤ n ^ 5 := by
  have hn3 : 2 ≤ n ^ 3 := by
    calc 2 ≤ n := hn
      _ ≤ n ^ 3 := by
        exact Nat.le_pow (by omega)
  calc
    n * (n ^ 3 + 2) ≤ n * (n ^ 3 + n ^ 3) := by gcongr
    _ = 2 * n ^ 4 := by ring
    _ ≤ n * n ^ 4 := by gcongr
    _ = n ^ 5 := by ring

theorem endpointPowerScale_log_le_five_log {n : ℕ} (hn : 2 ≤ n) :
    Real.log ((n : ℝ) * ((n ^ 3 : ℕ) + 2)) ≤
      5 * Real.log (n : ℝ) := by
  have hpos : (0 : ℝ) < (n : ℝ) * ((n ^ 3 : ℕ) + 2) := by positivity
  have hle : (n : ℝ) * ((n ^ 3 : ℕ) + 2) ≤ (n : ℝ) ^ 5 := by
    exact_mod_cast endpointPowerScale_mul_le_pow_five hn
  calc
    Real.log ((n : ℝ) * ((n ^ 3 : ℕ) + 2)) ≤
        Real.log ((n : ℝ) ^ 5) := Real.log_le_log hpos hle
    _ = 5 * Real.log (n : ℝ) := by rw [Real.log_pow]; norm_num

theorem log_natCast_pow (n L : ℕ) :
    Real.log ((n ^ L : ℕ) : ℝ) = (L : ℝ) * Real.log (n : ℝ) := by
  rw [Nat.cast_pow, Real.log_pow]

theorem natPow_rpow_fifteen_sixteen_le_div_four
    {n L : ℕ} (hn : 1 ≤ n) (hL : 64 ≤ L) :
    (((n ^ L : ℕ) : ℝ) ^ (15 / 16 : ℝ)) ≤
      ((n ^ L : ℕ) : ℝ) / (n : ℝ) ^ 4 := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := zero_lt_one.trans_le hnR
  have hexp : (L : ℝ) * (15 / 16 : ℝ) ≤ (L : ℝ) - 4 := by
    have hLR : (64 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  calc
    (((n ^ L : ℕ) : ℝ) ^ (15 / 16 : ℝ)) =
        ((n : ℝ) ^ (L : ℝ)) ^ (15 / 16 : ℝ) := by
      rw [Nat.cast_pow, Real.rpow_natCast]
    _ = (n : ℝ) ^ ((L : ℝ) * (15 / 16 : ℝ)) := by
      exact (Real.rpow_mul (zero_le_one.trans hnR) _ _).symm
    _ ≤ (n : ℝ) ^ ((L : ℝ) - 4) :=
      Real.rpow_le_rpow_of_exponent_le hnR hexp
    _ = (n : ℝ) ^ (L : ℝ) / (n : ℝ) ^ (4 : ℝ) := by
      rw [Real.rpow_sub hnpos]
    _ = ((n ^ L : ℕ) : ℝ) / (n : ℝ) ^ 4 := by
      norm_cast

theorem tendsto_log_sq_div_nat :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) ^ 2 / (n : ℝ))
      atTop (nhds 0) := by
  simpa [Function.comp_def, Real.rpow_one, Real.rpow_natCast] using
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 1)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

theorem tendsto_log_sq_div_nat_sq :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2)
      atTop (nhds 0) := by
  simpa [Function.comp_def, Real.rpow_natCast] using
    (isLittleO_log_rpow_rpow_atTop (2 : ℝ) (by norm_num : (0 : ℝ) < 2)).tendsto_div_nhds_zero.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

theorem eventually_twenty_log_add_const_le_self (D : ℝ) :
    ∀ᶠ y : ℝ in atTop, 20 * Real.log y + D ≤ y := by
  have hlog := Real.isLittleO_log_id_atTop.bound
    (show (0 : ℝ) < 1 / 40 by norm_num)
  filter_upwards [hlog, eventually_ge_atTop (max 1 (2 * max D 0))]
      with y hylog hy
  have hy1 : 1 ≤ y := (le_max_left _ _).trans hy
  have hy0 : 0 ≤ y := zero_le_one.trans hy1
  have hlog0 : 0 ≤ Real.log y := Real.log_nonneg hy1
  simp only [id] at hylog
  rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hy0] at hylog
  have hD : D ≤ y / 2 := by
    have htwo : 2 * max D 0 ≤ y := (le_max_right _ _).trans hy
    nlinarith [le_max_left D 0]
  nlinarith

theorem endpointPowerScale_explicitError_eq
    {n L Ke : ℕ} (hn : 0 < n) :
    (n : ℝ) ^ 2 *
        ((Ke : ℝ) * dirichletExplicitFormulaErrorScale
          ((n ^ L : ℕ) : ℝ) n ((n ^ 3 : ℕ) : ℝ)) =
      ((n ^ L : ℕ) : ℝ) *
        ((Ke : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 2 *
          (Real.log (n : ℝ) ^ 2 / (n : ℝ))) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hprod : ((n ^ L : ℕ) : ℝ) * (n : ℝ) =
      ((n ^ (L + 1) : ℕ) : ℝ) := by
    norm_cast
  unfold dirichletExplicitFormulaErrorScale
  rw [hprod, log_natCast_pow]
  norm_num only [Nat.cast_pow, Nat.cast_add, Nat.cast_one]
  field_simp

theorem endpointPowerScale_farTerm_le
    {n L J Afar : ℕ} {eta : ℝ}
    (hn : 2 ≤ n) (hL : 64 ≤ L)
    (hsaving : 1 / 16 ≤ (((J + 1 : ℕ) : ℝ) * eta)) :
    (n : ℝ) ^ 2 *
        (96 * (Afar : ℝ) *
          (((n ^ L : ℕ) : ℝ) ^
            (1 - (((J + 1 : ℕ) : ℝ) * eta))) *
          Real.log ((n : ℝ) * ((n ^ 3 : ℕ) + 2)) ^ 2) ≤
      ((n ^ L : ℕ) : ℝ) *
        ((96 * (Afar : ℝ) * 25) *
          (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2)) := by
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hlogn : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
  have hlogB := endpointPowerScale_log_le_five_log hn
  have hlogB0 : 0 ≤ Real.log ((n : ℝ) * ((n ^ 3 : ℕ) + 2)) := by
    apply Real.log_nonneg
    have hnCast : (2 : ℝ) ≤ n := by exact_mod_cast hn
    nlinarith [show (0 : ℝ) ≤ ((n ^ 3 : ℕ) : ℝ) by positivity]
  have hlogSq :
      Real.log ((n : ℝ) * ((n ^ 3 : ℕ) + 2)) ^ 2 ≤
        25 * Real.log (n : ℝ) ^ 2 := by
    nlinarith [sq_nonneg
      (5 * Real.log (n : ℝ) -
        Real.log ((n : ℝ) * ((n ^ 3 : ℕ) + 2)))]
  have hpow :
      (((n ^ L : ℕ) : ℝ) ^
          (1 - (((J + 1 : ℕ) : ℝ) * eta))) ≤
        (((n ^ L : ℕ) : ℝ) ^ (15 / 16 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le
    · have hone : 1 ≤ n ^ L := Nat.one_le_pow L n (by omega)
      exact_mod_cast hone
    · linarith
  have hpowDiv := natPow_rpow_fifteen_sixteen_le_div_four
    (show 1 ≤ n by omega) hL
  have hnpos : (0 : ℝ) < n := by positivity
  calc
    (n : ℝ) ^ 2 *
        (96 * (Afar : ℝ) *
          (((n ^ L : ℕ) : ℝ) ^
            (1 - (((J + 1 : ℕ) : ℝ) * eta))) *
          Real.log ((n : ℝ) * ((n ^ 3 : ℕ) + 2)) ^ 2) ≤
      (n : ℝ) ^ 2 *
        (96 * (Afar : ℝ) *
          (((n ^ L : ℕ) : ℝ) / (n : ℝ) ^ 4) *
          (25 * Real.log (n : ℝ) ^ 2)) := by
      gcongr
      exact hpow.trans hpowDiv
    _ = ((n ^ L : ℕ) : ℝ) *
        ((96 * (Afar : ℝ) * 25) *
          (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2)) := by
      field_simp

private theorem div_five_div_four (x y : ℝ) :
    (x * y / 5) / 4 = x * y / 20 := by ring

private theorem three_thirds_mul (x y : ℝ) :
    (x / 3) * y + (x / 3) * y + (x / 3) * y = x * y := by ring

private theorem endpointMiddleExponent_le
    {c eta logB logx lambda lower : ℝ}
    (hB : eta * logB = lambda) (hX : lower ≤ eta * logx) :
    c * eta * logB - eta * logx / 4 ≤ c * lambda - lower / 4 := by
  calc
    c * eta * logB - eta * logx / 4 =
        c * (eta * logB) - (eta * logx) / 4 := by ring
    _ = c * lambda - (eta * logx) / 4 := by rw [hB]
    _ ≤ c * lambda - lower / 4 := by
      exact sub_le_sub le_rfl (div_le_div_of_nonneg_right hX (by norm_num))

private theorem endpointMiddleTerm_le
    {C x a b : ℝ} (hC : 0 ≤ C) (hx : 0 ≤ x) (hab : a ≤ b) :
    8 * C * Real.exp a * x ≤ 8 * C * Real.exp b * x := by
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hab)
      (mul_nonneg (by norm_num) hC)) hx

private theorem endpointMiddleTerm_le_of_products
    {C x c eta logB logx lambda lower : ℝ}
    (hC : 0 ≤ C) (hx : 0 ≤ x)
    (hB : eta * logB = lambda) (hX : lower ≤ eta * logx) :
    8 * C * Real.exp (c * eta * logB - eta * logx / 4) * x ≤
      8 * C * Real.exp (c * lambda - lower / 4) * x :=
  endpointMiddleTerm_le hC hx (endpointMiddleExponent_le hB hX)

/-- FLP's nonexceptional endpoint estimate along an explicit power scale.
For every requested proportion, one fixed exponent works for all sufficiently
large bases. -/
theorem eventually_exists_pageExcludedEndpointMass_le_mul_above_with_selection :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ Lmin : ℕ, ∃ cPage : ℝ, 0 < cPage ∧
        PageWindowIsQuadratic cPage ∧
        ∃ L : ℕ, 64 ≤ L ∧ Lmin ≤ L ∧ 240 ∣ L ∧
        ∀ᶠ n : ℕ in atTop,
          ∃ m₀ : ℕ, m₀ ≤ n ∧
            (∑ q ∈ (Finset.Ioc 1 n).filter (fun q ↦ q ≠ m₀),
                primitiveEndpointMass (n ^ L) q) ≤
              epsilon * ((n ^ L : ℕ) : ℝ) ∧
            (m₀ = 0 ∨ PageExceptionalWitness n m₀ cPage) ∧
            PageConductorSelection n m₀ cPage := by
  intro epsilon hepsilon Lmin
  obtain ⟨cPage, lambda₀, hcPage, hlambda₀, hlambda₀Small,
      hquadratic, hmaster⟩ :=
    exists_pageExcludedEndpointMass_explicit_bound_with_selection
  let lambda : ℝ := lambda₀ / 2
  have hlambda : 0 < lambda := by dsimp [lambda]; positivity
  have hlambdaLe : lambda ≤ lambda₀ := by dsimp [lambda]; linarith
  obtain ⟨K, Camp, C, c, Ke, Afar, hK, hC, hc, hKe, hAfar, hbound⟩ :=
    hmaster lambda hlambda hlambdaLe
  let a : ℝ := Real.exp (-lambda / 20)
  have ha0 : 0 ≤ a := (Real.exp_pos _).le
  have ha1 : a < 1 := by
    dsimp [a]
    rw [Real.exp_lt_one_iff]
    linarith
  have hmidlim : Tendsto (fun L : ℕ ↦
      8 * C * Real.exp
        (c * lambda - (lambda * (L : ℝ) / 5) / 4)) atTop (nhds 0) := by
    have hpow := (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).const_mul
      (8 * C * Real.exp (c * lambda))
    have heq : (fun L : ℕ ↦
        8 * C * Real.exp (c * lambda) * a ^ L) =ᶠ[atTop]
        (fun L : ℕ ↦ 8 * C * Real.exp
          (c * lambda - (lambda * (L : ℝ) / 5) / 4)) := by
      filter_upwards [] with L
      dsimp [a]
      rw [show c * lambda - (lambda * (L : ℝ) / 5) / 4 =
          c * lambda + (L : ℝ) * (-lambda / 20) by ring,
        Real.exp_add, Real.exp_nat_mul]
      ring
    simpa using hpow.congr' heq
  have hmidSmall : ∀ᶠ L : ℕ in atTop,
      8 * C * Real.exp
        (c * lambda - (lambda * (L : ℝ) / 5) / 4) < epsilon / 3 :=
    hmidlim.eventually (gt_mem_nhds (by linarith : 0 < epsilon / 3))
  have hLscale : ∀ᶠ L : ℕ in atTop, 20 * c ≤ (L : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  have hLcontract : ∀ᶠ L : ℕ in atTop,
      10 * Real.log 2 / lambda ≤ (L : ℝ) :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop _
  have hLconditions := hmidSmall.and (hLscale.and (hLcontract.and
    ((eventually_ge_atTop 64).and (eventually_ge_atTop Lmin))))
  have hmul240 : Tendsto (fun k : ℕ ↦ 240 * k) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with k hk
    exact hk.trans (by omega)
  obtain ⟨k, hLmid, hLscale, hLcontract, hL64, hLmin⟩ :=
    (hmul240.eventually hLconditions).exists
  let L : ℕ := 240 * k
  have hLdiv : 240 ∣ L := ⟨k, rfl⟩
  refine ⟨cPage, hcPage, hquadratic, L, hL64, hLmin, hLdiv, ?_⟩
  let Amp : ℕ → ℕ := fun n ↦ n * (n ^ 3 + 2)
  have hAmpNatTop : Tendsto Amp atTop atTop := by
    apply Filter.tendsto_atTop_mono (f := fun n : ℕ ↦ n)
    · intro n
      dsimp [Amp]
      calc
        n = n * 1 := by omega
        _ ≤ n * (n ^ 3 + 2) := by gcongr; omega
    · exact tendsto_id
  have hAmpRealTop : Tendsto (fun n ↦ (Amp n : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp hAmpNatTop
  have hlogAmpTop : Tendsto (fun n ↦ Real.log (Amp n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp hAmpRealTop
  have hlogAmp : ∀ᶠ n : ℕ in atTop, 2 ≤ Real.log (Amp n : ℝ) :=
    hlogAmpTop.eventually_ge_atTop 2
  let D : ℝ := 20 * (K + Camp + 2 + Real.log 2)
  have hamp : ∀ᶠ n : ℕ in atTop,
      20 * (K + (Real.log (Real.log (Amp n : ℝ)) + Camp + 2) +
          Real.log 2) ≤ Real.log (Amp n : ℝ) := by
    have hcomp := hlogAmpTop.eventually
      (eventually_twenty_log_add_const_le_self D)
    filter_upwards [hcomp] with n hn
    dsimp [D] at hn
    nlinarith
  have herrSmall : ∀ᶠ n : ℕ in atTop,
      (Ke : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 2 *
          (Real.log (n : ℝ) ^ 2 / (n : ℝ)) < epsilon / 3 := by
    have hlim := tendsto_log_sq_div_nat.const_mul
      ((Ke : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 2)
    have hlim' : Tendsto (fun n : ℕ ↦
        (Ke : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 2 *
          (Real.log (n : ℝ) ^ 2 / (n : ℝ))) atTop (nhds 0) := by
      simpa using hlim
    exact hlim'.eventually (gt_mem_nhds (by linarith : 0 < epsilon / 3))
  have hfarSmall : ∀ᶠ n : ℕ in atTop,
      (96 * (Afar : ℝ) * 25) *
          (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2) < epsilon / 3 := by
    have hlim := tendsto_log_sq_div_nat_sq.const_mul
      (96 * (Afar : ℝ) * 25)
    have hlim' : Tendsto (fun n : ℕ ↦
        (96 * (Afar : ℝ) * 25) *
          (Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ 2)) atTop (nhds 0) := by
      simpa using hlim
    exact hlim'.eventually (gt_mem_nhds (by linarith : 0 < epsilon / 3))
  filter_upwards [hlogAmp, hamp, herrSmall, hfarSmall,
      eventually_ge_atTop 3] with n hlogAmpN hampN herrN hfarN hn
  let B : ℝ := (n : ℝ) * (((n ^ 3 : ℕ) : ℝ) + 2)
  let eta : ℝ := lambda / Real.log B
  let J : ℕ := endpointBandCount eta
  have hn1 : 1 ≤ n := by omega
  have hn2 : 2 ≤ n := (by norm_num : 2 ≤ 3).trans hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hlogn : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hB : (8 : ℝ) ≤ B := by
    have hn3 : 8 ≤ n ^ 3 := by
      simpa only [show 8 = 2 ^ 3 by norm_num] using
        Nat.pow_le_pow_left (show 2 ≤ n by omega) 3
    dsimp [B]
    have hnCast : (3 : ℝ) ≤ n := by exact_mod_cast hn
    have hn3Cast : (8 : ℝ) ≤ (n ^ 3 : ℕ) := by exact_mod_cast hn3
    nlinarith
  have hlogB : 0 < Real.log B :=
    Real.log_pos (lt_of_lt_of_le (by norm_num : (1 : ℝ) < 8) hB)
  have hlogBone : 1 ≤ Real.log B := by
    have hlog8 : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
      norm_num
    have hmono : Real.log 8 ≤ Real.log B :=
      Real.log_le_log (by norm_num) hB
    nlinarith [Real.log_two_gt_d9]
  have heta : 0 < eta := by dsimp [eta]; positivity
  have hetaSmall : eta ≤ 1 / 16 := by
    have hetaLe : eta ≤ lambda := by
      dsimp [eta]
      rw [div_le_iff₀ hlogB]
      nlinarith
    exact hetaLe.trans (hlambdaLe.trans hlambda₀Small)
  have hBlog : Real.log B ≤ 5 * Real.log (n : ℝ) := by
    simpa only [B] using endpointPowerScale_log_le_five_log (show 2 ≤ n by omega)
  have hlogx : Real.log (((n ^ L : ℕ) : ℝ)) =
      (L : ℝ) * Real.log (n : ℝ) := log_natCast_pow n L
  have hscale : c * Real.log B ≤
      Real.log (((n ^ L : ℕ) : ℝ)) / 4 := by
    rw [hlogx]
    have hcL : 5 * c ≤ (L : ℝ) / 4 := by linarith
    calc
      c * Real.log B ≤ c * (5 * Real.log (n : ℝ)) := by gcongr
      _ = (5 * c) * Real.log (n : ℝ) := by ring
      _ ≤ ((L : ℝ) / 4) * Real.log (n : ℝ) := by gcongr
      _ = (L : ℝ) * Real.log (n : ℝ) / 4 := by ring
  have hcontract : 2 * Real.log 2 ≤
      eta * Real.log (((n ^ L : ℕ) : ℝ)) := by
    have hlambdaL : 10 * Real.log 2 ≤ lambda * (L : ℝ) := by
      have := (div_le_iff₀ hlambda).mp hLcontract
      nlinarith
    rw [hlogx]
    dsimp [eta]
    rw [show lambda / Real.log B *
        ((L : ℝ) * Real.log (n : ℝ)) =
          (lambda * (L : ℝ) * Real.log (n : ℝ)) / Real.log B by ring]
    rw [le_div_iff₀ hlogB]
    calc
      2 * Real.log 2 * Real.log B ≤
          2 * Real.log 2 * (5 * Real.log (n : ℝ)) := by gcongr
      _ = (10 * Real.log 2) * Real.log (n : ℝ) := by ring
      _ ≤ (lambda * (L : ℝ)) * Real.log (n : ℝ) := by gcongr
      _ = lambda * (L : ℝ) * Real.log (n : ℝ) := by ring
  have hwidth := endpointBandCount_width heta hetaSmall
  have halpha := endpointBandCount_far_cutoff_half heta hetaSmall
  have hmain := hbound n (n ^ 3) (n ^ L) J hn
    (by
      calc 2 ≤ n := by omega
        _ ≤ n ^ 3 := Nat.le_pow (by omega))
    (by
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ n ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ ≤ n ^ L := Nat.pow_le_pow_right (by omega) (by omega))
    (Nat.pow_le_pow_right (by omega) (by omega : 3 ≤ L))
  have hmain' := hmain
    (by simpa only [Amp] using hlogAmpN)
    (by simpa only [Amp] using hampN)
    hwidth hscale hcontract halpha
  obtain ⟨m₀, hm₀, hmass, hwitness, hselection⟩ := hmain'
  refine ⟨m₀, hm₀, ?_, hwitness, hselection⟩
  have herrEq := endpointPowerScale_explicitError_eq
    (n := n) (L := L) (Ke := Ke) (show 0 < n by omega)
  have hmiddle :
      8 * C * Real.exp
          (c * eta * Real.log B -
            eta * Real.log (((n ^ L : ℕ) : ℝ)) / 4) *
          ((n ^ L : ℕ) : ℝ) <
        (epsilon / 3) * ((n ^ L : ℕ) : ℝ) := by
    have hetaB : eta * Real.log B = lambda := by
      dsimp [eta]
      rw [div_mul_cancel₀ _ hlogB.ne']
    have hetaX : lambda * (L : ℝ) / 5 ≤
        eta * Real.log (((n ^ L : ℕ) : ℝ)) := by
      rw [hlogx]
      dsimp [eta]
      rw [show lambda / Real.log B * ((L : ℝ) * Real.log (n : ℝ)) =
          (lambda * (L : ℝ) * Real.log (n : ℝ)) / Real.log B by ring]
      rw [le_div_iff₀ hlogB]
      have hmul := mul_le_mul_of_nonneg_left hBlog
        (mul_nonneg hlambda.le (by positivity : (0 : ℝ) ≤ (L : ℝ) / 5))
      calc
        lambda * (L : ℝ) / 5 * Real.log B ≤
            lambda * (L : ℝ) / 5 * (5 * Real.log (n : ℝ)) := by
          simpa only [div_eq_mul_inv, mul_assoc] using hmul
        _ = lambda * (L : ℝ) * Real.log (n : ℝ) := by ring
    have hx0 : 0 < ((n ^ L : ℕ) : ℝ) := by positivity
    exact (endpointMiddleTerm_le_of_products hC.le hx0.le hetaB hetaX).trans_lt
      (mul_lt_mul_of_pos_right hLmid hx0)
  have hfarSaving := endpointBandCount_far_saving heta
  have hfarBound := endpointPowerScale_farTerm_le
    (n := n) (L := L) (J := J) (Afar := Afar)
      hn2 hL64 hfarSaving
  rw [herrEq] at hmass
  have herrTerm :
      ((n ^ L : ℕ) : ℝ) *
          ((Ke : ℝ) * ((L + 1 : ℕ) : ℝ) ^ 2 *
            (Real.log (n : ℝ) ^ 2 / (n : ℝ))) <
        (epsilon / 3) * ((n ^ L : ℕ) : ℝ) := by
    simpa only [mul_comm] using
      (mul_lt_mul_of_pos_left herrN (show 0 < ((n ^ L : ℕ) : ℝ) by positivity))
  have hfarTerm :
      (n : ℝ) ^ 2 *
          (96 * (Afar : ℝ) *
            (((n ^ L : ℕ) : ℝ) ^
              (1 - (((J + 1 : ℕ) : ℝ) * eta))) *
            Real.log B ^ 2) <
        (epsilon / 3) * ((n ^ L : ℕ) : ℝ) := by
    apply hfarBound.trans_lt
    simpa only [mul_comm] using
      (mul_lt_mul_of_pos_left hfarN (show 0 < ((n ^ L : ℕ) : ℝ) by positivity))
  apply le_of_lt
  calc
    (∑ q ∈ (Finset.Ioc 1 n).filter (fun q ↦ q ≠ m₀),
        primitiveEndpointMass (n ^ L) q) ≤ _ := hmass
    _ < (epsilon / 3) * ((n ^ L : ℕ) : ℝ) +
        (epsilon / 3) * ((n ^ L : ℕ) : ℝ) +
        (epsilon / 3) * ((n ^ L : ℕ) : ℝ) := by
      exact add_lt_add (add_lt_add herrTerm hmiddle) hfarTerm
    _ = epsilon * ((n ^ L : ℕ) : ℝ) := three_thirds_mul _ _

/-- Projection of the canonical Page-conductor selection which retains the
actual real-zero witness.  The selected exponent is in fact a multiple of
`240`; the older interface does not expose that extra information. -/
theorem eventually_exists_pageExcludedEndpointMass_le_mul_above_with_witness :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ Lmin : ℕ, ∃ cPage : ℝ, 0 < cPage ∧
        ∃ L : ℕ, 64 ≤ L ∧ Lmin ≤ L ∧
        ∀ᶠ n : ℕ in atTop,
          ∃ m₀ : ℕ, m₀ ≤ n ∧
            (∑ q ∈ (Finset.Ioc 1 n).filter (fun q ↦ q ≠ m₀),
                primitiveEndpointMass (n ^ L) q) ≤
              epsilon * ((n ^ L : ℕ) : ℝ) ∧
            (m₀ = 0 ∨ PageExceptionalWitness n m₀ cPage) := by
  intro epsilon hepsilon Lmin
  obtain ⟨cPage, hcPage, _hquadratic, L, hL64, hLmin, _hLdiv, hmain⟩ :=
    eventually_exists_pageExcludedEndpointMass_le_mul_above_with_selection
      epsilon hepsilon Lmin
  refine ⟨cPage, hcPage, L, hL64, hLmin, ?_⟩
  filter_upwards [hmain] with n hn
  obtain ⟨m₀, hm₀, hmass, hwitness, _hselection⟩ := hn
  exact ⟨m₀, hm₀, hmass, hwitness⟩

/-- Backwards-compatible projection which forgets the Page-zero witness. -/
theorem eventually_exists_pageExcludedEndpointMass_le_mul_above :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∀ Lmin : ℕ, ∃ L : ℕ, 64 ≤ L ∧ Lmin ≤ L ∧
        ∀ᶠ n : ℕ in atTop,
          ∃ m₀ : ℕ, m₀ ≤ n ∧
            (∑ q ∈ (Finset.Ioc 1 n).filter (fun q ↦ q ≠ m₀),
                primitiveEndpointMass (n ^ L) q) ≤
              epsilon * ((n ^ L : ℕ) : ℝ) := by
  intro epsilon hepsilon Lmin
  obtain ⟨_cPage, _hcPage, L, hL64, hLmin, hscale⟩ :=
    eventually_exists_pageExcludedEndpointMass_le_mul_above_with_witness
      epsilon hepsilon Lmin
  refine ⟨L, hL64, hLmin, ?_⟩
  filter_upwards [hscale] with n hn
  obtain ⟨m₀, hm₀, hmass, _hwitness⟩ := hn
  exact ⟨m₀, hm₀, hmass⟩

/-- Backwards-compatible form with the original fixed lower bound `64`. -/
theorem eventually_exists_pageExcludedEndpointMass_le_mul :
    ∀ epsilon : ℝ, 0 < epsilon →
      ∃ L : ℕ, 64 ≤ L ∧
        ∀ᶠ n : ℕ in atTop,
          ∃ m₀ : ℕ, m₀ ≤ n ∧
            (∑ q ∈ (Finset.Ioc 1 n).filter (fun q ↦ q ≠ m₀),
                primitiveEndpointMass (n ^ L) q) ≤
              epsilon * ((n ^ L : ℕ) : ℝ) := by
  intro epsilon hepsilon
  obtain ⟨L, hL64, _hLmin, hL⟩ :=
    eventually_exists_pageExcludedEndpointMass_le_mul_above
      epsilon hepsilon 0
  exact ⟨L, hL64, hL⟩

end

end Erdos48
