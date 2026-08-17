/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos144.PrimeBlocks
import BoundedGaps.PrimeNumberTheorem.Analytic.StrongChebyshev
import UnitFractions.ForMathlib.BasicEstimates

/-!
# Quantitative prime-number-theorem input for Erdős Problem 144

Starting from the strong Chebyshev-psi remainder proved in `BoundedGaps`, this
file removes prime powers, obtains arbitrary fixed logarithmic savings for
Chebyshev theta, and transfers the estimate to reciprocal-prime mass in the
shrinking logarithmic blocks used by the Maier--Tenenbaum argument.  The final
pointwise estimate includes an explicit quadratic Bonferroni correction and
is packaged with a twenty-fifth-power tail for summation on the problem's
explicit scales.
-/

namespace Erdos144.StrongMertens

open Filter Real
open scoped Topology

open Erdos144.PrimeBlocks

noncomputable section

/-- The quantitative modulus-one estimate from `BoundedGaps`, with prime
powers removed by Mathlib's explicit `psi - theta` estimate.  Keeping the
prime-power term visible avoids any hidden asymptotic absorption. -/
theorem exists_abs_chebyshevTheta_sub_natCast_le_exp_neg_sqrtLog_add :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      ∃ X0 : ℕ, 4 ≤ X0 ∧
        ∀ x : ℕ, X0 ≤ x →
          |Chebyshev.theta (x : ℝ) - (x : ℝ)| ≤
            C * ((x : ℝ) *
              Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) +
              2 * Real.sqrt (x : ℝ) * Real.log (x : ℝ) := by
  obtain ⟨C, c, hC, hc, X0, hX0, hpsi⟩ :=
    BoundedGaps.PrimeNumberTheorem.exists_abs_chebyshevPsi_sub_natCast_le_exp_neg_sqrtLog
  refine ⟨C, c, hC, hc, X0, hX0, ?_⟩
  intro x hx
  have hx1 : (1 : ℝ) ≤ x := by
    exact_mod_cast (show 1 ≤ x by omega)
  have hthetaPsi :
      |Chebyshev.theta (x : ℝ) - Chebyshev.psi (x : ℝ)| ≤
        2 * Real.sqrt (x : ℝ) * Real.log (x : ℝ) := by
    rw [abs_sub_comm]
    exact Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1
  calc
    |Chebyshev.theta (x : ℝ) - (x : ℝ)| ≤
        |Chebyshev.theta (x : ℝ) - Chebyshev.psi (x : ℝ)| +
          |Chebyshev.psi (x : ℝ) - (x : ℝ)| := by
      simpa only [sub_add_sub_cancel] using
        abs_add_le
          (Chebyshev.theta (x : ℝ) - Chebyshev.psi (x : ℝ))
          (Chebyshev.psi (x : ℝ) - (x : ℝ))
    _ ≤ 2 * Real.sqrt (x : ℝ) * Real.log (x : ℝ) +
        C * ((x : ℝ) *
          Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) :=
      add_le_add hthetaPsi (hpsi x hx)
    _ = C * ((x : ℝ) *
          Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) +
        2 * Real.sqrt (x : ℝ) * Real.log (x : ℝ) := by ring

/-- The exponential theta remainder beats every fixed power of the
logarithm.  We leave the elementary prime-power removal term separate; this
is useful in finite block estimates because its square-root decay is much
stronger than any power needed there. -/
theorem exists_abs_chebyshevTheta_sub_natCast_le_logSaving_add
    (D : ℝ) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧
      ∃ X0 : ℕ, 4 ≤ X0 ∧
        ∀ x : ℕ, X0 ≤ x →
          |Chebyshev.theta (x : ℝ) - (x : ℝ)| ≤
            C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) D +
              2 * Real.sqrt (x : ℝ) * Real.log (x : ℝ) := by
  obtain ⟨C, c, hC, hc, Xenv, hXenv, henv⟩ :=
    exists_abs_chebyshevTheta_sub_natCast_le_exp_neg_sqrtLog_add
  have huTop : Tendsto
      (fun x : ℕ ↦ Real.sqrt (Real.log (x : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hdom :=
    ((isLittleO_rpow_exp_pos_mul_atTop (2 * D) hc).comp_tendsto huTop).eventuallyLE
  rw [Filter.eventually_atTop] at hdom
  obtain ⟨Xdom, hXdom⟩ := hdom
  let X0 : ℕ := max Xenv (max Xdom 4)
  refine ⟨C, hC, X0, by simp [X0], ?_⟩
  intro x hx
  have hxEnv : Xenv ≤ x := by
    dsimp [X0] at hx
    omega
  have hxDom : Xdom ≤ x := by
    dsimp [X0] at hx
    omega
  have hx4 : 4 ≤ x := by
    dsimp [X0] at hx
    omega
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hlogPos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have huNonneg : 0 ≤ Real.sqrt (Real.log (x : ℝ)) := Real.sqrt_nonneg _
  have hpoly := hXdom x hxDom
  have hpoly' :
      Real.rpow (Real.sqrt (Real.log (x : ℝ))) (2 * D) ≤
        Real.exp (c * Real.sqrt (Real.log (x : ℝ))) := by
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg huNonneg _),
      abs_of_pos (Real.exp_pos _)] using hpoly
  have hpowIdentity :
      Real.rpow (Real.log (x : ℝ)) D =
        Real.rpow (Real.sqrt (Real.log (x : ℝ))) (2 * D) := by
    calc
      Real.rpow (Real.log (x : ℝ)) D =
          Real.rpow (Real.sqrt (Real.log (x : ℝ)) ^ 2) D := by
        rw [Real.sq_sqrt (le_of_lt hlogPos)]
      _ = Real.rpow
          (Real.rpow (Real.sqrt (Real.log (x : ℝ))) (2 : ℝ)) D := by
        congr 1
        exact (Real.rpow_natCast _ 2).symm
      _ = Real.rpow (Real.sqrt (Real.log (x : ℝ))) ((2 : ℝ) * D) :=
        (Real.rpow_mul (Real.sqrt_nonneg _) 2 D).symm
      _ = Real.rpow (Real.sqrt (Real.log (x : ℝ))) (2 * D) := by rfl
  have hsavePos : 0 < Real.rpow (Real.log (x : ℝ)) D :=
    Real.rpow_pos_of_pos hlogPos _
  have hdecay :
      Real.exp (-c * Real.sqrt (Real.log (x : ℝ))) ≤
        1 / Real.rpow (Real.log (x : ℝ)) D := by
    apply (le_div_iff₀ hsavePos).2
    rw [hpowIdentity]
    calc
      Real.exp (-c * Real.sqrt (Real.log (x : ℝ))) *
          Real.rpow (Real.sqrt (Real.log (x : ℝ))) (2 * D) ≤
        Real.exp (-c * Real.sqrt (Real.log (x : ℝ))) *
          Real.exp (c * Real.sqrt (Real.log (x : ℝ))) :=
        mul_le_mul_of_nonneg_left hpoly' (Real.exp_pos _).le
      _ = 1 := by simp [← Real.exp_add]
  calc
    |Chebyshev.theta (x : ℝ) - (x : ℝ)| ≤
        C * ((x : ℝ) *
          Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) +
          2 * Real.sqrt (x : ℝ) * Real.log (x : ℝ) := henv x hxEnv
    _ ≤ C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) D +
          2 * Real.sqrt (x : ℝ) * Real.log (x : ℝ) := by
      have hmain : C * ((x : ℝ) *
          Real.exp (-c * Real.sqrt (Real.log (x : ℝ)))) ≤
          C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) D := by
        rw [div_eq_mul_inv, mul_assoc]
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (by simpa only [one_div] using hdecay) hxpos.le) hC.le
      linarith

/-- The prime-power removal term can also be absorbed into an arbitrary
fixed logarithmic saving. -/
theorem exists_abs_chebyshevTheta_sub_natCast_le_logSaving
    (D : ℝ) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧
      ∃ X0 : ℕ, 4 ≤ X0 ∧
        ∀ x : ℕ, X0 ≤ x →
          |Chebyshev.theta (x : ℝ) - (x : ℝ)| ≤
            C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) D := by
  obtain ⟨C, hC, Xenv, hXenv, henv⟩ :=
    exists_abs_chebyshevTheta_sub_natCast_le_logSaving_add D hD
  have hdom :=
    ((isLittleO_log_rpow_rpow_atTop (D + 1) (by norm_num : (0 : ℝ) < 1 / 2)).comp_tendsto
      tendsto_natCast_atTop_atTop).eventuallyLE
  rw [Filter.eventually_atTop] at hdom
  obtain ⟨Xdom, hXdom⟩ := hdom
  let X0 : ℕ := max Xenv (max Xdom 4)
  refine ⟨C + 2, by linarith, X0, by simp [X0], ?_⟩
  intro x hx
  have hxEnv : Xenv ≤ x := by
    dsimp [X0] at hx
    omega
  have hxDom : Xdom ≤ x := by
    dsimp [X0] at hx
    omega
  have hx4 : 4 ≤ x := by
    dsimp [X0] at hx
    omega
  have hxpos : (0 : ℝ) < (x : ℝ) := by positivity
  have hlogPos : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hpoly := hXdom x hxDom
  have hpoly' :
      Real.rpow (Real.log (x : ℝ)) (D + 1) ≤
        Real.rpow (x : ℝ) (1 / 2 : ℝ) := by
    simpa [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hlogPos.le _),
      abs_of_nonneg (Real.rpow_nonneg hxpos.le _)] using hpoly
  have hlogmul :
      Real.rpow (Real.log (x : ℝ)) D * Real.log (x : ℝ) ≤
        Real.sqrt (x : ℝ) := by
    have hadd : Real.rpow (Real.log (x : ℝ)) D * Real.log (x : ℝ) =
        Real.rpow (Real.log (x : ℝ)) (D + 1) := by
      simpa only [Real.rpow_one] using! (Real.rpow_add hlogPos D 1).symm
    calc
      Real.rpow (Real.log (x : ℝ)) D * Real.log (x : ℝ) =
          Real.rpow (Real.log (x : ℝ)) (D + 1) := hadd
      _ ≤ Real.rpow (x : ℝ) (1 / 2 : ℝ) := hpoly'
      _ = Real.sqrt (x : ℝ) := (Real.sqrt_eq_rpow _).symm
  have hsavePos : 0 < Real.rpow (Real.log (x : ℝ)) D :=
    Real.rpow_pos_of_pos hlogPos _
  have hprimePower :
      2 * Real.sqrt (x : ℝ) * Real.log (x : ℝ) ≤
        2 * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) D := by
    rw [le_div_iff₀ hsavePos]
    calc
      2 * Real.sqrt (x : ℝ) * Real.log (x : ℝ) *
          Real.rpow (Real.log (x : ℝ)) D =
        2 * Real.sqrt (x : ℝ) *
          (Real.rpow (Real.log (x : ℝ)) D * Real.log (x : ℝ)) := by ring
      _ ≤ 2 * Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ) :=
        mul_le_mul_of_nonneg_left hlogmul (by positivity)
      _ = 2 * (x : ℝ) := by
        rw [mul_assoc, Real.mul_self_sqrt hxpos.le]
  calc
    |Chebyshev.theta (x : ℝ) - (x : ℝ)| ≤
        C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) D +
          2 * Real.sqrt (x : ℝ) * Real.log (x : ℝ) := henv x hxEnv
    _ ≤ C * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) D +
          2 * (x : ℝ) / Real.rpow (Real.log (x : ℝ)) D :=
      by linarith
    _ = (C + 2) * (x : ℝ) /
          Real.rpow (Real.log (x : ℝ)) D := by ring

/-- The theta increment over a natural interval is the sum of prime
logarithms on that interval. -/
lemma chebyshevTheta_nat_sub_eq_sum_Ioc_primes {a b : ℕ} (hab : a ≤ b) :
    Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ) =
      ∑ p ∈ (Finset.Ioc a b).filter Nat.Prime, Real.log p := by
  rw [Chebyshev.theta_eq_sum_primesLE_log,
    Chebyshev.theta_eq_sum_primesLE_log,
    Nat.primesLE_eq_filter_Icc_zero,
    Nat.primesLE_eq_filter_Icc_zero,
    ← Finset.sum_sdiff_eq_sub]
  · apply Finset.sum_congr
    · ext p
      simp only [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc,
        Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨⟨_, hpb⟩, hp⟩, hpa⟩
        refine ⟨⟨?_, hpb⟩, hp⟩
        exact lt_of_not_ge fun h ↦ hpa ⟨⟨Nat.zero_le _, h⟩, hp⟩
      · rintro ⟨⟨hap, hpb⟩, hp⟩
        exact ⟨⟨⟨Nat.zero_le _, hpb⟩, hp⟩,
          fun h ↦ (not_le_of_gt hap) h.1.2⟩
    · intro p hp
      rfl
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_Icc] at hp ⊢
    exact ⟨⟨hp.1.1, hp.1.2.trans hab⟩, hp.2⟩

/-- Exact theta description of a multiplicative prime block. -/
lemma chebyshevTheta_sub_eq_sum_block {r x : ℝ}
    (hx : 0 ≤ x) (hrx : x ≤ r * x) :
    Chebyshev.theta (r * x) - Chebyshev.theta x =
      ∑ p ∈ block r x, Real.log p := by
  rw [Chebyshev.theta_eq_theta_coe_floor (r * x),
    Chebyshev.theta_eq_theta_coe_floor x]
  simpa only [block] using
    (chebyshevTheta_nat_sub_eq_sum_Ioc_primes (Nat.floor_mono hrx))

/-- Reciprocal-prime mass is sandwiched by a theta increment.  Unlike the
corresponding prime-count sandwich, this retains the strong theta remainder
without an additional partial-summation loss. -/
lemma thetaBlock_div_upper_le_mass_le_thetaBlock_div_lower {r x : ℝ}
    (hx : 1 < x) (hr : 1 ≤ r) :
    (Chebyshev.theta (r * x) - Chebyshev.theta x) /
          (r * x * Real.log (r * x)) ≤ mass r x ∧
      mass r x ≤
        (Chebyshev.theta (r * x) - Chebyshev.theta x) /
          (x * Real.log x) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hrx1 : 1 < r * x := by nlinarith [mul_le_mul_of_nonneg_right hr hx0.le]
  have hrx : x ≤ r * x := le_mul_of_one_le_left hx0.le hr
  have htheta := chebyshevTheta_sub_eq_sum_block hx0.le hrx
  rw [htheta, mass]
  constructor
  · rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro p hp
    have hpmem := mem_block (mul_nonneg hr0.le hx0.le) hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpmem.1.pos
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpmem.1.one_lt
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1
    have hlogUpper : Real.log (p : ℝ) ≤ Real.log (r * x) :=
      Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr hp0) (Set.mem_Ioi.mpr (mul_pos hr0 hx0)) hpmem.2.2
    have hprod : (p : ℝ) * Real.log p ≤
        (r * x) * Real.log (r * x) :=
      mul_le_mul hpmem.2.2 hlogUpper hlogp.le (mul_pos hr0 hx0).le
    rw [← one_div]
    rw [div_le_div_iff₀ (mul_pos (mul_pos hr0 hx0) (Real.log_pos hrx1)) hp0]
    nlinarith
  · rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro p hp
    have hpmem := mem_block (mul_nonneg hr0.le hx0.le) hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpmem.1.pos
    have hlogp : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast hpmem.1.one_lt)
    have hlogLower : Real.log x ≤ Real.log (p : ℝ) :=
      Real.strictMonoOn_log.monotoneOn
        (Set.mem_Ioi.mpr hx0) (Set.mem_Ioi.mpr hp0) hpmem.2.1.le
    have hprod : x * Real.log x ≤ (p : ℝ) * Real.log p :=
      mul_le_mul hpmem.2.1.le hlogLower (Real.log_pos hx).le hp0.le
    rw [← one_div]
    rw [div_le_div_iff₀ hp0 (mul_pos hx0 (Real.log_pos hx))]
    nlinarith

/-- The theta sandwich in the exact normalization of logarithmic blocks. -/
lemma logBlockMass_theta_bounds {K i : ℕ} (hK : 0 < K) (hi : 0 < i) :
    let a := Real.exp ((i : ℝ) / K)
    let b := Real.exp (((i + 1 : ℕ) : ℝ) / K)
    let T := Chebyshev.theta b - Chebyshev.theta a
    T * K / (((i + 1 : ℕ) : ℝ) * b) ≤ logBlockMass K i ∧
      logBlockMass K i ≤ T * K / ((i : ℝ) * a) := by
  dsimp only
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hx : (1 : ℝ) < Real.exp ((i : ℝ) / K) :=
    Real.one_lt_exp_iff.mpr (div_pos hiR hKR)
  have hr : (1 : ℝ) ≤ Real.exp ((K : ℝ)⁻¹) :=
    Real.one_le_exp (inv_nonneg.mpr hKR.le)
  have hs := thetaBlock_div_upper_le_mass_le_thetaBlock_div_lower hx hr
  have hab : Real.exp ((K : ℝ)⁻¹) * Real.exp ((i : ℝ) / K) =
      Real.exp (((i + 1 : ℕ) : ℝ) / K) := by
    rw [← Real.exp_add]
    congr 1
    norm_num only [Nat.cast_add, Nat.cast_one]
    field_simp
    ring
  have hloga : Real.log (Real.exp ((i : ℝ) / K)) = (i : ℝ) / K :=
    Real.log_exp _
  have hlogb : Real.log (Real.exp (((i + 1 : ℕ) : ℝ) / K)) =
      ((i + 1 : ℕ) : ℝ) / K := Real.log_exp _
  rw [hab, hloga, hlogb] at hs
  simpa only [logBlockMass] using (show
    (Chebyshev.theta (Real.exp (((i + 1 : ℕ) : ℝ) / K)) -
        Chebyshev.theta (Real.exp ((i : ℝ) / K))) * K /
          (((i + 1 : ℕ) : ℝ) *
            Real.exp (((i + 1 : ℕ) : ℝ) / K)) ≤
        mass (Real.exp ((K : ℝ)⁻¹)) (Real.exp ((i : ℝ) / K)) ∧
      mass (Real.exp ((K : ℝ)⁻¹)) (Real.exp ((i : ℝ) / K)) ≤
        (Chebyshev.theta (Real.exp (((i + 1 : ℕ) : ℝ) / K)) -
          Chebyshev.theta (Real.exp ((i : ℝ) / K))) * K /
            ((i : ℝ) * Real.exp ((i : ℝ) / K)) by
    constructor
    · convert hs.1 using 1 <;> field_simp <;> ring
    · convert hs.2 using 1 <;> field_simp <;> ring)

/-- Replacing a nonnegative real endpoint by its natural floor costs at most
one in a theta remainder. -/
lemma abs_chebyshevTheta_sub_le_floor_remainder_add_one {x : ℝ} (hx : 0 ≤ x) :
    |Chebyshev.theta x - x| ≤
      |Chebyshev.theta (⌊x⌋₊ : ℝ) - (⌊x⌋₊ : ℝ)| + 1 := by
  have hfloorLe : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx
  have hxLt : x < (⌊x⌋₊ : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one x
  have hfloorError : |(⌊x⌋₊ : ℝ) - x| ≤ 1 := by
    rw [abs_of_nonpos (sub_nonpos.mpr hfloorLe)]
    linarith
  rw [Chebyshev.theta_eq_theta_coe_floor x]
  calc
    |Chebyshev.theta (⌊x⌋₊ : ℝ) - x| ≤
        |Chebyshev.theta (⌊x⌋₊ : ℝ) - (⌊x⌋₊ : ℝ)| +
          |(⌊x⌋₊ : ℝ) - x| := by
      simpa only [sub_add_sub_cancel] using
        abs_add_le
          (Chebyshev.theta (⌊x⌋₊ : ℝ) - (⌊x⌋₊ : ℝ))
          ((⌊x⌋₊ : ℝ) - x)
    _ ≤ |Chebyshev.theta (⌊x⌋₊ : ℝ) - (⌊x⌋₊ : ℝ)| + 1 :=
      by linarith

/-- Uniform real-endpoint form of the logarithmic theta saving.  The floor is
kept explicit so downstream finite estimates can use the exact integer
threshold furnished by the strong Chebyshev theorem. -/
theorem exists_abs_chebyshevTheta_sub_real_le_logSaving_floor_add
    (D : ℝ) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧
      ∃ X0 : ℕ, 4 ≤ X0 ∧
        ∀ x : ℝ, X0 ≤ ⌊x⌋₊ →
          |Chebyshev.theta x - x| ≤
            C * (⌊x⌋₊ : ℝ) /
                Real.rpow (Real.log (⌊x⌋₊ : ℝ)) D +
              2 * Real.sqrt (⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ) + 1 := by
  obtain ⟨C, hC, X0, hX0, hbound⟩ :=
    exists_abs_chebyshevTheta_sub_natCast_le_logSaving_add D hD
  refine ⟨C, hC, X0, hX0, ?_⟩
  intro x hxFloor
  have hx0 : 0 ≤ x := by
    by_contra hxneg
    have hfloorZero : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    omega
  calc
    |Chebyshev.theta x - x| ≤
        |Chebyshev.theta (⌊x⌋₊ : ℝ) - (⌊x⌋₊ : ℝ)| + 1 :=
      abs_chebyshevTheta_sub_le_floor_remainder_add_one hx0
    _ ≤ (C * (⌊x⌋₊ : ℝ) /
          Real.rpow (Real.log (⌊x⌋₊ : ℝ)) D +
          2 * Real.sqrt (⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ)) + 1 :=
      by linarith [hbound ⌊x⌋₊ hxFloor]
    _ = C * (⌊x⌋₊ : ℝ) /
          Real.rpow (Real.log (⌊x⌋₊ : ℝ)) D +
          2 * Real.sqrt (⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ) + 1 := by ring

/-- Pure log-saving form at real endpoints, after absorbing prime powers. -/
theorem exists_abs_chebyshevTheta_sub_real_le_logSaving_floor
    (D : ℝ) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧
      ∃ X0 : ℕ, 4 ≤ X0 ∧
        ∀ x : ℝ, X0 ≤ ⌊x⌋₊ →
          |Chebyshev.theta x - x| ≤
            C * (⌊x⌋₊ : ℝ) /
                Real.rpow (Real.log (⌊x⌋₊ : ℝ)) D + 1 := by
  obtain ⟨C, hC, X0, hX0, hbound⟩ :=
    exists_abs_chebyshevTheta_sub_natCast_le_logSaving D hD
  refine ⟨C, hC, X0, hX0, ?_⟩
  intro x hxFloor
  have hx0 : 0 ≤ x := by
    by_contra hxneg
    have hfloorZero : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    omega
  exact (abs_chebyshevTheta_sub_le_floor_remainder_add_one hx0).trans
    (by linarith [hbound ⌊x⌋₊ hxFloor])

/-- The error of a theta increment is at most the sum of its two endpoint
errors. -/
lemma abs_thetaIncrement_sub_length_le_endpoint_errors {a b : ℝ} :
    |(Chebyshev.theta b - Chebyshev.theta a) - (b - a)| ≤
      |Chebyshev.theta b - b| + |Chebyshev.theta a - a| := by
  have h := abs_add_le (Chebyshev.theta b - b) (-(Chebyshev.theta a - a))
  rw [abs_neg] at h
  calc
    |(Chebyshev.theta b - Chebyshev.theta a) - (b - a)| =
        |(Chebyshev.theta b - b) + -(Chebyshev.theta a - a)| := by
      congr 1
      abel
    _ ≤ |Chebyshev.theta b - b| + |Chebyshev.theta a - a| := h

/-- Upper first-order mesh error for `exp (1 / K)`. -/
lemma mesh_exp_upper_error {K : ℕ} (hK : 0 < K) :
    (K : ℝ) * (Real.exp ((K : ℝ)⁻¹) - 1) - 1 ≤ (K : ℝ)⁻¹ := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hz : |(K : ℝ)⁻¹| ≤ 1 := by
    rw [abs_of_pos (inv_pos.mpr hKR)]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hK)
  have h := Real.abs_exp_sub_one_sub_id_le hz
  have hle : Real.exp ((K : ℝ)⁻¹) - 1 - (K : ℝ)⁻¹ ≤
      ((K : ℝ)⁻¹) ^ 2 := (le_abs_self _).trans h
  have hmul := mul_le_mul_of_nonneg_left hle hKR.le
  calc
    (K : ℝ) * (Real.exp ((K : ℝ)⁻¹) - 1) - 1 =
        (K : ℝ) *
          (Real.exp ((K : ℝ)⁻¹) - 1 - (K : ℝ)⁻¹) := by
      field_simp
    _ ≤ (K : ℝ) * ((K : ℝ)⁻¹) ^ 2 := hmul
    _ = (K : ℝ)⁻¹ := by field_simp

/-- Lower first-order mesh error and positivity for `exp (-1 / K)`. -/
lemma mesh_exp_lower_error {K : ℕ} (hK : 0 < K) :
    0 ≤ (K : ℝ) * (1 - Real.exp (-(K : ℝ)⁻¹)) ∧
      (K : ℝ) * (1 - Real.exp (-(K : ℝ)⁻¹)) ≤ 1 ∧
      1 - (K : ℝ) * (1 - Real.exp (-(K : ℝ)⁻¹)) ≤ (K : ℝ)⁻¹ := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hzpos : 0 < (K : ℝ)⁻¹ := inv_pos.mpr hKR
  have hnonneg : 0 ≤ 1 - Real.exp (-(K : ℝ)⁻¹) := by
    exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr
      (neg_nonpos.mpr (inv_nonneg.mpr hKR.le)))
  have hupper : 1 - Real.exp (-(K : ℝ)⁻¹) ≤ (K : ℝ)⁻¹ := by
    linarith [Real.add_one_le_exp (-(K : ℝ)⁻¹)]
  have hprodUpper : (K : ℝ) *
      (1 - Real.exp (-(K : ℝ)⁻¹)) ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hupper hKR.le
    field_simp at this ⊢
    exact this
  refine ⟨mul_nonneg hKR.le hnonneg, hprodUpper, ?_⟩
  have hz : |-(K : ℝ)⁻¹| ≤ 1 := by
    rw [abs_neg, abs_of_pos hzpos]
    exact inv_le_one_of_one_le₀ (by exact_mod_cast hK)
  have h := Real.abs_exp_sub_one_sub_id_le hz
  have hle : Real.exp (-(K : ℝ)⁻¹) - 1 - (-(K : ℝ)⁻¹) ≤
      (-(K : ℝ)⁻¹) ^ 2 := (le_abs_self _).trans h
  have hmul := mul_le_mul_of_nonneg_left hle hKR.le
  calc
    1 - (K : ℝ) * (1 - Real.exp (-(K : ℝ)⁻¹)) =
        (K : ℝ) *
          (Real.exp (-(K : ℝ)⁻¹) - 1 + (K : ℝ)⁻¹) := by
      field_simp
      ring
    _ ≤ (K : ℝ) * (-(K : ℝ)⁻¹) ^ 2 := by
      simpa only [sub_neg_eq_add] using hmul
    _ = (K : ℝ)⁻¹ := by field_simp

/-- Pointwise reciprocal-mass approximation on a logarithmic block.  The
three terms are respectively the exponential mesh error, the change from
`i` to `i+1`, and the strong-theta endpoint error. -/
lemma abs_logBlockMass_sub_inv_le_mesh_add_thetaError {K i : ℕ}
    (hK : 0 < K) (hi : 0 < i) :
    let a := Real.exp ((i : ℝ) / K)
    let b := Real.exp (((i + 1 : ℕ) : ℝ) / K)
    let delta := |(Chebyshev.theta b - Chebyshev.theta a) - (b - a)|
    |logBlockMass K i - (i : ℝ)⁻¹| ≤
      1 / ((K : ℝ) * i) + 1 / ((i : ℝ) * (i + 1)) +
        ((K : ℝ) / i) * Real.exp (-((i : ℝ) / K)) * delta := by
  dsimp only
  let a := Real.exp ((i : ℝ) / K)
  let b := Real.exp (((i + 1 : ℕ) : ℝ) / K)
  let T := Chebyshev.theta b - Chebyshev.theta a
  let delta := |T - (b - a)|
  let m := logBlockMass K i
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have ha0 : 0 < a := Real.exp_pos _
  have hb0 : 0 < b := Real.exp_pos _
  have hi10 : (0 : ℝ) < (i + 1 : ℕ) := by positivity
  have hs : T * K / (((i + 1 : ℕ) : ℝ) * b) ≤ m ∧
      m ≤ T * K / ((i : ℝ) * a) := by
    simpa only [a, b, T, m] using logBlockMass_theta_bounds hK hi
  have hdeltaUpper : T ≤ b - a + delta := by
    dsimp only [delta]
    linarith [le_abs_self (T - (b - a))]
  have hdeltaLower : b - a - delta ≤ T := by
    dsimp only [delta]
    linarith [neg_le_abs (T - (b - a))]
  let u : ℝ := (K : ℝ) / ((i : ℝ) * a)
  let l : ℝ := (K : ℝ) / (((i + 1 : ℕ) : ℝ) * b)
  have hu0 : 0 ≤ u := (div_nonneg hKR.le (mul_nonneg hiR.le ha0.le))
  have hl0 : 0 ≤ l := (div_nonneg hKR.le (mul_nonneg hi10.le hb0.le))
  have hmUpper : m ≤ (b - a) * u + delta * u := by
    calc
      m ≤ T * K / ((i : ℝ) * a) := hs.2
      _ = T * u := by simp only [u]; ring
      _ ≤ (b - a + delta) * u :=
        mul_le_mul_of_nonneg_right hdeltaUpper hu0
      _ = (b - a) * u + delta * u := by ring
  have hmLower : (b - a) * l - delta * l ≤ m := by
    calc
      (b - a) * l - delta * l = (b - a - delta) * l := by ring
      _ ≤ T * l := mul_le_mul_of_nonneg_right hdeltaLower hl0
      _ = T * K / (((i + 1 : ℕ) : ℝ) * b) := by simp only [l]; ring
      _ ≤ m := hs.1
  have hab : b = a * Real.exp ((K : ℝ)⁻¹) := by
    simp only [a, b, ← Real.exp_add]
    congr 1
    norm_num only [Nat.cast_add, Nat.cast_one]
    field_simp
  have hainv : a⁻¹ = Real.exp (-((i : ℝ) / K)) := by
    simp only [a, ← Real.exp_neg]
  have hmainUpper :
      (b - a) * u - (i : ℝ)⁻¹ ≤ 1 / ((K : ℝ) * i) := by
    have hmesh := mesh_exp_upper_error hK
    have heq : (b - a) * u - (i : ℝ)⁻¹ =
        ((K : ℝ) * (Real.exp ((K : ℝ)⁻¹) - 1) - 1) / i := by
      rw [hab]
      dsimp only [u]
      field_simp
    rw [heq]
    calc
      ((K : ℝ) * (Real.exp ((K : ℝ)⁻¹) - 1) - 1) / i ≤
          (K : ℝ)⁻¹ / i :=
        div_le_div_of_nonneg_right hmesh hiR.le
      _ = 1 / ((K : ℝ) * i) := by field_simp
  have hlFactor :
      (b - a) * l =
        ((K : ℝ) * (1 - Real.exp (-(K : ℝ)⁻¹))) /
          ((i + 1 : ℕ) : ℝ) := by
    rw [hab]
    dsimp only [l]
    rw [hab]
    have hexp : Real.exp ((K : ℝ)⁻¹) *
        Real.exp (-(K : ℝ)⁻¹) = 1 := by
      rw [← Real.exp_add]
      simp
    field_simp
    simp only [one_div]
    nlinarith
  have hmainLower :
      (i : ℝ)⁻¹ - (b - a) * l ≤
        1 / ((K : ℝ) * i) + 1 / ((i : ℝ) * (i + 1)) := by
    rcases mesh_exp_lower_error hK with ⟨hL0, hL1, hLerr⟩
    rw [hlFactor, ← one_div]
    let L : ℝ := (K : ℝ) * (1 - Real.exp (-(K : ℝ)⁻¹))
    have hdecomp : 1 / (i : ℝ) - L / ((i + 1 : ℕ) : ℝ) =
        (1 - L) / (i : ℝ) + L / ((i : ℝ) * (i + 1)) := by
      dsimp only [L]
      norm_num only [Nat.cast_add, Nat.cast_one]
      field_simp
      ring
    rw [show (K : ℝ) * (1 - Real.exp (-(K : ℝ)⁻¹)) = L by rfl,
      hdecomp]
    have hfirst : (1 - L) / (i : ℝ) ≤ (K : ℝ)⁻¹ / i :=
      div_le_div_of_nonneg_right (by simpa only [L] using hLerr) hiR.le
    have hden0 : 0 ≤ (i : ℝ) * (i + 1) := by positivity
    have hsecond : L / ((i : ℝ) * (i + 1)) ≤
        1 / ((i : ℝ) * (i + 1)) :=
      div_le_div_of_nonneg_right (by simpa only [L] using hL1) hden0
    have hrewrite : (K : ℝ)⁻¹ / i = 1 / ((K : ℝ) * i) := by
      field_simp
    rw [hrewrite] at hfirst
    exact add_le_add hfirst hsecond
  have hdeltaU : delta * u =
      ((K : ℝ) / i) * Real.exp (-((i : ℝ) / K)) * delta := by
    rw [← hainv]
    dsimp only [u]
    field_simp
  have hdeltaL : delta * l ≤
      ((K : ℝ) / i) * Real.exp (-((i : ℝ) / K)) * delta := by
    have hdelta0 : 0 ≤ delta := abs_nonneg _
    have hib : (i : ℝ) * a ≤ ((i + 1 : ℕ) : ℝ) * b := by
      apply mul_le_mul
      · norm_num
      · rw [hab]
        exact le_mul_of_one_le_right ha0.le
          (Real.one_le_exp (inv_nonneg.mpr hKR.le))
      · exact ha0.le
      · exact hi10.le
    have hlu : l ≤ u := by
      dsimp only [l, u]
      exact div_le_div_of_nonneg_left hKR.le (mul_pos hiR ha0) hib
    calc
      delta * l ≤ delta * u := mul_le_mul_of_nonneg_left hlu hdelta0
      _ = ((K : ℝ) / i) * Real.exp (-((i : ℝ) / K)) * delta := hdeltaU
  have hmiddle0 : 0 ≤ 1 / ((i : ℝ) * (i + 1)) := by positivity
  change |m - (i : ℝ)⁻¹| ≤ _
  rw [abs_le]
  constructor
  · linarith
  · linarith

/-- Endpoint theta error for the `i`-th logarithmic block. -/
noncomputable def logBlockThetaError (K i : ℕ) : ℝ :=
  let a := Real.exp ((i : ℝ) / K)
  let b := Real.exp (((i + 1 : ℕ) : ℝ) / K)
  |(Chebyshev.theta b - Chebyshev.theta a) - (b - a)|

/-- Total pointwise error furnished by the theta sandwich before the
Bonferroni correction. -/
noncomputable def logBlockMassError (K i : ℕ) : ℝ :=
  1 / ((K : ℝ) * i) + 1 / ((i : ℝ) * (i + 1)) +
    ((K : ℝ) / i) * Real.exp (-((i : ℝ) / K)) *
      logBlockThetaError K i

lemma abs_logBlockMass_sub_inv_le {K i : ℕ} (hK : 0 < K) (hi : 0 < i) :
    |logBlockMass K i - (i : ℝ)⁻¹| ≤ logBlockMassError K i := by
  simpa only [logBlockMassError, logBlockThetaError] using
    abs_logBlockMass_sub_inv_le_mesh_add_thetaError hK hi

lemma logBlockMassError_nonneg {K i : ℕ} (hK : 0 < K) (hi : 0 < i) :
    0 ≤ logBlockMassError K i := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  unfold logBlockMassError logBlockThetaError
  positivity

/-- Pointwise occupancy approximation, including the exact quadratic
Bonferroni cost. -/
lemma abs_logBlockOccupancy_sub_inv_le {K i : ℕ} (hK : 0 < K) (hi : 0 < i) :
    |logBlockOccupancy K i - (i : ℝ)⁻¹| ≤
      logBlockMassError K i +
        ((i : ℝ)⁻¹ + logBlockMassError K i) ^ 2 / 2 := by
  have hm := abs_logBlockMass_sub_inv_le hK hi
  have htransfer := abs_occupancy_sub_le
    (Real.exp ((K : ℝ)⁻¹)) (Real.exp ((i : ℝ) / K))
    ((i : ℝ)⁻¹) (logBlockMassError K i) hm
  have hm0 : 0 ≤ logBlockMass K i := by
    exact mass_nonneg _ _
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hE0 := logBlockMassError_nonneg hK hi
  have hmUpper : logBlockMass K i ≤
      (i : ℝ)⁻¹ + logBlockMassError K i := by
    linarith [le_abs_self (logBlockMass K i - (i : ℝ)⁻¹)]
  have htarget0 : 0 ≤ (i : ℝ)⁻¹ + logBlockMassError K i :=
    add_nonneg (inv_nonneg.mpr hiR.le) hE0
  have hsquare : (logBlockMass K i) ^ 2 ≤
      ((i : ℝ)⁻¹ + logBlockMassError K i) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hmUpper)
      (add_nonneg hm0 htarget0)]
  have hsquareRaw :
      (mass (Real.exp ((K : ℝ)⁻¹)) (Real.exp ((i : ℝ) / K))) ^ 2 ≤
        ((i : ℝ)⁻¹ + logBlockMassError K i) ^ 2 := by
    simpa only [logBlockMass] using hsquare
  have hdiv :=
    div_le_div_of_nonneg_right hsquareRaw (by norm_num : (0 : ℝ) ≤ 2)
  have hstep : logBlockMassError K i +
      (mass (Real.exp ((K : ℝ)⁻¹)) (Real.exp ((i : ℝ) / K))) ^ 2 / 2 ≤
        logBlockMassError K i +
          ((i : ℝ)⁻¹ + logBlockMassError K i) ^ 2 / 2 := by
    linarith
  simpa only [logBlockOccupancy] using htransfer.trans hstep

/-- Explicit floor-based majorant for one real theta endpoint. -/
noncomputable def thetaFloorLogError (C D x : ℝ) : ℝ :=
  C * (⌊x⌋₊ : ℝ) / Real.rpow (Real.log (⌊x⌋₊ : ℝ)) D +
    2 * Real.sqrt (⌊x⌋₊ : ℝ) * Real.log (⌊x⌋₊ : ℝ) + 1

/-- A fixed high logarithmic power controls all logarithmic-block theta
errors once both integer endpoints have crossed a single threshold. -/
theorem exists_logBlockThetaError_le_floor_logSaving (D : ℝ) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧
      ∃ X0 : ℕ, 4 ≤ X0 ∧
        ∀ K i : ℕ,
          X0 ≤ ⌊Real.exp ((i : ℝ) / K)⌋₊ →
          X0 ≤ ⌊Real.exp (((i + 1 : ℕ) : ℝ) / K)⌋₊ →
          logBlockThetaError K i ≤
            thetaFloorLogError C D (Real.exp ((i : ℝ) / K)) +
              thetaFloorLogError C D
                (Real.exp (((i + 1 : ℕ) : ℝ) / K)) := by
  obtain ⟨C, hC, X0, hX0, hbound⟩ :=
    exists_abs_chebyshevTheta_sub_real_le_logSaving_floor_add D hD
  refine ⟨C, hC, X0, hX0, ?_⟩
  intro K i ha hb
  unfold logBlockThetaError
  have hbnd := hbound (Real.exp (((i + 1 : ℕ) : ℝ) / K)) hb
  have habnd := hbound (Real.exp ((i : ℝ) / K)) ha
  calc
    |(Chebyshev.theta (Real.exp (((i + 1 : ℕ) : ℝ) / K)) -
        Chebyshev.theta (Real.exp ((i : ℝ) / K))) -
        (Real.exp (((i + 1 : ℕ) : ℝ) / K) -
          Real.exp ((i : ℝ) / K))| ≤
      |Chebyshev.theta (Real.exp (((i + 1 : ℕ) : ℝ) / K)) -
        Real.exp (((i + 1 : ℕ) : ℝ) / K)| +
      |Chebyshev.theta (Real.exp ((i : ℝ) / K)) -
        Real.exp ((i : ℝ) / K)| :=
      abs_thetaIncrement_sub_length_le_endpoint_errors
    _ ≤ thetaFloorLogError C D (Real.exp ((i : ℝ) / K)) +
        thetaFloorLogError C D
          (Real.exp (((i + 1 : ℕ) : ℝ) / K)) := by
      unfold thetaFloorLogError
      linarith

/-- Pure log-saving endpoint majorant for a logarithmic block. -/
theorem exists_logBlockThetaError_le_floor_logSaving_pure
    (D : ℝ) (hD : 0 ≤ D) :
    ∃ C : ℝ, 0 < C ∧
      ∃ X0 : ℕ, 4 ≤ X0 ∧
        ∀ K i : ℕ,
          X0 ≤ ⌊Real.exp ((i : ℝ) / K)⌋₊ →
          X0 ≤ ⌊Real.exp (((i + 1 : ℕ) : ℝ) / K)⌋₊ →
          logBlockThetaError K i ≤
            C * (⌊Real.exp ((i : ℝ) / K)⌋₊ : ℝ) /
                Real.rpow
                  (Real.log (⌊Real.exp ((i : ℝ) / K)⌋₊ : ℝ)) D + 1 +
              (C * (⌊Real.exp (((i + 1 : ℕ) : ℝ) / K)⌋₊ : ℝ) /
                Real.rpow
                  (Real.log
                    (⌊Real.exp (((i + 1 : ℕ) : ℝ) / K)⌋₊ : ℝ)) D + 1) := by
  obtain ⟨C, hC, X0, hX0, hbound⟩ :=
    exists_abs_chebyshevTheta_sub_real_le_logSaving_floor D hD
  refine ⟨C, hC, X0, hX0, ?_⟩
  intro K i ha hb
  have hinc := abs_thetaIncrement_sub_length_le_endpoint_errors
    (a := Real.exp ((i : ℝ) / K))
    (b := Real.exp (((i + 1 : ℕ) : ℝ) / K))
  unfold logBlockThetaError
  linarith [hbound _ ha, hbound _ hb]

/-- Beyond `log 2`, the natural floor of an exponential retains at least half
of its real value. -/
lemma half_exp_le_natFloor_exp {t : ℝ} (ht : Real.log 2 ≤ t) :
    Real.exp t / 2 ≤ (⌊Real.exp t⌋₊ : ℝ) := by
  have hexp2 : (2 : ℝ) ≤ Real.exp t := by
    calc
      (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp t := Real.exp_le_exp.mpr ht
  have hlt : Real.exp t < (⌊Real.exp t⌋₊ : ℝ) + 1 := by
    exact_mod_cast Nat.lt_floor_add_one (Real.exp t)
  linarith

/-- Hence the logarithm of the natural floor of `exp t` is at least `t/2`
once `t ≥ 2 log 2`. -/
lemma half_le_log_natFloor_exp {t : ℝ} (ht : 2 * Real.log 2 ≤ t) :
    t / 2 ≤ Real.log (⌊Real.exp t⌋₊ : ℝ) := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have htlog : Real.log 2 ≤ t := by linarith
  have hhalf := half_exp_le_natFloor_exp htlog
  have hhalfpos : 0 < Real.exp t / 2 := div_pos (Real.exp_pos _) (by norm_num)
  have hfloorpos : (0 : ℝ) < (⌊Real.exp t⌋₊ : ℝ) :=
    hhalfpos.trans_le hhalf
  have hlogmono : Real.log (Real.exp t / 2) ≤
      Real.log (⌊Real.exp t⌋₊ : ℝ) :=
    Real.strictMonoOn_log.monotoneOn
      (Set.mem_Ioi.mpr hhalfpos) (Set.mem_Ioi.mpr hfloorpos) hhalf
  rw [Real.log_div (Real.exp_ne_zero _) (by norm_num : (2 : ℝ) ≠ 0),
    Real.log_exp] at hlogmono
  linarith

/-- Convert a floor-based logarithmic theta estimate at `exp t` to a clean
power estimate in `t`. -/
lemma thetaFloor_logSaving_le_exp_div_pow {C t : ℝ} {m : ℕ}
    (hC : 0 ≤ C) (ht : 2 * Real.log 2 ≤ t)
    (htheta : |Chebyshev.theta (Real.exp t) - Real.exp t| ≤
      C * (⌊Real.exp t⌋₊ : ℝ) /
          Real.rpow (Real.log (⌊Real.exp t⌋₊ : ℝ)) (m : ℝ) + 1) :
    |Chebyshev.theta (Real.exp t) - Real.exp t| ≤
      C * (2 : ℝ) ^ m * Real.exp t / t ^ m + 1 := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have ht0 : 0 < t := by linarith
  have hfloorLe : ((⌊Real.exp t⌋₊ : ℕ) : ℝ) ≤ Real.exp t :=
    Nat.floor_le (Real.exp_pos _).le
  have hlogLower := half_le_log_natFloor_exp ht
  have hlog0 : 0 < Real.log (⌊Real.exp t⌋₊ : ℝ) := by
    have : 0 < t / 2 := by positivity
    exact this.trans_le hlogLower
  have hpowLower : (t / 2) ^ m ≤
      (Real.log (⌊Real.exp t⌋₊ : ℝ)) ^ m := by
    exact pow_le_pow_left₀ (by positivity) hlogLower m
  have hnum : C * ((⌊Real.exp t⌋₊ : ℕ) : ℝ) ≤ C * Real.exp t :=
    mul_le_mul_of_nonneg_left hfloorLe hC
  have hmain : C * ((⌊Real.exp t⌋₊ : ℕ) : ℝ) /
        (Real.log (⌊Real.exp t⌋₊ : ℝ)) ^ m ≤
      C * (2 : ℝ) ^ m * Real.exp t / t ^ m := by
    calc
      C * ((⌊Real.exp t⌋₊ : ℕ) : ℝ) /
          (Real.log (⌊Real.exp t⌋₊ : ℝ)) ^ m ≤
        C * Real.exp t /
          (Real.log (⌊Real.exp t⌋₊ : ℝ)) ^ m :=
        div_le_div_of_nonneg_right hnum (by positivity)
      _ ≤ C * Real.exp t / (t / 2) ^ m :=
        div_le_div_of_nonneg_left (mul_nonneg hC (Real.exp_pos _).le)
          (by positivity) hpowLower
      _ = C * (2 : ℝ) ^ m * Real.exp t / t ^ m := by
        field_simp
        rw [div_pow]
        field_simp
  have htheta' : |Chebyshev.theta (Real.exp t) - Real.exp t| ≤
      C * (⌊Real.exp t⌋₊ : ℝ) /
          (Real.log (⌊Real.exp t⌋₊ : ℝ)) ^ m + 1 := by
    have hpowEq : Real.rpow (Real.log (⌊Real.exp t⌋₊ : ℝ)) (m : ℝ) =
        (Real.log (⌊Real.exp t⌋₊ : ℝ)) ^ m := by
      simpa using! (Real.rpow_natCast
        (Real.log (⌊Real.exp t⌋₊ : ℝ)) m)
    rw [hpowEq] at htheta
    exact htheta
  linarith

/-- Uniform polynomial form of the logarithmic-block theta error. -/
theorem exists_logBlockThetaError_le_exp_div_pow_add_two (m : ℕ) :
    ∃ A : ℝ, 0 < A ∧
      ∃ X0 : ℕ, 4 ≤ X0 ∧
        ∀ K i : ℕ, 0 < K →
          2 * Real.log 2 ≤ (i : ℝ) / K →
          X0 ≤ ⌊Real.exp ((i : ℝ) / K)⌋₊ →
          X0 ≤ ⌊Real.exp (((i + 1 : ℕ) : ℝ) / K)⌋₊ →
          logBlockThetaError K i ≤
            A * Real.exp ((i : ℝ) / K) / (((i : ℝ) / K) ^ m) + 2 := by
  obtain ⟨C, hC, X0, hX0, hbound⟩ :=
    exists_abs_chebyshevTheta_sub_real_le_logSaving_floor (m : ℝ) (by positivity)
  let Q : ℝ := C * (2 : ℝ) ^ m
  let A : ℝ := Q * (1 + Real.exp 1)
  have hQ : 0 < Q := mul_pos hC (by positivity)
  have hA : 0 < A := mul_pos hQ (by positivity)
  refine ⟨A, hA, X0, hX0, ?_⟩
  intro K i hK ht haFloor hbFloor
  let t : ℝ := (i : ℝ) / K
  let u : ℝ := ((i + 1 : ℕ) : ℝ) / K
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have ht0 : 0 < t := by
    dsimp only [t]
    linarith [Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have huEq : u = t + (K : ℝ)⁻¹ := by
    dsimp only [t, u]
    norm_num only [Nat.cast_add, Nat.cast_one]
    field_simp
  have htu : t ≤ u := by
    rw [huEq]
    exact le_add_of_nonneg_right (inv_nonneg.mpr hKR.le)
  have huScale : 2 * Real.log 2 ≤ u := ht.trans htu
  have hthetaA := hbound (Real.exp t) (by simpa only [t] using haFloor)
  have hthetaB := hbound (Real.exp u) (by simpa only [u] using hbFloor)
  have hAerr : |Chebyshev.theta (Real.exp t) - Real.exp t| ≤
      Q * Real.exp t / t ^ m + 1 := by
    simpa only [Q] using thetaFloor_logSaving_le_exp_div_pow hC.le ht hthetaA
  have hBerr0 : |Chebyshev.theta (Real.exp u) - Real.exp u| ≤
      Q * Real.exp u / u ^ m + 1 := by
    simpa only [Q] using thetaFloor_logSaving_le_exp_div_pow hC.le huScale hthetaB
  have hinvLe : (K : ℝ)⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ (by exact_mod_cast hK)
  have huUpper : u ≤ t + 1 := by rw [huEq]; linarith
  have hexpUpper : Real.exp u ≤ Real.exp 1 * Real.exp t := by
    calc
      Real.exp u ≤ Real.exp (t + 1) := Real.exp_le_exp.mpr huUpper
      _ = Real.exp 1 * Real.exp t := by rw [Real.exp_add]; ring
  have hpowLower : t ^ m ≤ u ^ m := pow_le_pow_left₀ ht0.le htu m
  have hBmain : Q * Real.exp u / u ^ m ≤
      Q * Real.exp 1 * Real.exp t / t ^ m := by
    calc
      Q * Real.exp u / u ^ m ≤
          Q * (Real.exp 1 * Real.exp t) / u ^ m :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexpUpper hQ.le) (by positivity)
      _ ≤ Q * (Real.exp 1 * Real.exp t) / t ^ m :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hpowLower
      _ = Q * Real.exp 1 * Real.exp t / t ^ m := by ring
  have hBerr : |Chebyshev.theta (Real.exp u) - Real.exp u| ≤
      Q * Real.exp 1 * Real.exp t / t ^ m + 1 := by linarith
  have hinc := abs_thetaIncrement_sub_length_le_endpoint_errors
    (a := Real.exp t) (b := Real.exp u)
  have hdef : logBlockThetaError K i =
      |(Chebyshev.theta (Real.exp u) - Chebyshev.theta (Real.exp t)) -
        (Real.exp u - Real.exp t)| := by
    unfold logBlockThetaError
    congr 1 <;> simp only [t, u]
  change logBlockThetaError K i ≤ A * Real.exp t / t ^ m + 2
  rw [hdef]
  calc
    |(Chebyshev.theta (Real.exp u) - Chebyshev.theta (Real.exp t)) -
        (Real.exp u - Real.exp t)| ≤
      |Chebyshev.theta (Real.exp u) - Real.exp u| +
        |Chebyshev.theta (Real.exp t) - Real.exp t| := hinc
    _ ≤ (Q * Real.exp 1 * Real.exp t / t ^ m + 1) +
        (Q * Real.exp t / t ^ m + 1) := add_le_add hBerr hAerr
    _ = A * Real.exp t / t ^ m + 2 := by
      dsimp only [A]
      ring

/-- Absorb the harmless endpoint-floor constant once `exp t` dominates the
chosen power of `t`. -/
theorem exists_logBlockThetaError_le_relative_pow (m : ℕ) :
    ∃ A : ℝ, 0 < A ∧
      ∃ X0 : ℕ, 4 ≤ X0 ∧
        ∀ K i : ℕ, 0 < K →
          2 * Real.log 2 ≤ (i : ℝ) / K →
          (((i : ℝ) / K) ^ m) ≤ Real.exp ((i : ℝ) / K) →
          X0 ≤ ⌊Real.exp ((i : ℝ) / K)⌋₊ →
          X0 ≤ ⌊Real.exp (((i + 1 : ℕ) : ℝ) / K)⌋₊ →
          logBlockThetaError K i ≤
            A * Real.exp ((i : ℝ) / K) * (((K : ℝ) / i) ^ m) := by
  obtain ⟨A, hA, X0, hX0, hbound⟩ :=
    exists_logBlockThetaError_le_exp_div_pow_add_two m
  refine ⟨A + 2, by linarith, X0, hX0, ?_⟩
  intro K i hK ht hpoly ha hb
  have hi0 : (0 : ℝ) < i := by
    have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hratio : 0 < (i : ℝ) / K := by linarith
    rcases div_pos_iff.mp hratio with hpos | hneg
    · exact hpos.1
    · have hKR' : (0 : ℝ) < K := by exact_mod_cast hK
      linarith [hneg.2]
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have ht0 : 0 < (i : ℝ) / K := div_pos hi0 hKR
  have hpow0 : 0 < ((i : ℝ) / K) ^ m := pow_pos ht0 _
  have htwo : (2 : ℝ) ≤
      2 * Real.exp ((i : ℝ) / K) / (((i : ℝ) / K) ^ m) := by
    rw [le_div_iff₀ hpow0]
    nlinarith
  have hraw := hbound K i hK ht ha hb
  have hdiv : logBlockThetaError K i ≤
      (A + 2) * Real.exp ((i : ℝ) / K) /
        (((i : ℝ) / K) ^ m) := by
    calc
      logBlockThetaError K i ≤
          A * Real.exp ((i : ℝ) / K) / (((i : ℝ) / K) ^ m) + 2 := hraw
      _ ≤ A * Real.exp ((i : ℝ) / K) / (((i : ℝ) / K) ^ m) +
          2 * Real.exp ((i : ℝ) / K) / (((i : ℝ) / K) ^ m) := by
        linarith
      _ = (A + 2) * Real.exp ((i : ℝ) / K) /
          (((i : ℝ) / K) ^ m) := by ring
  calc
    logBlockThetaError K i ≤
        (A + 2) * Real.exp ((i : ℝ) / K) /
          (((i : ℝ) / K) ^ m) := hdiv
    _ = (A + 2) * Real.exp ((i : ℝ) / K) *
          (((K : ℝ) / i) ^ m) := by
      rw [div_pow, div_pow]
      field_simp

/-- Algebraic reduction used after the analytic endpoint estimate: a relative
theta error of order `(K/i)^m` contributes one additional power to the
reciprocal-mass error. -/
lemma logBlockMassError_le_of_thetaError {K i m : ℕ} {A : ℝ}
    (hK : 0 < K) (hi : 0 < i) (hA : 0 ≤ A)
    (htheta : logBlockThetaError K i ≤
      A * Real.exp ((i : ℝ) / K) * (((K : ℝ) / i) ^ m)) :
    logBlockMassError K i ≤
      1 / ((K : ℝ) * i) + 1 / ((i : ℝ) * (i + 1)) +
        A * (((K : ℝ) / i) ^ (m + 1)) := by
  have hKR : (0 : ℝ) ≤ K := by positivity
  have hiR : (0 : ℝ) ≤ i := by positivity
  have hratio : 0 ≤ (K : ℝ) / i := div_nonneg hKR hiR
  have hcoef : 0 ≤ ((K : ℝ) / i) *
      Real.exp (-((i : ℝ) / K)) := mul_nonneg hratio (Real.exp_pos _).le
  unfold logBlockMassError
  have htail :
    (K : ℝ) / i * Real.exp (-((i : ℝ) / K)) *
        logBlockThetaError K i ≤
      A * ((K : ℝ) / i) ^ (m + 1) := by
    calc
      (K : ℝ) / i * Real.exp (-((i : ℝ) / K)) *
          logBlockThetaError K i ≤
        (K : ℝ) / i * Real.exp (-((i : ℝ) / K)) *
          (A * Real.exp ((i : ℝ) / K) * ((K : ℝ) / i) ^ m) :=
        mul_le_mul_of_nonneg_left htheta hcoef
      _ = A * ((K : ℝ) / i) ^ (m + 1) := by
        rw [Real.exp_neg]
        simp only [Nat.cast_add, Nat.cast_one, pow_succ]
        field_simp [Real.exp_ne_zero]
  linarith

/-- The quantitative theta estimate packaged in the exact form used by the
finite logarithmic-block summation.  The reciprocal-mass error has one more
power of `K / i` than the relative theta error. -/
theorem exists_logBlockMassError_le_pow (m : ℕ) :
    ∃ A : ℝ, 0 < A ∧
      ∃ X0 : ℕ, 4 ≤ X0 ∧
        ∀ K i : ℕ, 0 < K → 0 < i →
          2 * Real.log 2 ≤ (i : ℝ) / K →
          (((i : ℝ) / K) ^ m) ≤ Real.exp ((i : ℝ) / K) →
          X0 ≤ ⌊Real.exp ((i : ℝ) / K)⌋₊ →
          X0 ≤ ⌊Real.exp (((i + 1 : ℕ) : ℝ) / K)⌋₊ →
          logBlockMassError K i ≤
            1 / ((K : ℝ) * i) + 1 / ((i : ℝ) * (i + 1)) +
              A * (((K : ℝ) / i) ^ (m + 1)) := by
  obtain ⟨A, hA, X0, hX0, htheta⟩ :=
    exists_logBlockThetaError_le_relative_pow m
  refine ⟨A, hA, X0, hX0, ?_⟩
  intro K i hK hi ht hpoly ha hb
  exact logBlockMassError_le_of_thetaError hK hi hA.le
    (htheta K i hK ht hpoly ha hb)

/-- A simplified occupancy estimate obtained from any explicit majorant for
`logBlockMassError`. -/
lemma abs_logBlockOccupancy_sub_inv_le_of_massError {K i : ℕ} {E : ℝ}
    (hK : 0 < K) (hi : 0 < i) (hE : logBlockMassError K i ≤ E)
    (hE0 : 0 ≤ E) :
    |logBlockOccupancy K i - (i : ℝ)⁻¹| ≤
      E + ((i : ℝ)⁻¹ + E) ^ 2 / 2 := by
  have hbase := abs_logBlockOccupancy_sub_inv_le hK hi
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hsum : 0 ≤ (i : ℝ)⁻¹ + logBlockMassError K i :=
    add_nonneg (inv_nonneg.mpr hiR.le) (logBlockMassError_nonneg hK hi)
  have hsum' : 0 ≤ (i : ℝ)⁻¹ + E :=
    add_nonneg (inv_nonneg.mpr hiR.le) hE0
  have hsq : ((i : ℝ)⁻¹ + logBlockMassError K i) ^ 2 ≤
      ((i : ℝ)⁻¹ + E) ^ 2 := by
    have hle : (i : ℝ)⁻¹ + logBlockMassError K i ≤
        (i : ℝ)⁻¹ + E := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hle) (add_nonneg hsum hsum')]
  have hdiv := div_le_div_of_nonneg_right hsq (by norm_num : (0 : ℝ) ≤ 2)
  linarith

/-- Once the analytic tail is no larger than the main reciprocal scale, the
quadratic Bonferroni correction is bounded by `8 / i^2`.  This is the
pointwise form needed by the finite error summation. -/
lemma abs_logBlockOccupancy_sub_inv_le_massPow_twenty_five
    {K i : ℕ} {A : ℝ} (hK : 0 < K) (hi : 0 < i) (hA : 0 ≤ A)
    (hmass : logBlockMassError K i ≤
      1 / ((K : ℝ) * i) + 1 / ((i : ℝ) * (i + 1)) +
        A * (((K : ℝ) / i) ^ 25))
    (htail : A * (((K : ℝ) / i) ^ 25) ≤ 1 / (i : ℝ)) :
    |logBlockOccupancy K i - (i : ℝ)⁻¹| ≤
      1 / ((K : ℝ) * i) + 1 / ((i : ℝ) * (i + 1)) +
        A * (((K : ℝ) / i) ^ 25) + 8 / (i : ℝ) ^ 2 := by
  let E : ℝ :=
    1 / ((K : ℝ) * i) + 1 / ((i : ℝ) * (i + 1)) +
      A * (((K : ℝ) / i) ^ 25)
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hiR : (0 : ℝ) < i := by exact_mod_cast hi
  have hmesh : 1 / ((K : ℝ) * i) ≤ 1 / (i : ℝ) := by
    apply one_div_le_one_div_of_le hiR
    nlinarith
  have hstep : 1 / ((i : ℝ) * (i + 1)) ≤ 1 / (i : ℝ) := by
    apply one_div_le_one_div_of_le hiR
    nlinarith
  have hE0 : 0 ≤ E := by
    dsimp only [E]
    positivity
  have hE : E ≤ 3 / (i : ℝ) := by
    calc
      E = 1 / ((K : ℝ) * i) + 1 / ((i : ℝ) * (i + 1)) +
          A * (((K : ℝ) / i) ^ 25) := rfl
      _ ≤ 1 / (i : ℝ) + 1 / (i : ℝ) + 1 / (i : ℝ) :=
        add_le_add (add_le_add hmesh hstep) htail
      _ = 3 / (i : ℝ) := by ring
  have hocc : |logBlockOccupancy K i - (i : ℝ)⁻¹| ≤
      E + ((i : ℝ)⁻¹ + E) ^ 2 / 2 := by
    apply abs_logBlockOccupancy_sub_inv_le_of_massError hK hi
    · simpa only [E] using hmass
    · exact hE0
  have hsum0 : 0 ≤ (i : ℝ)⁻¹ + E :=
    add_nonneg (inv_nonneg.mpr hiR.le) hE0
  have hfour0 : 0 ≤ 4 / (i : ℝ) := by positivity
  have hsum : (i : ℝ)⁻¹ + E ≤ 4 / (i : ℝ) := by
    calc
      (i : ℝ)⁻¹ + E ≤ 1 / (i : ℝ) + 3 / (i : ℝ) := by
        rw [inv_eq_one_div]
        exact add_le_add_right hE _
      _ = 4 / (i : ℝ) := by ring
  have hsq : ((i : ℝ)⁻¹ + E) ^ 2 ≤ (4 / (i : ℝ)) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hsum) (add_nonneg hsum0 hfour0)]
  have hquad : ((i : ℝ)⁻¹ + E) ^ 2 / 2 ≤ 8 / (i : ℝ) ^ 2 := by
    calc
      ((i : ℝ)⁻¹ + E) ^ 2 / 2 ≤ (4 / (i : ℝ)) ^ 2 / 2 :=
        div_le_div_of_nonneg_right hsq (by norm_num)
      _ = 8 / (i : ℝ) ^ 2 := by field_simp; norm_num
  change |logBlockOccupancy K i - (i : ℝ)⁻¹| ≤ E + 8 / (i : ℝ) ^ 2
  linarith

/-- Exact Abel summation of the reciprocal-prime prefix against the
Chebyshev theta function.  This is the identity to which the strong theta
remainder is applied on a logarithmic block. -/
theorem primeReciprocalPrefix_eq_theta_abel {x : ℝ} (hx : 2 ≤ x) :
    prime_summatory (fun p ↦ (p : ℝ)⁻¹) 2 x =
      Chebyshev.theta x * (x * Real.log x)⁻¹ +
        ∫ t in Set.Icc (2 : ℝ) x,
          Chebyshev.theta t *
            ((Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)) := by
  let a : ℕ → ℝ := fun n ↦ if n.Prime then Real.log n else 0
  let f : ℝ → ℝ := fun t ↦ (t * Real.log t)⁻¹
  let f' : ℝ → ℝ := fun t ↦
    -((Real.log t + 1) / (t ^ 2 * Real.log t ^ 2))
  have hdiff : ∀ t ∈ Set.Ici (2 : ℝ), HasDerivAt f (f' t) t := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := ht
    have ht0 : t ≠ 0 := by linarith
    have ht1 : 1 < t := by linarith
    have hlog0 : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    have hginv' : HasDerivAt f
        (-(Real.log t + 1) / (t * Real.log t) ^ 2) t := by
      simpa only [f] using!
        (Real.hasDerivAt_mul_log ht0).inv (mul_ne_zero ht0 hlog0)
    apply hginv'.congr_deriv
    dsimp [f']
    field_simp [ht0, hlog0]
  have hcont : ContinuousOn f' (Set.Ici (2 : ℝ)) := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := ht
    have ht0 : t ≠ 0 := by linarith
    have ht1 : 1 < t := by linarith
    have hlog0 : Real.log t ≠ 0 := (Real.log_pos ht1).ne'
    have hnum : ContinuousAt (fun y : ℝ ↦ Real.log y + 1) t := by fun_prop
    have hden : ContinuousAt (fun y : ℝ ↦ y ^ 2 * Real.log y ^ 2) t := by fun_prop
    exact ContinuousAt.continuousWithinAt (by
      dsimp [f']
      exact (hnum.div hden
        (mul_ne_zero (pow_ne_zero 2 ht0) (pow_ne_zero 2 hlog0))).neg)
  have hps := partial_summation_cont' a f f' two_ne_zero hdiff hcont x
  calc
    prime_summatory (fun p ↦ (p : ℝ)⁻¹) 2 x =
        summatory (fun n ↦ a n * f n) 2 x := by
      rw [prime_summatory_eq_summatory]
      apply congrArg (fun g : ℕ → ℝ ↦ summatory g 2 x)
      funext n
      by_cases hn : n.Prime
      · have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne_zero
        have hn1 : (1 : ℝ) < n := by exact_mod_cast hn.one_lt
        simp only [a, f, hn, if_true]
        field_simp [(Real.log_pos hn1).ne', hn0]
      · simp [a, hn]
    _ = summatory a 2 x * f x -
        ∫ t in Set.Icc (2 : ℝ) x, summatory a 2 t * f' t := hps
    _ = Chebyshev.theta x * (x * Real.log x)⁻¹ +
        ∫ t in Set.Icc (2 : ℝ) x,
          Chebyshev.theta t *
            ((Real.log t + 1) / (t ^ 2 * Real.log t ^ 2)) := by
      have ha : summatory a 2 = Chebyshev.theta := by
        rw [show Chebyshev.theta = chebyshev_first by rfl,
          chebyshev_first_eq_prime_summatory,
          prime_summatory_one_eq_prime_summatory_two,
          prime_summatory_eq_summatory]
      rw [ha]
      dsimp [f, f']
      simp_rw [mul_neg]
      rw [MeasureTheory.integral_neg]
      ring

/-- A fixed multiplicative prime block has reciprocal mass of order
`1 / log x`, with the constants obtained just by putting every reciprocal
between `1/(r*x)` and `1/x`.

The error `ε` is in the normalized PNT prime count.  This statement is fully
unconditional, but is intentionally not uniform as `r ↓ 1`. -/
theorem eventually_fixedRatio_mass_bounds {r ε : ℝ}
    (hr : 1 < r) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      (r - 1 - ε) / (r * Real.log x) ≤ mass r x ∧
        mass r x ≤ (r - 1 + ε) / Real.log x := by
  have hr0 : 0 < r := zero_lt_one.trans hr
  have hlower := eventually_mass_scaled_bounds hr (div_pos hε hr0)
  have hupper := eventually_mass_scaled_bounds hr hε
  filter_upwards [hlower, hupper, eventually_gt_atTop (1 : ℝ)] with x hl hu hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  constructor
  · rw [show (r - 1 - ε) / (r * Real.log x) =
        ((r - 1 - ε) / r) / Real.log x by field_simp]
    rw [div_le_iff₀ hlog]
    have hl' := hl.1
    have hconst : (r - 1) / r - ε / r = (r - 1 - ε) / r := by
      field_simp [hr0.ne']
    rw [hconst] at hl'
    simpa [mul_comm] using hl'.le
  · rw [le_div_iff₀ hlog]
    simpa [mul_comm] using hu.2.le

/-- A non-strict version convenient for downstream estimates. -/
theorem eventually_fixedRatio_mass_bounds_closed {r ε : ℝ}
    (hr : 1 < r) (hε : 0 < ε) :
    ∀ᶠ x : ℝ in atTop,
      (r - 1 - ε) / (r * Real.log x) ≤ mass r x ∧
        mass r x ≤ (r - 1 + ε) / Real.log x :=
  eventually_fixedRatio_mass_bounds hr hε

/-- At every fixed logarithmic resolution `K`, the normalized reciprocal
mass of the `i`-th logarithmic prime block is eventually trapped between
the two fixed-ratio PNT constants.  The quantifier order is important:
`K` is fixed before `i → ∞`. -/
theorem eventually_fixedResolution_logBlock_bounds {K : ℕ} {ε : ℝ}
    (hK : 0 < K) (hε : 0 < ε) :
    ∀ᶠ i : ℕ in atTop,
      (Real.exp ((K : ℝ)⁻¹) - 1) / Real.exp ((K : ℝ)⁻¹) - ε <
          ((i : ℝ) / K) * logBlockMass K i ∧
        ((i : ℝ) / K) * logBlockMass K i <
          Real.exp ((K : ℝ)⁻¹) - 1 + ε := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hr : (1 : ℝ) < Real.exp ((K : ℝ)⁻¹) :=
    Real.one_lt_exp_iff.mpr (inv_pos.mpr hKR)
  have hscale : Tendsto (fun i : ℕ ↦ Real.exp ((i : ℝ) / K)) atTop atTop := by
    apply Real.tendsto_exp_atTop.comp
    exact Tendsto.atTop_div_const hKR tendsto_natCast_atTop_atTop
  have hmass := eventually_mass_scaled_bounds hr hε
  filter_upwards [hscale.eventually hmass] with i hi
  simpa only [logBlockMass, Real.log_exp] using hi

end

end Erdos144.StrongMertens
