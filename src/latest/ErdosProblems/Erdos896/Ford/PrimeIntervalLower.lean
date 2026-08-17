/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.PrimeEstimates
import ErdosProblems.Erdos49.PNT.MediumPNT

/-!
# Lower bounds for factor-two prime intervals

This file is separated from `PrimeEstimates` because its input is the medium-strength
prime number theorem, whereas the upper estimates only require Mertens' theorems.
-/

namespace Erdos896.Ford

open Filter Asymptotics
open scoped BigOperators

private theorem sqrt_isLittleO_id :
    Real.sqrt =o[atTop] (_root_.id : ℝ → ℝ) := by
  have hratio : Tendsto (fun x : ℝ ↦ Real.sqrt x / x) atTop (nhds 0) := by
    have heq : (fun x : ℝ ↦ Real.sqrt x / x) =ᶠ[atTop]
        (fun x : ℝ ↦ (Real.sqrt x)⁻¹) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      conv_lhs => rhs; rw [← Real.mul_self_sqrt hx.le]
      field_simp [Real.sqrt_ne_zero'.mpr hx]
    rw [tendsto_congr' heq]
    exact tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  apply (isLittleO_iff_tendsto' ?_).2 hratio
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  exact fun h ↦ (hx.ne' h).elim

private theorem theta_sub_id_isLittleO :
    (Chebyshev.theta - _root_.id) =o[atTop] (_root_.id : ℝ → ℝ) := by
  obtain ⟨c, hc, hpnt⟩ := MediumPNT
  let ε : ℝ → ℝ := fun x ↦
    Real.exp (-c * Real.log x ^ ((1 : ℝ) / 10))
  have hpow : Tendsto
      (fun x : ℝ ↦ c * Real.log x ^ ((1 : ℝ) / 10)) atTop atTop :=
    Tendsto.const_mul_atTop hc
      ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < (1 : ℝ) / 10)).comp
        Real.tendsto_log_atTop)
  have hneg : Tendsto
      (fun x : ℝ ↦ -(c * Real.log x ^ ((1 : ℝ) / 10))) atTop atBot := by
    have h := tendsto_neg_atTop_atBot.comp hpow
    change Tendsto (fun x : ℝ ↦ -(c * Real.log x ^ ((1 : ℝ) / 10))) atTop atBot at h
    exact h
  have hε0 : Tendsto ε atTop (nhds 0) := by
    apply Real.tendsto_exp_atBot.comp
    simpa only [neg_mul] using hneg
  have hpntErrorLittle :
      (fun x : ℝ ↦ x * ε x) =o[atTop] (_root_.id : ℝ → ℝ) := by
    refine (isLittleO_iff_tendsto' ?_).2 ?_
    · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      exact fun h ↦ (hx.ne' h).elim
    · have heq : (fun x : ℝ ↦ (x * ε x) / _root_.id x) =ᶠ[atTop] ε := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        simp [_root_.id, hx.ne']
      rw [tendsto_congr' heq]
      exact hε0
  have hpsiLittle :
      (Chebyshev.psi - _root_.id) =o[atTop] (_root_.id : ℝ → ℝ) :=
    hpnt.trans_isLittleO hpntErrorLittle
  have hprimePowersLittle :
      (Chebyshev.psi - Chebyshev.theta) =o[atTop] (_root_.id : ℝ → ℝ) :=
    Chebyshev.isBigO_psi_sub_theta_sqrt.trans_isLittleO sqrt_isLittleO_id
  refine (hpsiLittle.sub hprimePowersLittle).congr' ?_ (Eventually.of_forall fun _ ↦ rfl)
  filter_upwards with x
  simp only [Pi.sub_apply, _root_.id_eq]
  ring

private lemma primesLE_subset_two_mul (U : ℕ) :
    Nat.primesLE U ⊆ Nat.primesLE (2 * U) := by
  intro p hp
  exact Nat.mem_primesLE.mpr
    ⟨(Nat.le_of_mem_primesLE hp).trans (by omega), Nat.prime_of_mem_primesLE hp⟩

/-- Eventually, the factor-two interval `(U, 2U]` contains at least
`U / (8 log U)` primes. -/
theorem eventually_one_eighth_mul_div_log_le_primeIntervalCard :
    ∃ U₀ : ℕ, ∀ U : ℕ, U₀ ≤ U →
      (1 / 8 : ℝ) * U / Real.log U ≤
        ((Nat.primesLE (2 * U) \ Nat.primesLE U).card : ℝ) := by
  have hthetaError : ∀ᶠ x : ℝ in atTop,
      ‖Chebyshev.theta x - x‖ ≤ (1 / 16 : ℝ) * ‖x‖ := by
    simpa only [Pi.sub_apply, _root_.id_eq] using
      theta_sub_id_isLittleO.bound (by norm_num : (0 : ℝ) < 1 / 16)
  obtain ⟨X, hX⟩ := eventually_atTop.1 hthetaError
  obtain ⟨N, hN⟩ := exists_nat_ge X
  refine ⟨max N 4, fun U hU ↦ ?_⟩
  have hUN : N ≤ U := (le_max_left N 4).trans hU
  have hU4 : 4 ≤ U := (le_max_right N 4).trans hU
  have hUR : X ≤ (U : ℝ) := hN.trans (by exact_mod_cast hUN)
  have hthetaU := hX (U : ℝ) hUR
  have htheta2U := hX (((2 * U : ℕ) : ℝ))
    (hUR.trans (by exact_mod_cast (show U ≤ 2 * U by omega)))
  have hUpos : (0 : ℝ) < U := by positivity
  have hlogU : 0 < Real.log U :=
    Real.log_pos (by exact_mod_cast (show 1 < U by omega))
  have hlog2U : 0 < Real.log (((2 * U : ℕ) : ℝ)) :=
    Real.log_pos (by exact_mod_cast (show 1 < 2 * U by omega))
  have hlogmul : Real.log (((2 * U : ℕ) : ℝ)) = Real.log 2 + Real.log U := by
    push_cast
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity : (U : ℝ) ≠ 0)]
  have hlog4le : Real.log 4 ≤ Real.log U := by
    exact Real.strictMonoOn_log.monotoneOn (by norm_num) (Set.mem_Ioi.mpr hUpos)
      (by exact_mod_cast hU4)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)]
    ring
  have hlog2U_le : Real.log (((2 * U : ℕ) : ℝ)) ≤
      (3 / 2 : ℝ) * Real.log U := by
    rw [hlogmul]
    rw [hlog4] at hlog4le
    linarith
  simp only [Real.norm_eq_abs, abs_of_pos hUpos,
    abs_of_pos (by push_cast; positivity : (0 : ℝ) < ((2 * U : ℕ) : ℝ))] at hthetaU htheta2U
  have hthetaDiff : (3 / 4 : ℝ) * U ≤
      Chebyshev.theta ((2 * U : ℕ) : ℝ) - Chebyshev.theta (U : ℝ) := by
    push_cast
    have hUabs := (abs_le.mp hthetaU).2
    have h2Uabs := (abs_le.mp htheta2U).1
    push_cast at hUabs h2Uabs
    linarith
  let s := Nat.primesLE (2 * U) \ Nat.primesLE U
  have hsubset : Nat.primesLE U ⊆ Nat.primesLE (2 * U) := primesLE_subset_two_mul U
  have hthetaDiffEq :
      Chebyshev.theta ((2 * U : ℕ) : ℝ) - Chebyshev.theta (U : ℝ) =
        ∑ p ∈ s, Real.log p := by
    dsimp [s]
    rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log,
      sub_eq_iff_eq_add]
    exact (Finset.sum_sdiff hsubset).symm
  have hsumCard : (∑ p ∈ s, Real.log p) ≤
      (s.card : ℝ) * Real.log (((2 * U : ℕ) : ℝ)) := by
    calc
      (∑ p ∈ s, Real.log p) ≤
          ∑ _p ∈ s, Real.log (((2 * U : ℕ) : ℝ)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hp' := Finset.mem_sdiff.mp hp
        exact Real.strictMonoOn_log.monotoneOn
          (Set.mem_Ioi.mpr (by
            exact_mod_cast (Nat.prime_of_mem_primesLE hp'.1).pos))
          (Set.mem_Ioi.mpr (by push_cast; positivity))
          (by exact_mod_cast Nat.le_of_mem_primesLE hp'.1)
      _ = (s.card : ℝ) * Real.log (((2 * U : ℕ) : ℝ)) := by simp
  have hcardLog : (3 / 4 : ℝ) * U ≤
      (s.card : ℝ) * Real.log (((2 * U : ℕ) : ℝ)) := by
    rw [← hthetaDiffEq] at hsumCard
    exact hthetaDiff.trans hsumCard
  have hcardLog' : (3 / 4 : ℝ) * U ≤
      (s.card : ℝ) * ((3 / 2 : ℝ) * Real.log U) :=
    hcardLog.trans (mul_le_mul_of_nonneg_left hlog2U_le (by positivity))
  change (1 / 8 : ℝ) * U / Real.log U ≤ (s.card : ℝ)
  apply (div_le_iff₀ hlogU).2
  nlinarith

/-- Existential-constant form of the factor-two prime-cardinality lower bound. -/
theorem exists_primeIntervalCard_two_mul_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ U₀ : ℕ, ∀ U : ℕ, U₀ ≤ U →
      c * U / Real.log U ≤
        ((Nat.primesLE (2 * U) \ Nat.primesLE U).card : ℝ) := by
  obtain ⟨U₀, h⟩ := eventually_one_eighth_mul_div_log_le_primeIntervalCard
  exact ⟨1 / 8, by norm_num, U₀, h⟩

/-- Eventually, the reciprocal mass of primes in `(U, 2U]` is at least
`1 / (16 log U)`. -/
theorem eventually_one_sixteenth_div_log_le_primeReciprocalIntervalSum :
    ∃ U₀ : ℕ, ∀ U : ℕ, U₀ ≤ U →
      (1 / 16 : ℝ) / Real.log U ≤ primeReciprocalIntervalSum U (2 * U) := by
  obtain ⟨U₀, hcard⟩ := eventually_one_eighth_mul_div_log_le_primeIntervalCard
  refine ⟨max U₀ 4, fun U hU ↦ ?_⟩
  have hU₀ : U₀ ≤ U := (le_max_left U₀ 4).trans hU
  have hU4 : 4 ≤ U := (le_max_right U₀ 4).trans hU
  have hUpos : (0 : ℝ) < U := by positivity
  have h2Upos : (0 : ℝ) < ((2 * U : ℕ) : ℝ) := by push_cast; positivity
  have hlogU : 0 < Real.log U :=
    Real.log_pos (by exact_mod_cast (show 1 < U by omega))
  let s := Nat.primesLE (2 * U) \ Nat.primesLE U
  have hmass : (s.card : ℝ) / ((2 * U : ℕ) : ℝ) ≤
      primeReciprocalIntervalSum U (2 * U) := by
    unfold primeReciprocalIntervalSum
    dsimp [s]
    calc
      (((Nat.primesLE (2 * U) \ Nat.primesLE U).card : ℝ) /
          ((2 * U : ℕ) : ℝ)) =
          ∑ _p ∈ Nat.primesLE (2 * U) \ Nat.primesLE U,
            (1 : ℝ) / ((2 * U : ℕ) : ℝ) := by simp [div_eq_mul_inv]
      _ ≤ ∑ p ∈ Nat.primesLE (2 * U) \ Nat.primesLE U, (1 : ℝ) / p := by
        apply Finset.sum_le_sum
        intro p hp
        have hpPrime := Nat.prime_of_mem_primesLE (Finset.mem_sdiff.mp hp).1
        exact one_div_le_one_div_of_le
          (by exact_mod_cast hpPrime.pos)
          (by exact_mod_cast Nat.le_of_mem_primesLE (Finset.mem_sdiff.mp hp).1)
  have hcard' := hcard U hU₀
  change (1 / 8 : ℝ) * U / Real.log U ≤ (s.card : ℝ) at hcard'
  calc
    (1 / 16 : ℝ) / Real.log U =
        ((1 / 8 : ℝ) * U / Real.log U) / ((2 * U : ℕ) : ℝ) := by
      push_cast
      field_simp
      ring
    _ ≤ (s.card : ℝ) / ((2 * U : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hcard' h2Upos.le
    _ ≤ primeReciprocalIntervalSum U (2 * U) := hmass

/-- Existential-constant form of the factor-two reciprocal-prime lower bound. -/
theorem exists_primeReciprocalIntervalSum_two_mul_lower :
    ∃ c : ℝ, 0 < c ∧ ∃ U₀ : ℕ, ∀ U : ℕ, U₀ ≤ U →
      c / Real.log U ≤ primeReciprocalIntervalSum U (2 * U) := by
  obtain ⟨U₀, h⟩ := eventually_one_sixteenth_div_log_le_primeReciprocalIntervalSum
  exact ⟨1 / 16, by norm_num, U₀, h⟩

end Erdos896.Ford
