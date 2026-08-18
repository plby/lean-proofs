/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1161.Basic
import ErdosProblems.Erdos1161.DivisorBounds
import ErdosProblems.Erdos1161.NearDivisor
import ErdosProblems.Erdos1161.PrimePowerAvoidance
import ErdosProblems.Erdos1161.LargeOrders

/-!
# The structural part of Beker's theorem

This file contains the global part of the resolution of Erdős Problem 1161.
It first records the exact translations between normalized probabilities and
integer counts, and the elementary arithmetic separation lemma used in the
first-cycle argument.
-/

open scoped BigOperators Topology
open Filter Asymptotics

namespace Erdos1161

/-- The polynomial box used throughout the structural argument: the
large-order cutoff `m³ ≤ n⁴` in particular places `m` below `n²`. -/
theorem le_sq_of_cube_le_fourth {n m : ℕ} (hn : 0 < n)
    (h : m ^ 3 ≤ n ^ 4) : m ≤ n ^ 2 := by
  by_contra hnot
  have hmn : n ^ 2 < m := Nat.lt_of_not_ge hnot
  have hn4le6 : n ^ 4 ≤ n ^ 6 := by
    exact Nat.pow_le_pow_right (by omega) (by omega)
  have hcube : n ^ 6 < m ^ 3 := by
    nlinarith [Nat.mul_self_le_mul_self (Nat.le_of_lt hmn)]
  omega

private theorem eventually_const_mul_eighth_rpow_lt_self (C : ℝ) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ (1 / 8 : ℝ) < n := by
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (7 / 8 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 7 / 8)).comp
      tendsto_natCast_atTop_atTop
  filter_upwards [(tendsto_atTop.1 ht) (C + 1), eventually_gt_atTop 0]
      with n hnC hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (n : ℝ) ^ (7 / 8 : ℝ) * (n : ℝ) ^ (1 / 8 : ℝ) = n := by
    rw [← Real.rpow_add hnR]
    norm_num
  calc
    C * (n : ℝ) ^ (1 / 8 : ℝ)
        < (n : ℝ) ^ (7 / 8 : ℝ) * (n : ℝ) ^ (1 / 8 : ℝ) := by
          apply mul_lt_mul_of_pos_right _ (Real.rpow_pos_of_pos hnR _)
          linarith
    _ = n := hpow

/-- Uniformly on the polynomial box `m³ ≤ n⁴`, every fixed multiple of
`τ(m)²` is eventually smaller than `√n`.  This single integer inequality
supplies all of the explicit error thresholds in the near-divisor and
prime-power steps. -/
theorem eventually_const_mul_divisorCount_sq_lt_sqrt (C : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m → m ^ 3 ≤ n ^ 4 →
      C * divisorCount m ^ 2 < n.sqrt := by
  obtain ⟨N₀, hN₀⟩ :=
    exists_uniform_divisorCount_power_le_eighth 4 (by norm_num)
  filter_upwards [eventually_ge_atTop N₀,
      eventually_const_mul_eighth_rpow_lt_self (((C + 1) ^ 2 : ℕ) : ℝ),
      eventually_gt_atTop 0] with n hnN hgrowth hn
  intro m hm hmn
  have hmle2 : m ≤ n ^ 2 := le_sq_of_cube_le_fourth hn hmn
  have hmle4 : m ≤ n ^ 4 :=
    hmle2.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have htau := hN₀ n hnN m (by omega) hmle4
  have htau1 : 1 ≤ divisorCount m := by
    rw [divisorCount]
    apply Finset.card_pos.mpr
    exact ⟨1, Nat.mem_divisors.mpr ⟨one_dvd m, hm.ne'⟩⟩
  by_contra hnot
  have hsqrt : n.sqrt ≤ C * divisorCount m ^ 2 := Nat.le_of_not_gt hnot
  have hnlt : n < (n.sqrt + 1) ^ 2 := by simpa using Nat.lt_succ_sqrt' n
  have hstep : C * divisorCount m ^ 2 + 1 ≤
      (C + 1) * divisorCount m ^ 2 := by
    nlinarith [show 1 ≤ divisorCount m ^ 2 from
      Nat.one_le_pow 2 (divisorCount m) (by omega)]
  have hpow1 : (n.sqrt + 1) ^ 2 ≤
      (C * divisorCount m ^ 2 + 1) ^ 2 := by
    nlinarith [Nat.mul_self_le_mul_self
      (by omega : n.sqrt + 1 ≤ C * divisorCount m ^ 2 + 1)]
  have hpow2 : (C * divisorCount m ^ 2 + 1) ^ 2 ≤
      ((C + 1) * divisorCount m ^ 2) ^ 2 := by
    nlinarith [Nat.mul_self_le_mul_self hstep]
  have hnat : n < (C + 1) ^ 2 * divisorCount m ^ 4 := by
    calc
      n < (n.sqrt + 1) ^ 2 := hnlt
      _ ≤ (C * divisorCount m ^ 2 + 1) ^ 2 := hpow1
      _ ≤ ((C + 1) * divisorCount m ^ 2) ^ 2 := hpow2
      _ = (C + 1) ^ 2 * divisorCount m ^ 4 := by ring
  have hreal : (n : ℝ) <
      (((C + 1) ^ 2 : ℕ) : ℝ) * (divisorCount m : ℝ) ^ 4 := by
    exact_mod_cast hnat
  have hupper :
      (((C + 1) ^ 2 : ℕ) : ℝ) * (divisorCount m : ℝ) ^ 4 ≤
        (((C + 1) ^ 2 : ℕ) : ℝ) * (n : ℝ) ^ (1 / 8 : ℝ) := by
    exact mul_le_mul_of_nonneg_left htau (by positivity)
  linarith

/-- The corresponding uniform estimate for any fixed positive power of the
divisor function.  The cubic instance is used to compare the structural
error with the probability of seeing the missing prime power. -/
theorem eventually_const_mul_divisorCount_pow_lt_sqrt
    (C k : ℕ) (hk : 0 < k) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, 0 < m → m ^ 3 ≤ n ^ 4 →
      C * divisorCount m ^ k < n.sqrt := by
  obtain ⟨N₀, hN₀⟩ :=
    exists_uniform_divisorCount_power_le_eighth (2 * k) (by omega)
  filter_upwards [eventually_ge_atTop N₀,
      eventually_const_mul_eighth_rpow_lt_self (((C + 1) ^ 2 : ℕ) : ℝ),
      eventually_gt_atTop 0] with n hnN hgrowth hn
  intro m hm hmn
  have hmle2 : m ≤ n ^ 2 := le_sq_of_cube_le_fourth hn hmn
  have hmle : m ≤ n ^ (2 * k) :=
    hmle2.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have htau := hN₀ n hnN m (by omega) hmle
  have htau' : ((divisorCount m ^ k : ℕ) : ℝ) ^ 2 ≤
      (n : ℝ) ^ (1 / 8 : ℝ) := by
    simpa [Nat.cast_pow, ← pow_mul, Nat.mul_comm] using htau
  have htau1 : 1 ≤ divisorCount m := by
    rw [divisorCount]
    apply Finset.card_pos.mpr
    exact ⟨1, Nat.mem_divisors.mpr ⟨one_dvd m, hm.ne'⟩⟩
  let T := divisorCount m ^ k
  have hT1 : 1 ≤ T := by
    dsimp [T]
    exact Nat.one_le_pow k (divisorCount m) (by omega)
  by_contra hnot
  have hsqrt : n.sqrt ≤ C * T := by
    simpa [T] using Nat.le_of_not_gt hnot
  have hnlt : n < (n.sqrt + 1) ^ 2 := by simpa using Nat.lt_succ_sqrt' n
  have hstep : C * T + 1 ≤ (C + 1) * T := by nlinarith
  have hpow1 : (n.sqrt + 1) ^ 2 ≤ (C * T + 1) ^ 2 := by
    nlinarith [Nat.mul_self_le_mul_self
      (by omega : n.sqrt + 1 ≤ C * T + 1)]
  have hpow2 : (C * T + 1) ^ 2 ≤ ((C + 1) * T) ^ 2 := by
    nlinarith [Nat.mul_self_le_mul_self hstep]
  have hnat : n < (C + 1) ^ 2 * T ^ 2 := by
    calc
      n < (n.sqrt + 1) ^ 2 := hnlt
      _ ≤ (C * T + 1) ^ 2 := hpow1
      _ ≤ ((C + 1) * T) ^ 2 := hpow2
      _ = (C + 1) ^ 2 * T ^ 2 := by ring
  have hreal : (n : ℝ) < (((C + 1) ^ 2 : ℕ) : ℝ) * (T : ℝ) ^ 2 := by
    exact_mod_cast hnat
  have hupper : (((C + 1) ^ 2 : ℕ) : ℝ) * (T : ℝ) ^ 2 ≤
      (((C + 1) ^ 2 : ℕ) : ℝ) * (n : ℝ) ^ (1 / 8 : ℝ) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa [T] using htau'
  linarith

private theorem natCast_div_lt_inv_of_mul_lt
    {a b C : ℕ} (hb : 0 < b) (hC : 0 < C) (h : C * a < b) :
    (a : ℚ) / b < 1 / C := by
  rw [div_lt_div_iff₀ (by exact_mod_cast hb : (0 : ℚ) < b)
    (by exact_mod_cast hC : (0 : ℚ) < C)]
  exact_mod_cast (by simpa [Nat.mul_comm] using h)

/-! ## Exact normalization and the universal lower bound -/

/-- At positive degree, Beker's probability threshold `1 / n` is exactly
the count threshold `(n - 1)!`. -/
theorem one_div_le_orderProbability_iff {n m : ℕ} (hn : 0 < n) :
    (1 : ℝ) / n ≤ orderProbability n m ↔
      (n - 1).factorial ≤ orderCount n m := by
  rw [orderProbability, div_le_div_iff₀ (by positivity : (0 : ℝ) < n)
    (by positivity : (0 : ℝ) < (n.factorial : ℝ))]
  rw [one_mul, ← Nat.cast_mul, factorial_eq_mul_pred_factorial hn]
  norm_cast
  constructor
  · intro h
    have h' : (n - 1).factorial * n ≤ orderCount n m * n := by
      simpa only [Nat.mul_comm n (n - 1).factorial] using h
    exact Nat.le_of_mul_le_mul_right h' hn
  · intro h
    simpa [mul_comm] using Nat.mul_le_mul_left n h

/-- The count version of `one_div_le_orderProbability_iff`. -/
theorem orderProbability_ge_one_div_of_orderCount_ge_factorial
    {n m : ℕ} (hn : 0 < n)
    (h : (n - 1).factorial ≤ orderCount n m) :
    (1 : ℝ) / n ≤ orderProbability n m :=
  (one_div_le_orderProbability_iff hn).2 h

/-- Rational normalization of the same threshold, in the form consumed by
the exact first-cycle recurrence. -/
theorem one_div_le_orderRationalProbability_of_orderProbability
    {n m : ℕ} (hn : 0 < n)
    (h : (1 : ℝ) / n ≤ orderProbability n m) :
    (1 / n : ℚ) ≤ (orderCount n m : ℚ) / (n.factorial : ℚ) := by
  have hc : (n - 1).factorial ≤ orderCount n m :=
    (one_div_le_orderProbability_iff hn).1 h
  rw [div_le_div_iff₀ (by positivity : (0 : ℚ) < n)
    (by positivity : (0 : ℚ) < n.factorial)]
  rw [one_mul, factorial_eq_mul_pred_factorial hn]
  push_cast
  exact_mod_cast (by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left n hc)

/-- A full `n`-cycle has order `n`; there are exactly `(n-1)!` of them.
Consequently the order-`n` fiber gives the lower bound in Theorem 1.1. -/
theorem pred_factorial_le_orderCount_self {n : ℕ} (hn : 0 < n) :
    (n - 1).factorial ≤ orderCount n n := by
  by_cases hn1 : n = 1
  · subst n
    norm_num [orderCount]
  · have hn2 : 2 ≤ n := by omega
    let cycles : Finset (Equiv.Perm (Fin n)) :=
      Finset.univ.filter (fun σ ↦ σ.cycleType = ({n} : Multiset ℕ))
    have hcycles : cycles.card = (n - 1).factorial := by
      simpa [cycles] using
        (Equiv.Perm.card_of_cycleType_singleton (n := n) hn2
          (by simp : n ≤ Fintype.card (Fin n)))
    rw [orderCount_eq_card_filter, ← hcycles]
    apply Finset.card_le_card
    intro σ hσ
    rw [Finset.mem_filter] at hσ ⊢
    refine ⟨hσ.1, ?_⟩
    rw [← Equiv.Perm.lcm_cycleType, hσ.2]
    simp

theorem one_div_le_orderProbability_self {n : ℕ} (hn : 0 < n) :
    (1 : ℝ) / n ≤ orderProbability n n :=
  orderProbability_ge_one_div_of_orderCount_ge_factorial hn
    (pred_factorial_le_orderCount_self hn)

theorem pred_factorial_le_maxOrderCount {n : ℕ} (hn : 0 < n) :
    (n - 1).factorial ≤ maxOrderCount n :=
  (pred_factorial_le_orderCount_self hn).trans
    (orderCount_le_maxOrderCount n n)

theorem one_div_le_maxOrderProbability {n : ℕ} (hn : 0 < n) :
    (1 : ℝ) / n ≤ maxOrderProbability n := by
  obtain ⟨m, _, hm⟩ := exists_orderCount_eq_maxOrderCount n
  have hmode : IsMode n m := isMode_iff_orderCount_eq_maxOrderCount.2 hm
  rw [maxOrderProbability_eq_orderProbability_of_isMode hmode]
  exact (one_div_le_orderProbability_iff hn).2
    ((pred_factorial_le_orderCount_self hn).trans (hmode n))

/-- Multiplying Beker's normalized asymptotic by `n!` gives the count
asymptotic with comparison function `(n-1)!`. -/
theorem maxOrderCount_isEquivalent_pred_factorial_of_probability
    (hprob : (fun n : ℕ ↦ maxOrderProbability n) ~[atTop]
      (fun n : ℕ ↦ (1 : ℝ) / n)) :
    (fun n : ℕ ↦ (maxOrderCount n : ℝ)) ~[atTop]
      (fun n : ℕ ↦ ((n - 1).factorial : ℝ)) := by
  have hprobDen : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / n ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    positivity
  have hratio :=
    (Asymptotics.isEquivalent_iff_tendsto_one hprobDen).mp hprob
  have hcountDen : ∀ᶠ n : ℕ in atTop,
      ((n - 1).factorial : ℝ) ≠ 0 :=
    Filter.Eventually.of_forall fun n ↦ by positivity
  apply (Asymptotics.isEquivalent_iff_tendsto_one hcountDen).mpr
  apply hratio.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  change maxOrderProbability n / ((1 : ℝ) / n) =
    (maxOrderCount n : ℝ) / ((n - 1).factorial : ℝ)
  rw [maxOrderProbability, factorial_eq_mul_pred_factorial hn]
  push_cast
  field_simp

/-- A uniform eventual upper bound matching the `n`-cycle lower bound is
enough to establish Beker's normalized asymptotic.  The structural argument
below supplies precisely this upper bound. -/
theorem maxOrderProbability_isEquivalent_of_eventually_upper
    (hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      maxOrderProbability n ≤ (1 + ε) / n) :
    (fun n : ℕ ↦ maxOrderProbability n) ~[atTop]
      (fun n : ℕ ↦ (1 : ℝ) / n) := by
  have hden : ∀ᶠ n : ℕ in atTop, (1 : ℝ) / n ≠ 0 := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    positivity
  apply (Asymptotics.isEquivalent_iff_tendsto_one hden).mpr
  rw [tendsto_order]
  constructor
  · intro a ha
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hlower := one_div_le_maxOrderProbability hn
    have hdenpos : (0 : ℝ) < 1 / n := by positivity
    have hone : (1 : ℝ) ≤ maxOrderProbability n / (1 / n) :=
      (le_div_iff₀ hdenpos).2 (by simpa using hlower)
    exact ha.trans_le hone
  · intro b hb
    let ε : ℝ := (b - 1) / 2
    have hε : 0 < ε := by dsimp [ε]; linarith
    filter_upwards [eventually_gt_atTop 0, hupper ε hε] with n hn hnupper
    have hdenpos : (0 : ℝ) < 1 / n := by positivity
    have hratio : maxOrderProbability n / (1 / n) ≤ 1 + ε := by
      apply (div_le_iff₀ hdenpos).2
      simpa [div_eq_mul_inv, mul_assoc] using hnupper
    exact hratio.trans_lt (by dsimp [ε]; linarith)

theorem maxOrderCount_isEquivalent_pred_factorial_of_eventually_upper
    (hupper : ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      maxOrderProbability n ≤ (1 + ε) / n) :
    (fun n : ℕ ↦ (maxOrderCount n : ℝ)) ~[atTop]
      (fun n : ℕ ↦ ((n - 1).factorial : ℝ)) :=
  maxOrderCount_isEquivalent_pred_factorial_of_probability
    (maxOrderProbability_isEquivalent_of_eventually_upper hupper)

/-! ## Orders of residual permutations -/

/-- The order of a permutation on `s` letters divides
`lcm(1,…,s)`.  This is the group-theoretic reason that Beker's lcm
condition makes the residual permutation irrelevant. -/
theorem orderOf_perm_dvd_lcmUpto {s : ℕ} (σ : Equiv.Perm (Fin s)) :
    orderOf σ ∣ Nat.lcmUpto s := by
  rw [← Equiv.Perm.lcm_cycleType, Multiset.lcm_dvd]
  intro d hd
  apply Finset.dvd_lcm
  refine Finset.mem_Icc.mpr ⟨?_, ?_⟩
  · exact (Equiv.Perm.two_le_of_mem_cycleType hd).trans' (by omega)
  · exact (Equiv.Perm.le_card_support_of_mem_cycleType hd).trans
      (by simpa using Finset.card_le_univ σ.support)

theorem lcm_orderOf_eq_of_lcmUpto_dvd {s d : ℕ}
    (hd : Nat.lcmUpto s ∣ d) (σ : Equiv.Perm (Fin s)) :
    Nat.lcm (orderOf σ) d = d :=
  Nat.lcm_eq_right ((orderOf_perm_dvd_lcmUpto σ).trans hd)

/-- A Beker candidate `m ≤ n` absorbs the order of every permutation on
the `n-m` residual letters. -/
theorem lcm_residual_order_eq_candidate {n m : ℕ}
    (hm : BekerCandidate n m) (σ : Equiv.Perm (Fin (n - m))) :
    Nat.lcm (orderOf σ) m = m :=
  lcm_orderOf_eq_of_lcmUpto_dvd hm.2 σ

/-- Once a near divisor `d` absorbs every residual cycle length, a single
successful residual permutation forces the target order to be exactly `d`.
This packages the final deterministic step of Beker's structural argument. -/
theorem eq_and_bekerCandidate_of_residual_witness
    {n m d : ℕ} (hd : 0 < d)
    (hlcm : Nat.lcmUpto (n - d) ∣ d)
    (σ : Equiv.Perm (Fin (n - d)))
    (hsuccess : Nat.lcm (orderOf σ) d = m) :
    m = d ∧ BekerCandidate n m := by
  have habsorb : Nat.lcm (orderOf σ) d = d :=
    lcm_orderOf_eq_of_lcmUpto_dvd hlcm σ
  have hmd : m = d := hsuccess.symm.trans habsorb
  refine ⟨hmd, ?_⟩
  rw [hmd]
  exact ⟨hd, hlcm⟩

/-! ## Identifying the two residual probability models -/

/-- `NearDivisor` expresses the residual event via the complete-cycle-type
recurrence, while `PrimePowerAvoidance` expresses it as a cycle-index sum.
They are exactly the same probability. -/
theorem residualSuccessWeight_eq_residualOrderProbability
    (s d m : ℕ) :
    residualSuccessWeight s d m = residualOrderProbability s d m := by
  rw [residualOrderProbability_eq_completeCycleTypeMass,
    completeCycleTypeMass_eq_sum_cycleTypes]
  unfold residualSuccessWeight
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext mu
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hmu, hsuccess⟩
      refine ⟨hmu, ?_⟩
      rw [Multiset.lcm_cons, lcm_eq_nat_lcm,
        lcm_completeCycleType hmu, Nat.lcm_comm]
      exact hsuccess
    · rintro ⟨hmu, hsuccess⟩
      refine ⟨hmu, ?_⟩
      rw [Multiset.lcm_cons, lcm_eq_nat_lcm,
        lcm_completeCycleType hmu, Nat.lcm_comm] at hsuccess
      exact hsuccess
  · intro mu hmu
    rfl

theorem exists_residual_witness_of_probability_pos
    {s d m : ℕ} (h : 0 < residualOrderProbability s d m) :
    ∃ σ : Equiv.Perm (Fin s), Nat.lcm (orderOf σ) d = m := by
  have hcount : 0 < residualOrderCount s d m := by
    by_contra hnot
    have hz : residualOrderCount s d m = 0 := Nat.eq_zero_of_not_pos hnot
    simp [residualOrderProbability, hz] at h
  unfold residualOrderCount cycleTypeEventCount at hcount
  obtain ⟨σ, hσ⟩ := Finset.card_pos.mp hcount
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
  refine ⟨σ, ?_⟩
  rw [← Equiv.Perm.lcm_cycleType]
  exact hσ

/-! ## The arithmetic separation used by the first-cycle recursion -/

/-- Two distinct divisors of `m` which both lie in the last `s` integers
below `n` force a lower bound on `m`.  This is the division-free form of
`lcm(d₁,d₂) ≥ d₁d₂/s`. -/
theorem mul_le_mul_of_two_near_divisors {n s m d₁ d₂ : ℕ}
    (hm : 0 < m) (hd₁m : d₁ ∣ m) (hd₂m : d₂ ∣ m)
    (hd₁n : n - s < d₁) (_hd₂n : n - s < d₂)
    (hd₁d₂ : d₁ < d₂) (hd₂le : d₂ ≤ n) :
    d₁ * d₂ ≤ m * s := by
  have hgcd_dvd_diff : Nat.gcd d₁ d₂ ∣ d₂ - d₁ := by
    exact Nat.dvd_sub (Nat.gcd_dvd_right d₁ d₂)
      (Nat.gcd_dvd_left d₁ d₂)
  have hdiff_pos : 0 < d₂ - d₁ := Nat.sub_pos_of_lt hd₁d₂
  have hdiff_le_s : d₂ - d₁ ≤ s := by
    by_cases hsn : s ≤ n
    · omega
    · exact (Nat.sub_le d₂ d₁).trans (hd₂le.trans (by omega))
  have hgcd_le_s : Nat.gcd d₁ d₂ ≤ s :=
    (Nat.le_of_dvd hdiff_pos hgcd_dvd_diff).trans hdiff_le_s
  have hlcm_dvd : Nat.lcm d₁ d₂ ∣ m := Nat.lcm_dvd hd₁m hd₂m
  have hlcm_le : Nat.lcm d₁ d₂ ≤ m :=
    Nat.le_of_dvd hm hlcm_dvd
  calc
    d₁ * d₂ = Nat.lcm d₁ d₂ * Nat.gcd d₁ d₂ :=
      (Nat.lcm_mul_gcd d₁ d₂).symm
    _ ≤ m * s := Nat.mul_le_mul hlcm_le hgcd_le_s

/-- An immediately usable uniqueness criterion for near-`n` divisors. -/
theorem atMostOne_near_divisor
    {n s m : ℕ} (hm : 0 < m) (hsep : m * s < (n - s + 1) ^ 2) :
    Set.Subsingleton {d : ℕ | d ∣ m ∧ n - s < d ∧ d ≤ n} := by
  intro d₁ hd₁ d₂ hd₂
  by_contra hne
  have hlt : d₁ < d₂ ∨ d₂ < d₁ := Nat.lt_or_gt_of_ne hne
  rcases hlt with hlt | hlt
  · have hmul := mul_le_mul_of_two_near_divisors hm hd₁.1 hd₂.1
      hd₁.2.1 hd₂.2.1 hlt hd₂.2.2
    have hlower₁ : n - s + 1 ≤ d₁ := Nat.succ_le_iff.mpr hd₁.2.1
    have hlower₂ : n - s + 1 ≤ d₂ := Nat.succ_le_iff.mpr hd₂.2.1
    have hlower : (n - s + 1) ^ 2 ≤ d₁ * d₂ := by
      simpa [pow_two] using Nat.mul_le_mul hlower₁ hlower₂
    exact (Nat.lt_irrefl _) (hlower.trans_lt (hmul.trans_lt hsep))
  · have hmul := mul_le_mul_of_two_near_divisors hm hd₂.1 hd₁.1
      hd₂.2.1 hd₁.2.1 hlt hd₁.2.2
    have hlower₁ : n - s + 1 ≤ d₁ := Nat.succ_le_iff.mpr hd₁.2.1
    have hlower₂ : n - s + 1 ≤ d₂ := Nat.succ_le_iff.mpr hd₂.2.1
    have hlower : (n - s + 1) ^ 2 ≤ d₂ * d₁ := by
      simpa [pow_two] using Nat.mul_le_mul hlower₂ hlower₁
    exact (Nat.lt_irrefl _) (hlower.trans_lt (hmul.trans_lt hsep))

/-- The first-cycle sum is at most one unit of near-divisor mass plus its
divisor-function tail.  This is the quantitative upper bound behind
`max p_n(m) ~ 1/n`. -/
theorem orderRationalProbability_le_one_add_divisor_error
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hmCube : m ^ 3 ≤ n ^ 4) (hnLarge : 4096 < n) :
    (orderCount n m : ℚ) / (n.factorial : ℚ) ≤
      (1 / n : ℚ) *
        (1 + (divisorCount m : ℚ) ^ 2 / (n.sqrt : ℕ)) := by
  classical
  have hnearUnique : ∀ a ∈ nearDivisors n m,
      ∀ b ∈ nearDivisors n m, a = b := by
    intro a ha b hb
    apply nearDivisors_subsingleton_of_cube_le_fourth hm hmCube hnLarge
    · exact (mem_nearDivisors hm).mp ha
    · exact (mem_nearDivisors hm).mp hb
  have hnear :
      (∑ d ∈ nearDivisors n m,
        residualOrderProbability (n - d) d m) ≤ 1 := by
    by_cases hne : (nearDivisors n m).Nonempty
    · obtain ⟨d, hd⟩ := hne
      have heq : nearDivisors n m = {d} := by
        ext e
        simp only [Finset.mem_singleton]
        constructor
        · intro he
          exact hnearUnique e he d hd
        · rintro rfl
          exact hd
      rw [heq]
      simp only [Finset.sum_singleton]
      exact (residualOrderProbability_le_orderDvdProbability (n - d) d m).trans
        (orderDvdProbability_le_one (n - d) m)
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp
  have hfar :
      (∑ d ∈ farDivisors n m,
        residualOrderProbability (n - d) d m) ≤
          (divisorCount m : ℚ) ^ 2 / (n.sqrt : ℕ) := by
    apply sum_farDivisors_le_divisorCount_sq_div_sqrt hn hm
    intro d hd
    exact residualOrderProbability_le_divisorCount_div_of_mem_far hn hm hd
  rw [orderRationalProbability_recursion_filtered hn,
    ← sum_boundedDivisors_residualOrderProbability_eq hm]
  have hsplit := sum_farDivisors_add_sum_nearDivisors n m
    (fun d ↦ residualOrderProbability (n - d) d m)
  have hsum :
      (∑ d ∈ boundedDivisors n m,
        residualOrderProbability (n - d) d m) ≤
          1 + (divisorCount m : ℚ) ^ 2 / (n.sqrt : ℕ) := by
    rw [← hsplit]
    linarith
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

theorem orderProbability_le_one_add_divisor_error
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hmCube : m ^ 3 ≤ n ^ 4) (hnLarge : 4096 < n) :
    orderProbability n m ≤
      (1 / n : ℝ) *
        (1 + (divisorCount m : ℝ) ^ 2 / (n.sqrt : ℕ)) := by
  have hQ := orderRationalProbability_le_one_add_divisor_error
    hn hm hmCube hnLarge
  have hR :
      (((orderCount n m : ℚ) / (n.factorial : ℚ) : ℚ) : ℝ) ≤
        (((1 / n : ℚ) *
          (1 + (divisorCount m : ℚ) ^ 2 / (n.sqrt : ℕ)) : ℚ) : ℝ) :=
    Rat.cast_le.mpr hQ
  simpa [orderProbability] using hR

/-! ## The finite structural endgame -/

/-- Beker's structural conclusion after the large-order cutoff and the
uniform divisor estimates have been instantiated.  All analytic inputs are
integer inequalities; the remaining argument is the exact first-cycle
recurrence and the finite prime-power contradiction. -/
theorem threshold_structure_of_cube_le_fourth
    {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hmCube : m ^ 3 ≤ n ^ 4) (hnLarge : 4096 < n)
    (hthreshold :
      (1 / n : ℚ) ≤ (orderCount n m : ℚ) / (n.factorial : ℚ))
    (hhalf : 2 * divisorCount m ^ 2 < n.sqrt)
    (hfinite : (225 : ℕ).factorial * divisorCount m ^ 2 < n.sqrt)
    (hcube : 2 * divisorCount m ^ 3 < n.sqrt) :
    m ≤ n ∧ BekerCandidate n m := by
  let T := divisorCount m
  let delta : ℚ := (T : ℚ) ^ 2 / (n.sqrt : ℕ)
  have hsqrt : 0 < n.sqrt := Nat.sqrt_pos.2 hn
  have hdeltaHalf : delta < 1 / 2 := by
    dsimp [delta, T]
    exact natCast_div_lt_inv_of_mul_lt hsqrt (by norm_num) hhalf
  have hdeltaFinite : delta < 1 / ((225 : ℕ).factorial : ℚ) := by
    dsimp [delta, T]
    exact natCast_div_lt_inv_of_mul_lt hsqrt (by positivity) hfinite
  have hdeltaOne : delta < 1 := hdeltaHalf.trans (by norm_num)
  obtain ⟨d, hdNear, _, hsuccessLower⟩ :=
    exists_unique_nearDivisor_of_rational_order_threshold hn hm hmCube
      hnLarge hthreshold
      (fun d hd ↦ residualOrderProbability_le_divisorCount_div_of_mem_far
        hn hm hd)
      (by simpa [delta, T] using hdeltaOne)
  have hdData : d ∣ m ∧ n - n.sqrt < d ∧ d ≤ n :=
    (mem_nearDivisors hm).mp hdNear
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdData.1 hm
  let s := n - d
  have hsuccessLower' :
      1 - delta ≤ residualOrderProbability s d m := by
    simpa [s, delta, T] using hsuccessLower
  have hsuccessHalf :
      1 / 2 < residualOrderProbability s d m := by
    linarith
  have hsuccessPos : 0 < residualOrderProbability s d m :=
    (by norm_num : (0 : ℚ) < 1 / 2).trans hsuccessHalf
  obtain ⟨σ, hσ⟩ :=
    exists_residual_witness_of_probability_pos hsuccessPos
  have hlcm : Nat.lcmUpto s ∣ d := by
    by_cases hs0 : s = 0
    · rw [hs0, Nat.lcmUpto]
      simp
    · have hs : 0 < s := Nat.pos_of_ne_zero hs0
      have hresidualBound :
          residualOrderProbability s d m ≤ (T : ℚ) / s := by
        dsimp only [T]
        simpa only [divisorCount] using
          (residualOrderProbability_le_divisors_card_div
            (j := d) hs hm)
      have hsRatio : (s : ℚ) / 2 < T := by
        have hcomb : (1 / 2 : ℚ) < (T : ℚ) / s :=
          hsuccessHalf.trans_le hresidualBound
        rw [lt_div_iff₀ (by exact_mod_cast hs : (0 : ℚ) < s)] at hcomb
        linarith
      have hslt : s < 2 * T := by exact_mod_cast (by linarith : (s : ℚ) < 2 * T)
      have hsle : s ≤ 2 * T := hslt.le
      have hnatS : s * T ^ 2 < n.sqrt := by
        calc
          s * T ^ 2 ≤ (2 * T) * T ^ 2 := Nat.mul_le_mul_right _ hsle
          _ = 2 * T ^ 3 := by ring
          _ < n.sqrt := by simpa [T] using hcube
      have hsmallS : delta < 1 / (s : ℚ) := by
        dsimp [delta]
        rw [div_lt_div_iff₀
          (by exact_mod_cast hsqrt : (0 : ℚ) < n.sqrt)
          (by exact_mod_cast hs : (0 : ℚ) < s)]
        exact_mod_cast (by simpa [Nat.mul_comm] using hnatS)
      have hsmallConst : delta < 7 / 16 :=
        hdeltaFinite.trans (by norm_num)
      have hfailure : residualFailureWeight s d m ≤ delta := by
        have htotal := residualSuccessWeight_add_failureWeight s d m
        rw [residualSuccessWeight_eq_residualOrderProbability] at htotal
        linarith
      exact lcmUpto_dvd_of_residualFailureWeight_le hs hdpos.ne' delta
        hfailure hsmallS hsmallConst hdeltaFinite
  change Nat.lcmUpto (n - d) ∣ d at hlcm
  change Equiv.Perm (Fin (n - d)) at σ
  change Nat.lcm (orderOf σ) d = m at hσ
  have hresult := eq_and_bekerCandidate_of_residual_witness hdpos hlcm σ hσ
  refine ⟨?_, hresult.2⟩
  rw [hresult.1]
  exact hdData.2.2

/-- The eventual structural theorem, factored through the only global
analytic input: anticoncentration for orders satisfying `n⁴ ≤ m³`. -/
theorem eventually_orderProbability_ge_one_div_imp_bekerCandidate_of_large_order_cutoff
    (hlarge : ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      n ^ 4 ≤ m ^ 3 → orderProbability n m < (1 : ℝ) / n) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      (1 : ℝ) / n ≤ orderProbability n m →
        m ≤ n ∧ BekerCandidate n m := by
  filter_upwards [hlarge, eventually_gt_atTop 4096,
      eventually_const_mul_divisorCount_sq_lt_sqrt 2,
      eventually_const_mul_divisorCount_sq_lt_sqrt (225 : ℕ).factorial,
      eventually_const_mul_divisorCount_pow_lt_sqrt 2 3 (by norm_num)]
      with n hlargeN hnLarge hhalfN hfiniteN hcubeN
  intro m hthresholdReal
  have hn : 0 < n := by omega
  have hcount : (n - 1).factorial ≤ orderCount n m :=
    (one_div_le_orderProbability_iff hn).1 hthresholdReal
  have hcountPos : 0 < orderCount n m :=
    (Nat.factorial_pos (n - 1)).trans_le hcount
  have hm : 0 < m :=
    possibleOrder_pos (orderCount_pos_iff_mem_possibleOrders.mp hcountPos)
  have hmCube : m ^ 3 ≤ n ^ 4 := by
    by_contra hnot
    have hlargeOrder : n ^ 4 ≤ m ^ 3 := by omega
    exact (not_lt_of_ge hthresholdReal) (hlargeN m hlargeOrder)
  exact threshold_structure_of_cube_le_fourth hn hm hmCube hnLarge
    (one_div_le_orderRationalProbability_of_orderProbability hn hthresholdReal)
    (hhalfN m hm hmCube) (hfiniteN m hm hmCube) (hcubeN m hm hmCube)

theorem eventually_orderCount_ge_pred_factorial_imp_bekerCandidate_of_large_order_cutoff
    (hlarge : ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      n ^ 4 ≤ m ^ 3 → orderProbability n m < (1 : ℝ) / n) :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      (n - 1).factorial ≤ orderCount n m →
        m ≤ n ∧ BekerCandidate n m := by
  filter_upwards
    [eventually_orderProbability_ge_one_div_imp_bekerCandidate_of_large_order_cutoff
      hlarge, eventually_gt_atTop 0] with n hstructure hn
  intro m hm
  exact hstructure m ((one_div_le_orderProbability_iff hn).2 hm)

/-- The same inputs give the matching uniform upper bound for the largest
order fiber. -/
theorem eventually_maxOrderProbability_le_of_large_order_cutoff
    (hlarge : ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      n ^ 4 ≤ m ^ 3 → orderProbability n m < (1 : ℝ) / n) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n : ℕ in atTop,
      maxOrderProbability n ≤ (1 + ε) / n := by
  intro ε hε
  obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
  let C := k + 1
  filter_upwards [hlarge, eventually_gt_atTop 4096,
      eventually_const_mul_divisorCount_sq_lt_sqrt C]
      with n hlargeN hnLarge herrorN
  have hn : 0 < n := by omega
  obtain ⟨m, hmPossible, hmMax⟩ := exists_orderCount_eq_maxOrderCount n
  have hmode : IsMode n m := isMode_iff_orderCount_eq_maxOrderCount.2 hmMax
  have hm : 0 < m := possibleOrder_pos hmPossible
  have hthreshold : (1 : ℝ) / n ≤ orderProbability n m := by
    rw [← maxOrderProbability_eq_orderProbability_of_isMode hmode]
    exact one_div_le_maxOrderProbability hn
  have hmCube : m ^ 3 ≤ n ^ 4 := by
    by_contra hnot
    have hlargeOrder : n ^ 4 ≤ m ^ 3 := by omega
    exact (not_lt_of_ge hthreshold) (hlargeN m hlargeOrder)
  have hsqrt : 0 < n.sqrt := Nat.sqrt_pos.2 hn
  have hdeltaInv :
      (divisorCount m : ℝ) ^ 2 / (n.sqrt : ℕ) < 1 / (C : ℝ) := by
    rw [div_lt_div_iff₀
      (by exact_mod_cast hsqrt : (0 : ℝ) < n.sqrt)
      (by positivity : (0 : ℝ) < C)]
    exact_mod_cast (by simpa [Nat.mul_comm] using herrorN m hm hmCube)
  have hdeltaEps :
      (divisorCount m : ℝ) ^ 2 / (n.sqrt : ℕ) < ε := by
    exact hdeltaInv.trans (by simpa [C] using hk)
  rw [maxOrderProbability_eq_orderProbability_of_isMode hmode]
  calc
    orderProbability n m ≤
        (1 / n : ℝ) *
          (1 + (divisorCount m : ℝ) ^ 2 / (n.sqrt : ℕ)) :=
      orderProbability_le_one_add_divisor_error hn hm hmCube hnLarge
    _ ≤ (1 / n : ℝ) * (1 + ε) := by
      gcongr
    _ = (1 + ε) / n := by ring

theorem maxOrderProbability_isEquivalent_one_div_of_large_order_cutoff
    (hlarge : ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      n ^ 4 ≤ m ^ 3 → orderProbability n m < (1 : ℝ) / n) :
    (fun n : ℕ ↦ maxOrderProbability n) ~[atTop]
      (fun n : ℕ ↦ (1 : ℝ) / n) :=
  maxOrderProbability_isEquivalent_of_eventually_upper
    (eventually_maxOrderProbability_le_of_large_order_cutoff hlarge)

theorem maxOrderCount_isEquivalent_pred_factorial_of_large_order_cutoff
    (hlarge : ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      n ^ 4 ≤ m ^ 3 → orderProbability n m < (1 : ℝ) / n) :
    (fun n : ℕ ↦ (maxOrderCount n : ℝ)) ~[atTop]
      (fun n : ℕ ↦ ((n - 1).factorial : ℝ)) :=
  maxOrderCount_isEquivalent_pred_factorial_of_probability
    (maxOrderProbability_isEquivalent_one_div_of_large_order_cutoff hlarge)

/-! ## Beker's unconditional structural and asymptotic theorems -/

theorem eventually_orderProbability_ge_one_div_imp_bekerCandidate :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      (1 : ℝ) / n ≤ orderProbability n m →
        m ≤ n ∧ BekerCandidate n m :=
  eventually_orderProbability_ge_one_div_imp_bekerCandidate_of_large_order_cutoff
    eventually_orderProbability_lt_inv_of_fourth_le_cube

theorem eventually_orderCount_ge_pred_factorial_imp_bekerCandidate :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ,
      (n - 1).factorial ≤ orderCount n m →
        m ≤ n ∧ BekerCandidate n m :=
  eventually_orderCount_ge_pred_factorial_imp_bekerCandidate_of_large_order_cutoff
    eventually_orderProbability_lt_inv_of_fourth_le_cube

theorem eventually_maxOrderProbability_le (ε : ℝ) (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      maxOrderProbability n ≤ (1 + ε) / n :=
  eventually_maxOrderProbability_le_of_large_order_cutoff
    eventually_orderProbability_lt_inv_of_fourth_le_cube ε hε

theorem maxOrderProbability_isEquivalent_one_div :
    (fun n : ℕ ↦ maxOrderProbability n) ~[atTop]
      (fun n : ℕ ↦ (1 : ℝ) / n) :=
  maxOrderProbability_isEquivalent_one_div_of_large_order_cutoff
    eventually_orderProbability_lt_inv_of_fourth_le_cube

/-- Beker's Theorem 1.1 in its original counting normalization:
`max_m f_m(n) ~ (n-1)!`. -/
theorem maxOrderCount_isEquivalent_pred_factorial :
    (fun n : ℕ ↦ (maxOrderCount n : ℝ)) ~[atTop]
      (fun n : ℕ ↦ ((n - 1).factorial : ℝ)) :=
  maxOrderCount_isEquivalent_pred_factorial_of_large_order_cutoff
    eventually_orderProbability_lt_inv_of_fourth_le_cube

end Erdos1161
