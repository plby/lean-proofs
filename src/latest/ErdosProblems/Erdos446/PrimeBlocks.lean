/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.LowerReduction
import ErdosProblems.Erdos697.Erdos697PrimeHarmonic
import UnitFractions.ForMathlib.BasicEstimates

/-!
# Erdős Problem 446: reciprocal-prime blocks

We use the exact doubly exponential endpoints `2^(2^j)`.  Mertens' theorem
with its formal `O(1 / log x)` error then says that each sufficiently late
block has reciprocal mass arbitrarily close to `log 2`.
-/

namespace Erdos446

open Filter Finset Real Asymptotics
open scoped BigOperators Topology

/-- Doubly exponential natural endpoints for Ford's prime blocks. -/
def blockEndpoint (j : ℕ) : ℕ := 2 ^ (2 ^ j)

/-- Primes in `(2^(2^j), 2^(2^(j+1))]`. -/
def primeBlock (j : ℕ) : Finset ℕ :=
  Nat.primesLE (blockEndpoint (j + 1)) \ Nat.primesLE (blockEndpoint j)

/-- Reciprocal mass of the `j`th prime block. -/
noncomputable def primeBlockMass (j : ℕ) : ℝ :=
  ∑ p ∈ primeBlock j, 1 / (p : ℝ)

theorem blockEndpoint_pos (j : ℕ) : 0 < blockEndpoint j := by
  simp [blockEndpoint]

theorem blockEndpoint_mono : Monotone blockEndpoint := by
  intro i j hij
  exact Nat.pow_le_pow_right (by omega)
    (Nat.pow_le_pow_right (by omega) hij)

theorem blockEndpoint_strictMono : StrictMono blockEndpoint := by
  intro i j hij
  unfold blockEndpoint
  exact Nat.pow_lt_pow_right (by omega)
    (Nat.pow_lt_pow_right (by omega) hij)

theorem mem_primeBlock {j p : ℕ} :
    p ∈ primeBlock j ↔
      p.Prime ∧ blockEndpoint j < p ∧ p ≤ blockEndpoint (j + 1) := by
  simp only [primeBlock, Finset.mem_sdiff, Nat.mem_primesLE, not_and_or,
    not_le]
  aesop

theorem primeBlock_pairwise_disjoint {i j : ℕ} (hij : i ≠ j) :
    Disjoint (primeBlock i) (primeBlock j) := by
  rw [Finset.disjoint_left]
  intro p hpi hpj
  rw [mem_primeBlock] at hpi hpj
  rcases lt_or_gt_of_ne hij with hij' | hji'
  · have hi1j : i + 1 ≤ j := by omega
    have : blockEndpoint (i + 1) < p :=
      lt_of_le_of_lt (blockEndpoint_mono hi1j) hpj.2.1
    omega
  · have hj1i : j + 1 ≤ i := by omega
    have : blockEndpoint (j + 1) < p :=
      lt_of_le_of_lt (blockEndpoint_mono hj1i) hpi.2.1
    omega

theorem primeBlockMass_eq_sub (j : ℕ) :
    primeBlockMass j =
      Erdos697.PrimeHarmonic.sum (blockEndpoint (j + 1)) -
        Erdos697.PrimeHarmonic.sum (blockEndpoint j) := by
  rw [primeBlockMass, primeBlock, Erdos697.PrimeHarmonic.sum]
  exact Finset.sum_sdiff_eq_sub
    (Nat.primesLE_mono (blockEndpoint_mono (Nat.le_succ j)))

theorem log_blockEndpoint (j : ℕ) :
    Real.log (blockEndpoint j : ℝ) = (2 : ℝ) ^ j * Real.log 2 := by
  rw [blockEndpoint, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  norm_num

theorem log_log_blockEndpoint (j : ℕ) :
    Real.log (Real.log (blockEndpoint j : ℝ)) =
      (j : ℝ) * Real.log 2 + Real.log (Real.log 2) := by
  rw [log_blockEndpoint, Real.log_mul (by positivity)
    (ne_of_gt (Real.log_pos (by norm_num)))]
  rw [Real.log_pow]

theorem log_log_blockEndpoint_succ_sub (j : ℕ) :
    Real.log (Real.log (blockEndpoint (j + 1) : ℝ)) -
      Real.log (Real.log (blockEndpoint j : ℝ)) = Real.log 2 := by
  rw [log_log_blockEndpoint, log_log_blockEndpoint]
  push_cast
  ring

/-- Natural-endpoint reciprocal-prime Mertens estimate with a vanishing
`1 / log N` error. -/
theorem exists_primeHarmonic_sharp_error :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop,
      |Erdos697.PrimeHarmonic.sum N -
          (Real.log (Real.log (N : ℝ)) + meissel_mertens)| ≤
        C / Real.log (N : ℝ) := by
  obtain ⟨c, hc⟩ := prime_reciprocal.bound
  let C : ℝ := |c| + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  have hnat := tendsto_natCast_atTop_atTop.eventually hc
  filter_upwards [hnat, eventually_ge_atTop 3] with N hN hN3
  have hlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hrewrite :
      prime_summatory (fun p ↦ (p : ℝ)⁻¹) 1 (N : ℝ) =
        Erdos697.PrimeHarmonic.sum N := by
    rw [prime_summatory, Nat.floor_natCast,
      Erdos697.PrimeHarmonic.sum]
    apply Finset.sum_congr
    · ext p
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesLE]
      constructor
      · rintro ⟨⟨hp1, hpN⟩, hp⟩
        exact ⟨hpN, hp⟩
      · rintro ⟨hpN, hp⟩
        exact ⟨⟨hp.one_le, hpN⟩, hp⟩
    · intro p hp
      rw [one_div]
  simp only [Real.norm_eq_abs, norm_inv, abs_of_pos hlog] at hN
  rw [hrewrite] at hN
  calc
    |Erdos697.PrimeHarmonic.sum N -
        (Real.log (Real.log (N : ℝ)) + meissel_mertens)| ≤
        c * (Real.log (N : ℝ))⁻¹ := hN
    _ ≤ C * (Real.log (N : ℝ))⁻¹ := by
      apply mul_le_mul_of_nonneg_right
      · dsimp [C]
        linarith [le_abs_self c]
      · positivity
    _ = C / Real.log (N : ℝ) := by rw [div_eq_mul_inv]

/-- Sufficiently late doubly exponential prime blocks have reciprocal mass
within ten percent of `log 2`. -/
theorem eventually_primeBlockMass_bounds :
    ∀ᶠ j : ℕ in atTop,
      (9 / 10 : ℝ) * Real.log 2 ≤ primeBlockMass j ∧
      primeBlockMass j ≤ (11 / 10 : ℝ) * Real.log 2 := by
  obtain ⟨C, hC, herror⟩ := exists_primeHarmonic_sharp_error
  have hendpointTop : Tendsto blockEndpoint atTop atTop := by
    refine Filter.tendsto_atTop_mono' atTop
      (f₁ := fun j : ℕ ↦ 2 ^ j) ?_ ?_
    · filter_upwards with j
      exact Nat.pow_le_pow_right (by omega)
        (Nat.le_of_lt j.lt_two_pow_self)
    · exact tendsto_pow_atTop_atTop_of_one_lt (by omega : (1 : ℕ) < 2)
  have herrorJ := hendpointTop.eventually herror
  have herrorSucc := (Filter.tendsto_add_atTop_nat 1).eventually herrorJ
  have hsmall : ∀ᶠ j : ℕ in atTop,
      C / Real.log (blockEndpoint j : ℝ) ≤ Real.log 2 / 20 := by
    have hpowTop : Tendsto (fun j : ℕ ↦ (2 : ℝ) ^ j) atTop atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
    have hdenTop : Tendsto
        (fun j : ℕ ↦ (2 : ℝ) ^ j * Real.log 2) atTop atTop :=
      Filter.Tendsto.atTop_mul_const (Real.log_pos (by norm_num)) hpowTop
    have hinvZero : Tendsto
        (fun j : ℕ ↦ C / ((2 : ℝ) ^ j * Real.log 2)) atTop (nhds 0) := by
      simpa only [Pi.inv_apply, div_eq_mul_inv, mul_zero] using
        tendsto_const_nhds.mul hdenTop.inv_tendsto_atTop
    have hevent := (tendsto_order.1 hinvZero).2
      (Real.log 2 / 20) (by positivity)
    filter_upwards [hevent] with j hj
    simpa only [log_blockEndpoint] using hj.le
  have hsmallSucc := (Filter.tendsto_add_atTop_nat 1).eventually hsmall
  filter_upwards [herrorJ, herrorSucc, hsmall, hsmallSucc]
      with j hj hjs hjsmall hjssmall
  rw [primeBlockMass_eq_sub]
  have hmain := log_log_blockEndpoint_succ_sub j
  constructor
  · have hlowJ := neg_le_of_abs_le hj
    have huppJ := le_of_abs_le hj
    have hlowS := neg_le_of_abs_le hjs
    have huppS := le_of_abs_le hjs
    nlinarith
  · have hlowJ := neg_le_of_abs_le hj
    have huppJ := le_of_abs_le hj
    have hlowS := neg_le_of_abs_le hjs
    have huppS := le_of_abs_le hjs
    nlinarith

theorem exists_primeBlock_threshold :
    ∃ J₀ : ℕ, ∀ j : ℕ, J₀ ≤ j →
      (9 / 10 : ℝ) * Real.log 2 ≤ primeBlockMass j ∧
      primeBlockMass j ≤ (11 / 10 : ℝ) * Real.log 2 :=
  Filter.eventually_atTop.1 eventually_primeBlockMass_bounds

/-- The reciprocal mass of the `j`th doubly exponential block differs from
`log 2` by `O(2⁻ʲ)`.  This quantitative form, rather than a fixed ten-percent
window, is what prevents a spurious exponential loss in products over many
slots. -/
theorem exists_primeBlockMass_geometric_error :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ j : ℕ in atTop,
      |primeBlockMass j - Real.log 2| ≤ C / (2 : ℝ) ^ j := by
  obtain ⟨C₀, hC₀, herror⟩ := exists_primeHarmonic_sharp_error
  let E : ℕ → ℝ := fun N ↦
    Erdos697.PrimeHarmonic.sum N -
      (Real.log (Real.log (N : ℝ)) + meissel_mertens)
  let C : ℝ := 2 * C₀ / Real.log 2
  have hC : 0 < C := by
    dsimp [C]
    positivity
  have hendpointTop : Tendsto blockEndpoint atTop atTop := by
    refine Filter.tendsto_atTop_mono' atTop
      (f₁ := fun j : ℕ ↦ 2 ^ j) ?_ ?_
    · filter_upwards with j
      exact Nat.pow_le_pow_right (by omega)
        (Nat.le_of_lt j.lt_two_pow_self)
    · exact tendsto_pow_atTop_atTop_of_one_lt (by omega : (1 : ℕ) < 2)
  have herrorJ := hendpointTop.eventually herror
  have herrorSucc := (Filter.tendsto_add_atTop_nat 1).eventually herrorJ
  refine ⟨C, hC, ?_⟩
  filter_upwards [herrorJ, herrorSucc] with j hj hjs
  have hjLog : 0 < Real.log (blockEndpoint j : ℝ) :=
    Real.log_pos (by
      exact_mod_cast (show 1 < blockEndpoint j by
        unfold blockEndpoint
        exact one_lt_pow₀ (by omega) (by positivity)))
  have hjsLog : 0 < Real.log (blockEndpoint (j + 1) : ℝ) :=
    Real.log_pos (by
      exact_mod_cast (show 1 < blockEndpoint (j + 1) by
        unfold blockEndpoint
        exact one_lt_pow₀ (by omega) (by positivity)))
  have hlogMono :
      Real.log (blockEndpoint j : ℝ) ≤
        Real.log (blockEndpoint (j + 1) : ℝ) := by
    exact Real.log_le_log (by exact_mod_cast blockEndpoint_pos j)
      (by exact_mod_cast blockEndpoint_mono (Nat.le_succ j))
  have hCdiv :
      C₀ / Real.log (blockEndpoint (j + 1) : ℝ) ≤
        C₀ / Real.log (blockEndpoint j : ℝ) := by
    exact div_le_div_of_nonneg_left hC₀.le hjLog hlogMono
  have hmassError :
      primeBlockMass j - Real.log 2 =
        E (blockEndpoint (j + 1)) - E (blockEndpoint j) := by
    dsimp [E]
    rw [primeBlockMass_eq_sub]
    linarith [log_log_blockEndpoint_succ_sub j]
  rw [hmassError]
  calc
    |E (blockEndpoint (j + 1)) - E (blockEndpoint j)| ≤
        |E (blockEndpoint (j + 1))| + |E (blockEndpoint j)| :=
      abs_sub _ _
    _ ≤ C₀ / Real.log (blockEndpoint (j + 1) : ℝ) +
        C₀ / Real.log (blockEndpoint j : ℝ) := add_le_add hjs hj
    _ ≤ C₀ / Real.log (blockEndpoint j : ℝ) +
        C₀ / Real.log (blockEndpoint j : ℝ) := add_le_add hCdiv le_rfl
    _ = C / (2 : ℝ) ^ j := by
      rw [log_blockEndpoint]
      dsimp [C]
      field_simp
      ring

end Erdos446
