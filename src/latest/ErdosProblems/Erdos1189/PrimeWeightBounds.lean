/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Quantitative estimates for the sum of prime weights p-1.
Informal source: the prime-number-theorem estimates used in Sections 6 and 7
of Pickhardt and Omniscience Research Agent.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.PrimeEstimates

namespace Erdos1189

open Finset Filter

lemma primeWeightSum_tail_bound (M N : ℕ) :
    M * ((Nat.primesLE N \ Nat.primesLE M).card) ≤ primeWeightSum N := by
  have hsub : Nat.primesLE N \ Nat.primesLE M ⊆ Nat.primesLE N := sdiff_subset
  calc
    M * ((Nat.primesLE N \ Nat.primesLE M).card) =
        ∑ p ∈ Nat.primesLE N \ Nat.primesLE M, M := by simp [Nat.mul_comm]
    _ ≤ ∑ p ∈ Nat.primesLE N \ Nat.primesLE M, (p - 1) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hpN, hpM⟩ := mem_sdiff.mp hp
      have hpP := Nat.prime_of_mem_primesLE hpN
      have hpgt : M < p := by
        by_contra hh
        exact hpM (Nat.mem_primesLE.mpr ⟨by omega, hpP⟩)
      omega
    _ ≤ primeWeightSum N := sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

lemma tendsto_nat_div_sixteen : Tendsto (fun n : ℕ => n / 16) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [eventually_ge_atTop (b * 16)] with n hn
  exact (Nat.le_div_iff_mul_le (by decide)).mpr hn

/-- A lower bound of the required order; no partial-summation theorem is assumed. -/
theorem eventually_primeWeightSum_lower :
    ∀ᶠ N : ℕ in atTop, (N : ℝ) ^ 2 ≤ 128 * primeWeightSum N * Real.log N := by
  filter_upwards [eventually_primeCounting_log_bounds,
    tendsto_nat_div_sixteen.eventually eventually_primeCounting_log_bounds,
    eventually_ge_atTop 1024] with N hN hM hlarge
  let M := N / 16
  have hMdef : N < 16 * (M + 1) := by
    have hmod := Nat.mod_lt N (by decide : 0 < 16)
    have hid := Nat.mod_add_div N 16
    dsimp [M]
    omega
  have hMN : M ≤ N := Nat.div_le_self _ _
  have hMpos : 0 < M := by dsimp [M]; omega
  have hMlower : N ≤ 32 * M := by omega
  have hMupper : 16 * M ≤ N := by
    have := Nat.div_mul_le_self N 16
    simpa only [M, Nat.mul_comm] using this
  have hMr : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hMlower' : (N : ℝ) ≤ 32 * M := by exact_mod_cast hMlower
  have hMupper' : 16 * (M : ℝ) ≤ N := by exact_mod_cast hMupper
  have hsquare : (N : ℝ) ≤ (M : ℝ) ^ 2 := by
    have hNlarge : (1024 : ℝ) ≤ N := by exact_mod_cast hlarge
    nlinarith
  have hlog : Real.log N ≤ 2 * Real.log M := by
    have hh := Real.log_le_log hNr hsquare
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hlogpos : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hsub : Nat.primesLE M ⊆ Nat.primesLE N := by
    intro p hp
    exact Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans hMN,
      Nat.prime_of_mem_primesLE hp⟩
  let K := (Nat.primesLE N \ Nat.primesLE M).card
  have hK : (K : ℝ) + Nat.primeCounting M = Nat.primeCounting N := by
    have hh := card_sdiff_add_card_eq_card hsub
    rw [Nat.primesLE_card_eq_primeCounting, Nat.primesLE_card_eq_primeCounting] at hh
    exact_mod_cast hh
  have hpiM : (Nat.primeCounting M : ℝ) * Real.log N ≤ 4 * M := by
    calc
      _ ≤ (Nat.primeCounting M : ℝ) * (2 * Real.log M) :=
        mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ 4 * M := by nlinarith [hM.2]
  have hKlower : (N : ℝ) ≤ 4 * K * Real.log N := by
    have hmain := hN.1
    rw [← hK] at hmain
    nlinarith
  have hweight : (M : ℝ) * K ≤ primeWeightSum N := by
    exact_mod_cast primeWeightSum_tail_bound M N
  have hprod := mul_le_mul hMlower' hKlower (by positivity : (0 : ℝ) ≤ N)
    (by positivity : (0 : ℝ) ≤ 32 * M)
  have hwlog := mul_le_mul_of_nonneg_right hweight hlogpos
  nlinarith

end Erdos1189
