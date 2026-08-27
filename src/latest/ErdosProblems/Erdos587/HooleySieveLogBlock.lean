import ErdosProblems.Erdos587.HooleySieveTailRange
import ErdosProblems.Erdos587.HooleyLogBlocks

/-!
# Geometric decay of the nonterminal prime blocks

Choosing the fixed Rankin parameter `2k + 2` overcomes the rough divisor
cost when the affine values have size at most `(R + 1)^k`. All dependence
on the block index is the summable factor `exp (-j)`.
-/

open scoped BigOperators

namespace Erdos587

theorem exists_delta_sieve_log_block_bound (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℤ), B ≠ 0 → IsCoprime A B →
      ∀ R N Y j : ℕ, 2 ≤ R → 2 ≤ N → R ^ 4 ≤ Y → N ≤ (R + 1) ^ k → 1 ≤ j →
      2 * (2 * (k : ℝ) + 2) ≤ Real.log (deltaLogCutoff R j : ℝ) →
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 Y →
      (∀ n ∈ S, (A + B * n).natAbs ≤ N) →
      (∀ n ∈ S, ∃ a b : ℕ, (A + B * n).natAbs = a * b ∧
        0 < a ∧ 0 < b ∧ a ≤ R ^ 2 ∧ R ≤ a ∧
        a.primeFactors ⊆ Nat.primesLE (deltaLogCutoff R j) ∧
        ∀ p ∈ b.primeFactors, deltaLogCutoff R (j + 1) < p) →
      (∑ n ∈ S, (hooleyDelta (A + B * n).natAbs : ℝ)) ≤
        C * ((B.natAbs : ℝ) / B.natAbs.totient) * Y *
          (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5 * Real.exp (-(j : ℝ)) := by
  obtain ⟨C₀, hC₀, hmean⟩ := exists_hooleyDelta_harmonic_loglog_bound
  let M : ℝ := 2 * (k : ℝ) + 2
  let E : ℝ := 20 * deltaRankinMertensConstant * M * Real.exp M
  refine ⟨3 * C₀ * (2 * k) * Real.exp (E + 2 * k), by positivity, ?_⟩
  intro A B hB hAB R N Y j hR hN hRY hRN hj hlarge S hS hvalues hcover
  let z := deltaLogCutoff R j
  let Q := deltaLogCutoff R (j + 1)
  have hR1 : 1 ≤ R := by omega
  have hQ : 0 < Q := deltaLogCutoff_pos hR1 (j + 1)
  have hlogz : 0 < Real.log (z : ℝ) := by
    change 2 * M ≤ Real.log (z : ℝ) at hlarge
    dsimp only [M] at hlarge
    have hk0 := Nat.cast_nonneg (α := ℝ) k
    linarith
  have hz : 2 ≤ z := by
    by_contra hz
    have hz1 : z = 1 := by have := deltaLogCutoff_pos hR1 j; change 0 < z at this; omega
    rw [hz1, Nat.cast_one, Real.log_one] at hlogz
    exact (lt_irrefl 0) hlogz
  have hlogQ : 0 < Real.log (Q + 1 : ℕ) :=
    Real.log_pos (by exact_mod_cast (show 1 < Q + 1 by omega))
  have hRpos : (0 : ℝ) < R := by exact_mod_cast (show 0 < R by omega)
  have hβ0 : 0 ≤ M / Real.log (z : ℝ) := by dsimp only [M]; positivity
  have hβ : M / Real.log (z : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hlogz).mpr
    change 2 * M ≤ Real.log (z : ℝ) at hlarge
    linarith
  have hβM : M / Real.log (z : ℝ) * Real.log (z : ℝ) ≤ M := by
    rw [div_mul_cancel₀ _ hlogz.ne']
  have htail := delta_sieve_tail_range_le hB hAB hQ hz (deltaLogCutoff_sieve_size hR1 hj hRY)
    hRpos hβ0 hβ hβM S hS hvalues
  have hcover' : ∀ n ∈ S, ∃ a b : ℕ, (A + B * n).natAbs = a * b ∧
      0 < a ∧ 0 < b ∧ a ≤ R ^ 2 ∧ (R : ℝ) ≤ a ∧
      a.primeFactors ⊆ Nat.primesLE z ∧ ∀ p ∈ b.primeFactors, Q < p := by
    intro n hn
    obtain ⟨a, b, hf, ha, hb, haR, hRa, hsm, hr⟩ := hcover n hn
    exact ⟨a, b, hf, ha, hb, haR, by exact_mod_cast hRa, hsm, hr⟩
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hlogN : Real.log (N : ℝ) ≤ 2 * (k : ℝ) * Real.log (R : ℝ) := by
    have h := Real.log_le_log (by exact_mod_cast (show 0 < N by omega))
      (show (N : ℝ) ≤ ((R + 1 : ℕ) : ℝ) ^ k by exact_mod_cast hRN)
    rw [Real.log_pow] at h
    nlinarith [mul_le_mul_of_nonneg_left (delta_log_succ_le hR) (Nat.cast_nonneg k)]
  have hcutq : Real.log (R : ℝ) ≤ ((j : ℝ) + 1) * Real.log (Q + 1 : ℕ) := by
    have h := (div_le_iff₀ (by positivity : (0 : ℝ) < ((j + 1 : ℕ) : ℝ))).mp
      (deltaLogCutoff_succ_log_gt R (j + 1)).le
    simpa only [Nat.cast_add, Nat.cast_one, mul_comm] using h
  have hcutz : (j : ℝ) * Real.log (z : ℝ) ≤ Real.log (R : ℝ) := by
    have h := (le_div_iff₀ (by exact_mod_cast hj : (0 : ℝ) < j)).mp
      (deltaLogCutoff_log_le hR1 j)
    simpa only [mul_comm] using h
  have hdecay := delta_log_block_decay (E := E) hlogz hlogQ hlogN0
    (Nat.cast_nonneg k) (Nat.cast_nonneg j) hlogN hcutq hcutz
  calc
    _ ≤ 3 * ((B.natAbs : ℝ) / B.natAbs.totient) * Y / Real.log (Q + 1 : ℕ) *
        Real.exp (Real.log 2 * Real.log (N : ℝ) / Real.log (Q + 1 : ℕ) + E -
          M / Real.log (z : ℝ) * Real.log (R : ℝ)) *
            ∑ d ∈ Finset.Icc 1 N, (hooleyDelta d : ℝ) / d := htail hcover'
    _ ≤ 3 * ((B.natAbs : ℝ) / B.natAbs.totient) * Y / Real.log (Q + 1 : ℕ) *
        Real.exp (Real.log 2 * Real.log (N : ℝ) / Real.log (Q + 1 : ℕ) + E -
          M / Real.log (z : ℝ) * Real.log (R : ℝ)) *
            (C₀ * Real.log (N : ℝ) * (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5) :=
      mul_le_mul_of_nonneg_left (hmean N hN) (by positivity)
    _ = (3 * C₀ * ((B.natAbs : ℝ) / B.natAbs.totient) * Y *
        (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5) *
          ((Real.log (N : ℝ) / Real.log (Q + 1 : ℕ)) *
            Real.exp (Real.log 2 * Real.log (N : ℝ) / Real.log (Q + 1 : ℕ) + E -
              (2 * (k : ℝ) + 2) * Real.log (R : ℝ) / Real.log (z : ℝ))) := by
      have heq : M / Real.log (z : ℝ) * Real.log (R : ℝ) =
          (2 * (k : ℝ) + 2) * Real.log (R : ℝ) / Real.log (z : ℝ) := by dsimp only [M]; ring
      rw [heq]
      ring
    _ ≤ (3 * C₀ * ((B.natAbs : ℝ) / B.natAbs.totient) * Y *
        (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5) *
          (2 * k * Real.exp (E + 2 * k) * Real.exp (-(j : ℝ))) :=
      mul_le_mul_of_nonneg_left hdecay (by positivity)
    _ = _ := by ring

end Erdos587
