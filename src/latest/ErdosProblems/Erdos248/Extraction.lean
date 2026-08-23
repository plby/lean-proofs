import ErdosProblems.Erdos248.PrimeRanges

/-!
# Erdős Problem 248: extraction from finite weighted bad-event bounds

This file uses no probability-measure API.  A direct double-sum argument
shows that if the total sieve mass of the finitely many relevant bad shifts
is smaller than the normalizing mass, then some positive-weight point avoids
every one of them.  Shifts beyond the binary logarithm of the interval are
handled by the elementary size estimate from `Arithmetic.lean`.
-/

noncomputable section

open scoped ArithmeticFunction.omega BigOperators

namespace Erdos248

local instance extractionDecidable (p : Prop) : Decidable p :=
  Classical.propDecidable p

def natBadAt (C k n : ℕ) : Prop :=
  C * k < ω (n + k)

def weightedBadMass (K C k : ℕ) : ℝ :=
  ∑ n ∈ Finset.Ico (intervalStart K) (2 * intervalStart K),
    if natBadAt C k n then sieveWeight K n else 0

theorem weightedBadMass_nonneg (K C k : ℕ) :
    0 ≤ weightedBadMass K C k := by
  unfold weightedBadMass
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact sieveWeight_nonneg K n
  · exact le_rfl

theorem exists_avoids_relevant_bad_shifts {K C : ℕ}
    (hbad :
      (∑ k ∈ Finset.Icc 1 (intervalExponent K), weightedBadMass K C k) <
        sieveMass K) :
    ∃ n ∈ Finset.Ico (intervalStart K) (2 * intervalStart K),
      sieveWeight K n ≠ 0 ∧
        ∀ k ∈ Finset.Icc 1 (intervalExponent K), ω (n + k) ≤ C * k := by
  classical
  by_contra hnot
  push Not at hnot
  have hpoint : ∀ n ∈ Finset.Ico (intervalStart K) (2 * intervalStart K),
      sieveWeight K n ≤
        ∑ k ∈ Finset.Icc 1 (intervalExponent K),
          if natBadAt C k n then sieveWeight K n else 0 := by
    intro n hn
    by_cases hw : sieveWeight K n = 0
    · simp [hw]
    · obtain ⟨k, hk, hkbad⟩ := hnot n hn hw
      have hterm :
          sieveWeight K n =
            (if natBadAt C k n then sieveWeight K n else 0) := by
        rw [if_pos]
        exact hkbad
      calc
        sieveWeight K n =
            (if natBadAt C k n then sieveWeight K n else 0) := hterm
        _ ≤ ∑ j ∈ Finset.Icc 1 (intervalExponent K),
            if natBadAt C j n then sieveWeight K n else 0 := by
          exact Finset.single_le_sum
            (s := Finset.Icc 1 (intervalExponent K))
            (f := fun j => if natBadAt C j n then sieveWeight K n else 0)
            (fun j hj => by
              split_ifs
              · exact sieveWeight_nonneg K n
              · exact le_rfl) hk
  have hsum : sieveMass K ≤
      ∑ n ∈ Finset.Ico (intervalStart K) (2 * intervalStart K),
        ∑ k ∈ Finset.Icc 1 (intervalExponent K),
          if natBadAt C k n then sieveWeight K n else 0 := by
    unfold sieveMass BoundedGaps.Maynard.sieveWeightSum
    exact Finset.sum_le_sum fun n hn => hpoint n hn
  have hswap :
      (∑ n ∈ Finset.Ico (intervalStart K) (2 * intervalStart K),
        ∑ k ∈ Finset.Icc 1 (intervalExponent K),
          if natBadAt C k n then sieveWeight K n else 0) =
      ∑ k ∈ Finset.Icc 1 (intervalExponent K), weightedBadMass K C k := by
    unfold weightedBadMass
    rw [Finset.sum_comm]
  rw [hswap] at hsum
  exact (not_lt_of_ge hsum) hbad

theorem exists_isGood_of_weightedBadMass {K C : ℕ} (hC : 2 ≤ C)
    (hbad :
      (∑ k ∈ Finset.Icc 1 (intervalExponent K), weightedBadMass K C k) <
        sieveMass K) :
    ∃ n : ℕ, intervalStart K ≤ n ∧ n < 2 * intervalStart K ∧
      IsGood (C : ℝ) n := by
  obtain ⟨n, hnrange, hnweight, hgood⟩ :=
    exists_avoids_relevant_bad_shifts hbad
  have hn := Finset.mem_Ico.mp hnrange
  refine ⟨n, hn.1, hn.2, ?_⟩
  intro k hk1
  by_cases hkM : k ≤ intervalExponent K
  · have hknat := hgood k (Finset.mem_Icc.mpr ⟨hk1, hkM⟩)
    exact_mod_cast hknat
  · have hLk : intervalExponent K + 1 ≤ k := by omega
    have hnPow : n ≤ 2 ^ (intervalExponent K + 1) := by
      have : 2 * intervalStart K = 2 ^ (intervalExponent K + 1) := by
        rw [intervalStart, pow_succ]
        ring
      omega
    have hfar := omega_add_le_two_mul_of_le_pow hnPow hLk hk1
    have hCle : 2 * k ≤ C * k := Nat.mul_le_mul_right k hC
    exact_mod_cast hfar.trans hCle

end Erdos248
