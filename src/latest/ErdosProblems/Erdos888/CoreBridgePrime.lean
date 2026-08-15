import ErdosProblems.Erdos888.BlockEncoding
import ErdosProblems.Erdos888.PrimeEstimates

open Filter Finset Real Set MeasureTheory Asymptotics
open scoped BigOperators Topology

namespace Erdos888
namespace CoreBridgePrime

noncomputable section

/-- The exponent-indexed block from `BlockEncoding` is exactly the
scale-indexed block from `PrimeEstimates` at scale `2^i`. -/
theorem dyadicPrimeBlock_eq_dyadicPrimes (i : ℕ) :
    dyadicPrimeBlock i = dyadicPrimes (2 ^ i) := by
  ext p
  simp only [mem_dyadicPrimeBlock, mem_dyadicPrimes]
  rw [pow_succ]
  simp only [Nat.mul_comm]

/-- Distinct exponent-indexed dyadic prime blocks are pairwise disjoint. -/
theorem pairwiseDisjoint_dyadicPrimeBlock (S : Finset ℕ) :
    (↑S : Set ℕ).PairwiseDisjoint dyadicPrimeBlock := by
  intro i hi j hj hij
  exact dyadicPrimeBlock_disjoint hij

/-- If every exponent in `S` satisfies the room condition
`c X 2^j ≤ n`, all primes in all those blocks lie below `2n/(cX)`.

The proof deliberately goes through the disjoint union of the blocks.  Thus
the left side counts every prime exactly once, rather than losing a factor
`S.card` by bounding the blocks one at a time. -/
theorem sum_card_dyadicPrimeBlock_le_primeCounting
    {S : Finset ℕ} {c X n : ℕ} (hc : 0 < c) (hX : 0 < X)
    (hroom : ∀ j ∈ S, c * X * 2 ^ j ≤ n) :
    ∑ j ∈ S, (dyadicPrimeBlock j).card ≤
      Nat.primeCounting (2 * n / (c * X)) := by
  let U : Finset ℕ := S.biUnion dyadicPrimeBlock
  have hUsub : U ⊆ primesUpTo (2 * n / (c * X)) := by
    intro p hp
    rcases Finset.mem_biUnion.mp hp with ⟨j, hjS, hpj⟩
    have hpPrime : p.Prime := prime_of_mem_dyadicPrimeBlock hpj
    have hpUpper : p ≤ 2 * 2 ^ j := by
      simpa [pow_succ, Nat.mul_comm] using le_upper_of_mem_dyadicPrimeBlock hpj
    have hprod : p * (c * X) ≤ 2 * n := by
      calc
        p * (c * X) ≤ (2 * 2 ^ j) * (c * X) :=
          Nat.mul_le_mul_right (c * X) hpUpper
        _ = 2 * (c * X * 2 ^ j) := by ring
        _ ≤ 2 * n := Nat.mul_le_mul_left 2 (hroom j hjS)
    have hpBound : p ≤ 2 * n / (c * X) :=
      (Nat.le_div_iff_mul_le (Nat.mul_pos hc hX)).2 hprod
    exact mem_primesUpTo.mpr ⟨hpPrime, hpBound⟩
  calc
    ∑ j ∈ S, (dyadicPrimeBlock j).card = U.card := by
      symm
      exact Finset.card_biUnion (pairwiseDisjoint_dyadicPrimeBlock S)
    _ ≤ (primesUpTo (2 * n / (c * X))).card := Finset.card_le_card hUsub
    _ = Nat.primeCounting (2 * n / (c * X)) := card_primesUpTo _

/-- A single absolute constant controls the prime-counting term produced by
the disjoint-union lemma, expressed at the natural quotient `m = n / d`.

The harmless factor `4` absorbs the possible remainder in natural-number
division: if `m ≥ 1`, then `(2n)/d ≤ 4m`. -/
theorem exists_forall_primeCounting_two_mul_div_le_scale :
    ∃ C : ℝ, 0 < C ∧ ∀ n d : ℕ, 0 < d → 1 ≤ n / d →
      (Nat.primeCounting (2 * n / d) : ℝ) ≤
        C * (((n / d : ℕ) : ℝ) / lambda ((n / d : ℕ) : ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := exists_forall_primeCounting_le_scale
  refine ⟨4 * C, mul_pos (by norm_num) hCpos, ?_⟩
  intro n d hd hm
  let m : ℕ := n / d
  let B : ℕ := 2 * n / d
  have hmOne : 1 ≤ m := by simpa [m] using hm
  have hmposR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hBm : m ≤ B := by
    dsimp [m, B]
    exact Nat.div_le_div_right (by omega : n ≤ 2 * n)
  have hBfour : B ≤ 4 * m := by
    have hmod : n % d < d := Nat.mod_lt n hd
    have hdecomp : n % d + d * m = n := by
      simpa only [m] using Nat.mod_add_div n d
    have hdle : d ≤ d * m := by
      simpa only [mul_one] using Nat.mul_le_mul_left d hmOne
    apply (Nat.div_le_iff_le_mul hd).2
    have hmain : 2 * n ≤ 4 * m * d := by nlinarith
    omega
  have hlamM : 0 < lambda (m : ℝ) := lambda_pos (by exact_mod_cast hmOne)
  have hlamMono : lambda (m : ℝ) ≤ lambda (B : ℝ) := by
    apply lambda_mono hmposR
    exact_mod_cast hBm
  have hscale : (B : ℝ) / lambda (B : ℝ) ≤
      4 * ((m : ℝ) / lambda (m : ℝ)) := by
    calc
      (B : ℝ) / lambda (B : ℝ) ≤ (B : ℝ) / lambda (m : ℝ) := by
        exact div_le_div_of_nonneg_left (by positivity) hlamM hlamMono
      _ ≤ ((4 * m : ℕ) : ℝ) / lambda (m : ℝ) := by
        exact div_le_div_of_nonneg_right (by exact_mod_cast hBfour) hlamM.le
      _ = 4 * ((m : ℝ) / lambda (m : ℝ)) := by
        norm_num
        ring
  calc
    (Nat.primeCounting (2 * n / d) : ℝ) =
        (Nat.primeCounting B : ℝ) := by rfl
    _ ≤ C * ((B : ℝ) / lambda (B : ℝ)) := hC B
    _ ≤ C * (4 * ((m : ℝ) / lambda (m : ℝ))) :=
      mul_le_mul_of_nonneg_left hscale hCpos.le
    _ = (4 * C) * (((n / d : ℕ) : ℝ) / lambda ((n / d : ℕ) : ℝ)) := by
      simp only [m]
      ring

/-- Uniform analytic form of `sum_card_dyadicPrimeBlock_le_primeCounting`.
It is valid for every finite exponent set and every positive pair `c,X`, as
soon as the natural quotient `n/(cX)` is nonzero. -/
theorem exists_forall_sum_card_dyadicPrimeBlock_le_scale :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : Finset ℕ) (c X n : ℕ), 0 < c → 0 < X → 1 ≤ n / (c * X) →
        (∀ j ∈ S, c * X * 2 ^ j ≤ n) →
        (∑ j ∈ S, ((dyadicPrimeBlock j).card : ℝ)) ≤
          C * (((n / (c * X) : ℕ) : ℝ) /
            lambda ((n / (c * X) : ℕ) : ℝ)) := by
  obtain ⟨C, hCpos, hC⟩ := exists_forall_primeCounting_two_mul_div_le_scale
  refine ⟨C, hCpos, ?_⟩
  intro S c X n hc hX hquot hroom
  have hfinite := sum_card_dyadicPrimeBlock_le_primeCounting hc hX hroom
  have hfiniteR :
      (∑ j ∈ S, ((dyadicPrimeBlock j).card : ℝ)) ≤
        (Nat.primeCounting (2 * n / (c * X)) : ℝ) := by
    exact_mod_cast hfinite
  exact hfiniteR.trans (hC n (c * X) (Nat.mul_pos hc hX) hquot)

/-- Passing from the natural quotient `m = n/d` to the exact real quotient
costs at most a factor two on the regularized prime-counting scale.

The proof uses only `m ≤ n/d < m+1 ≤ 2m` and
`lambda (2m) ≤ 2 lambda m`; the latter follows from `log 2 ≤ 1` and
`log m ≥ 0`. -/
theorem natQuotient_div_lambda_le_two_realQuotient_div_lambda
    {n d : ℕ} (hd : 0 < d) (hm : 1 ≤ n / d) :
    (((n / d : ℕ) : ℝ) / lambda ((n / d : ℕ) : ℝ)) ≤
      2 * (((n : ℝ) / (d : ℝ)) / lambda ((n : ℝ) / (d : ℝ))) := by
  let m : ℕ := n / d
  let x : ℝ := (n : ℝ) / (d : ℝ)
  have hmOneNat : 1 ≤ m := by simpa [m] using hm
  have hmOne : (1 : ℝ) ≤ m := by exact_mod_cast hmOneNat
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hmx : (m : ℝ) ≤ x := by
    dsimp [m, x]
    exact Nat.cast_div_le
  have hxpos : 0 < x := lt_of_lt_of_le (by positivity : (0 : ℝ) < m) hmx
  have hnlt : n < (m + 1) * d := by
    apply (Nat.div_lt_iff_lt_mul hd).1
    simp [m]
  have hxlt : x < (m : ℝ) + 1 := by
    apply (div_lt_iff₀ hdR).2
    exact_mod_cast (by simpa [Nat.add_mul] using hnlt)
  have hmSuccLe : (m : ℝ) + 1 ≤ 2 * m := by
    exact_mod_cast (show m + 1 ≤ 2 * m by omega)
  have hxTwoM : x ≤ 2 * (m : ℝ) := hxlt.le.trans hmSuccLe
  have hlamM : 0 < lambda (m : ℝ) := lambda_pos hmOne
  have hxOne : (1 : ℝ) ≤ x := hmOne.trans hmx
  have hlamX : 0 < lambda x := lambda_pos hxOne
  have hlamXTwoM : lambda x ≤ lambda (2 * (m : ℝ)) := by
    exact lambda_mono hxpos hxTwoM
  have hlamTwoM : lambda (2 * (m : ℝ)) ≤ 2 * lambda (m : ℝ) := by
    rw [lambda_eq_one_add_log (by positivity),
      lambda_eq_one_add_log (by positivity), Real.log_mul (by norm_num) (by positivity)]
    have hlogTwo : Real.log 2 ≤ 1 := by
      have h := Real.log_le_sub_one_of_pos zero_lt_two
      norm_num at h
      exact h
    have hlogM : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg hmOne
    linarith
  have hlamCompare : lambda x ≤ 2 * lambda (m : ℝ) :=
    hlamXTwoM.trans hlamTwoM
  change (m : ℝ) / lambda (m : ℝ) ≤ 2 * (x / lambda x)
  calc
    (m : ℝ) / lambda (m : ℝ) ≤ x / lambda (m : ℝ) :=
      div_le_div_of_nonneg_right hmx hlamM.le
    _ ≤ 2 * (x / lambda x) := by
      rw [show 2 * (x / lambda x) = (2 * x) / lambda x by ring]
      apply (div_le_div_iff₀ hlamM hlamX).2
      have hmul := mul_le_mul_of_nonneg_left hlamCompare hxpos.le
      nlinarith

/-- Exact-real-quotient version of the uniform block-sum estimate.  This is
the form used after a core `c` and a dyadic scale `X` have been fixed in the
upper-bound argument. -/
theorem exists_forall_sum_card_dyadicPrimeBlock_le_real_scale :
    ∃ C : ℝ, 0 < C ∧
      ∀ (S : Finset ℕ) (c X n : ℕ), 0 < c → 0 < X → 1 ≤ n / (c * X) →
        (∀ j ∈ S, c * X * 2 ^ j ≤ n) →
        (∑ j ∈ S, ((dyadicPrimeBlock j).card : ℝ)) ≤
          C * (((n : ℝ) / ((c : ℝ) * (X : ℝ))) /
            lambda ((n : ℝ) / ((c : ℝ) * (X : ℝ)))) := by
  obtain ⟨C, hCpos, hC⟩ :=
    exists_forall_sum_card_dyadicPrimeBlock_le_scale
  refine ⟨2 * C, mul_pos (by norm_num) hCpos, ?_⟩
  intro S c X n hc hX hquot hroom
  have hnat := hC S c X n hc hX hquot hroom
  have hcompare := natQuotient_div_lambda_le_two_realQuotient_div_lambda
    (Nat.mul_pos hc hX) hquot
  calc
    (∑ j ∈ S, ((dyadicPrimeBlock j).card : ℝ)) ≤
        C * (((n / (c * X) : ℕ) : ℝ) /
          lambda ((n / (c * X) : ℕ) : ℝ)) := hnat
    _ ≤ C * (2 * (((n : ℝ) / ((c * X : ℕ) : ℝ)) /
          lambda ((n : ℝ) / ((c * X : ℕ) : ℝ)))) :=
      mul_le_mul_of_nonneg_left hcompare hCpos.le
    _ = (2 * C) * (((n : ℝ) / ((c : ℝ) * (X : ℝ))) /
          lambda ((n : ℝ) / ((c : ℝ) * (X : ℝ)))) := by
      norm_num
      ring

end
end CoreBridgePrime
end Erdos888
