import ErdosProblems.Erdos327.Analytic.WeightedLinearSieveCutoff

/-!
# Truncated-degree boundary bound for the finite weighted sieve

The generic cutoff bound charges all subsets through a coarse `2^|P|`
factor.  Here only degrees `k ≤ 2R` occur, so binomial coefficients can
instead be bounded by `|P|^k ≤ z^k`.
-/

namespace Erdos327.Analytic

open Finset
open scoped BigOperators

/-- A finite set of primes at most `z` has cardinality at most `z`. -/
theorem card_le_cutoff_of_subset_primesLE
    {P : Finset ℕ} {z : ℕ} (hPz : P ⊆ Nat.primesLE z) :
    P.card ≤ z := by
  have hPIcc : P ⊆ Icc 1 z := by
    intro p hp
    have hpData := Nat.mem_primesLE.mp (hPz hp)
    exact mem_Icc.mpr ⟨hpData.2.one_le, hpData.1⟩
  have hcard := card_le_card hPIcc
  simpa using hcard

/-- On a prime set below `z`, each binomial coefficient is at most
`z^k`. -/
theorem choose_card_le_cutoff_pow
    {P : Finset ℕ} {z k : ℕ} (hPz : P ⊆ Nat.primesLE z) :
    Nat.choose P.card k ≤ z ^ k := by
  exact (Nat.choose_le_pow P.card k).trans
    (Nat.pow_le_pow_left
      (card_le_cutoff_of_subset_primesLE hPz) k)

/-- Degree truncation replaces the exponential `2^|P|` boundary by a
polynomial expression in `R` and `z`. -/
theorem subsetBoundarySum_le_truncated_polynomial
    {P : Finset ℕ} {z X R : ℕ}
    (hz : 1 ≤ z) (hPz : P ⊆ Nat.primesLE z) :
    (∑ k ∈ range (2 * R + 1),
        ∑ T ∈ (univ : Finset P).powersetCard k,
          (3 : ℝ) ^ T.card *
            (9 * (X : ℝ) + subsetModulus T)) ≤
      ((2 * R + 1 : ℕ) : ℝ) *
        (z : ℝ) ^ (2 * R) * (3 : ℝ) ^ (2 * R) *
        (9 * (X : ℝ) + (z : ℝ) ^ (2 * R)) := by
  have hpz : ∀ p ∈ P, p ≤ z := fun p hp ↦
    (Nat.mem_primesLE.mp (hPz hp)).1
  have hchoose :=
    subsetBoundarySum_le_choose
      (P := P) (z := z) (X := X) (m := 2 * R + 1) hpz
  have hterm (k : ℕ) (hk : k ∈ range (2 * R + 1)) :
      (Nat.choose P.card k : ℝ) *
          ((3 : ℝ) ^ k *
            (9 * (X : ℝ) + (z : ℝ) ^ k)) ≤
        (z : ℝ) ^ (2 * R) *
          ((3 : ℝ) ^ (2 * R) *
            (9 * (X : ℝ) + (z : ℝ) ^ (2 * R))) := by
    have hkR : k ≤ 2 * R := by
      rw [mem_range] at hk
      omega
    have hchooseNat := choose_card_le_cutoff_pow
      (P := P) (z := z) (k := k) hPz
    have hzpowNat : z ^ k ≤ z ^ (2 * R) :=
      Nat.pow_le_pow_right (by omega) hkR
    have hchooseReal :
        (Nat.choose P.card k : ℝ) ≤ (z : ℝ) ^ (2 * R) := by
      exact_mod_cast hchooseNat.trans hzpowNat
    have h3pow :
        (3 : ℝ) ^ k ≤ (3 : ℝ) ^ (2 * R) :=
      pow_le_pow_right₀ (by norm_num) hkR
    have hzpow :
        (z : ℝ) ^ k ≤ (z : ℝ) ^ (2 * R) :=
      pow_le_pow_right₀ (by exact_mod_cast hz) hkR
    have hinner :
        (3 : ℝ) ^ k *
            (9 * (X : ℝ) + (z : ℝ) ^ k) ≤
          (3 : ℝ) ^ (2 * R) *
            (9 * (X : ℝ) + (z : ℝ) ^ (2 * R)) := by
      exact mul_le_mul h3pow (add_le_add le_rfl hzpow)
        (by positivity) (by positivity)
    exact mul_le_mul hchooseReal hinner
      (by positivity) (by positivity)
  calc
    (∑ k ∈ range (2 * R + 1),
        ∑ T ∈ (univ : Finset P).powersetCard k,
          (3 : ℝ) ^ T.card *
            (9 * (X : ℝ) + subsetModulus T)) ≤
      ∑ k ∈ range (2 * R + 1),
        (Nat.choose P.card k : ℝ) *
          ((3 : ℝ) ^ k *
            (9 * (X : ℝ) + (z : ℝ) ^ k)) := hchoose
    _ ≤ ∑ _k ∈ range (2 * R + 1),
        (z : ℝ) ^ (2 * R) *
          ((3 : ℝ) ^ (2 * R) *
            (9 * (X : ℝ) + (z : ℝ) ^ (2 * R))) :=
      sum_le_sum fun k hk ↦ hterm k hk
    _ = _ := by
      simp
      ring

/-- Finite weighted-sieve bound with the truncated-degree polynomial
boundary in place of `2^|P|`. -/
theorem finiteWeightBoxSum_le_primeInvSum_add_truncated_boundary
    {P : Finset ℕ} {z : ℕ}
    (hprime : ∀ p ∈ P, p.Prime)
    [∀ p : P, NeZero (p : ℕ)]
    (w ell : ∀ p : P,
      ZMod (p : ℕ) × ZMod (p : ℕ) → ℝ)
    (hcomplement : ∀ (p : P) u, w p u + ell p u = 1)
    (hell0 : ∀ (p : P) u, 0 ≤ ell p u)
    (hell1 : ∀ (p : P) u, ell p u ≤ 1)
    (hsupport : ∀ p : P,
      (residueWeightSupport (p : ℕ) (ell p)).card ≤
        3 * (p : ℕ))
    (hPz : P ⊆ Nat.primesLE z)
    (hmean : ∀ p : P,
      localLossMean ell p ≤ 3 / (p : ℝ))
    (hz : 1 ≤ z) (X R : ℕ) :
    finiteWeightBoxSum w X ≤
      8 * (X : ℝ) ^ 2 * (∏ p : P, localWeightMean w p) +
        8 * (X : ℝ) ^ 2 *
          ((3 * primeInvSum z) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) +
        ((2 * R + 1 : ℕ) : ℝ) *
          (z : ℝ) ^ (2 * R) * (3 : ℝ) ^ (2 * R) *
          (9 * (X : ℝ) + (z : ℝ) ^ (2 * R)) := by
  have hmean0 : ∀ p : P, 0 ≤ localLossMean ell p := fun p ↦
    (localLossMean_nonneg_le_one
      hprime ell hell0 hell1 p).1
  have htail :=
    localLossFactorialTail_le_primeInvSum
      ell hmean0 hPz hmean (R := R)
  have htailScaled :
      8 * (X : ℝ) ^ 2 *
          ((∑ p : P, localLossMean ell p) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) ≤
        8 * (X : ℝ) ^ 2 *
          ((3 * primeInvSum z) ^ (2 * R + 1) /
            ((2 * R + 1).factorial : ℝ)) :=
    mul_le_mul_of_nonneg_left htail (by positivity)
  have hboundary :=
    subsetBoundarySum_le_truncated_polynomial
      (P := P) (X := X) (R := R) hz hPz
  calc
    finiteWeightBoxSum w X ≤
        8 * (X : ℝ) ^ 2 * (∏ p : P, localWeightMean w p) +
          8 * (X : ℝ) ^ 2 *
            ((∑ p : P, localLossMean ell p) ^ (2 * R + 1) /
              ((2 * R + 1).factorial : ℝ)) +
          ∑ k ∈ range (2 * R + 1),
            ∑ T ∈ (univ : Finset P).powersetCard k,
              (3 : ℝ) ^ T.card *
                (9 * (X : ℝ) + subsetModulus T) :=
      finiteWeightBoxSum_le_main_add_tail_add_boundary
        hprime w ell hcomplement hell0 hell1 hsupport X R
    _ ≤ _ :=
      add_le_add (add_le_add le_rfl htailScaled) hboundary

end Erdos327.Analytic
