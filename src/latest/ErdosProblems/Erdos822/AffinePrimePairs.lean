/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.AffineBetaSieve

/-!
# Prime pairs among two affine forms

The beta sieve counts parameters whose two-form product has no small prime
factor.  A genuine pair of large prime values is a member of that sifted
set; this file records the finite inclusion used when collision equations
are parameterized.
-/

namespace Erdos822

/-- Parameters below X on which both affine forms are prime and exceed the
sieving ceiling. -/
def twoAffinePrimeCandidates
    (a s b t X y : ℕ) : Finset ℕ :=
  (Finset.range X).filter fun n ↦
    (a * n + s).Prime ∧ (b * n + t).Prime ∧
      y < a * n + s ∧ y < b * n + t

@[simp]
theorem mem_twoAffinePrimeCandidates_iff
    {a s b t X y n : ℕ} :
    n ∈ twoAffinePrimeCandidates a s b t X y ↔
      n < X ∧ (a * n + s).Prime ∧ (b * n + t).Prime ∧
        y < a * n + s ∧ y < b * n + t := by
  simp [twoAffinePrimeCandidates, and_assoc]

/-- If both affine values are primes above y, their product is coprime to
the product of all sieving primes in (z,y]. -/
theorem mem_siftedTwoAffineCandidates_of_mem_primeCandidates
    {a s b t X z y n : ℕ}
    (hn : n ∈ twoAffinePrimeCandidates a s b t X y) :
    n ∈ siftedTwoAffineCandidates a s b t X z (y + 1) := by
  rw [mem_twoAffinePrimeCandidates_iff] at hn
  rw [siftedTwoAffineCandidates, Finset.mem_filter]
  refine ⟨Finset.mem_range.mpr hn.1, ?_⟩
  by_contra hcop
  obtain ⟨p, hp, hpProd, hpAffine⟩ :=
    Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hpMem :=
    Erdos387.prime_mem_sievePrimes_of_dvd_product hp hpProd
  have hpy : p ≤ y := by
    have := (Erdos387.mem_sievePrimes.mp hpMem).2.2
    omega
  rw [twoAffineProduct] at hpAffine
  rcases hp.dvd_mul.mp hpAffine with hleft | hright
  · have hpeq : p = a * n + s :=
      ((hn.2.1.dvd_iff_eq hp.ne_one).mp hleft).symm
    omega
  · have hpeq : p = b * n + t :=
      ((hn.2.2.1.dvd_iff_eq hp.ne_one).mp hright).symm
    omega

theorem twoAffinePrimeCandidates_subset_sifted
    (a s b t X z y : ℕ) :
    twoAffinePrimeCandidates a s b t X y ⊆
      siftedTwoAffineCandidates a s b t X z (y + 1) := by
  intro n hn
  exact mem_siftedTwoAffineCandidates_of_mem_primeCandidates hn

/-- Every concrete upper bound for the sifted set is therefore also an
upper bound for genuine large prime pairs. -/
theorem exists_twoAffinePrimeCandidates_concrete_upper_bound :
    ∃ A : ℝ, 1 ≤ A ∧
      ∀ a s b t X z y S : ℕ,
        (∀ p : ℕ, p.Prime →
          p ∣ Erdos387.sievePrimeProduct z (y + 1) → ¬ p ∣ a ∧ ¬ p ∣ b) →
        2 ≤ z → z ≤ y → 1 < y → 101 ≤ S →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        let V := Erdos851.localEulerProduct
          (Erdos851.pairShiftDensity (affineDetNat a s b t)) z y
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := y ^ S
        ((twoAffinePrimeCandidates a s b t X y).card : ℝ) ≤
          (X : ℝ) * ((1 + eta) * V) + (D : ℝ) ^ 2 := by
  obtain ⟨A, hA, hbound⟩ :=
    exists_twoAffine_concrete_cardinality_upper_bound
  refine ⟨A, hA, ?_⟩
  intro a s b t X z y S hadmissible hz hzy hy hS hlog
  dsimp only
  calc
    ((twoAffinePrimeCandidates a s b t X y).card : ℝ) ≤
        ((siftedTwoAffineCandidates a s b t X z (y + 1)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card
        (twoAffinePrimeCandidates_subset_sifted a s b t X z y)
    _ ≤ (X : ℝ) *
          ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            Erdos851.localEulerProduct
              (Erdos851.pairShiftDensity (affineDetNat a s b t)) z y) +
          ((y ^ S : ℕ) : ℝ) ^ 2 :=
      hbound a s b t X z y S hadmissible hz hzy hy hS hlog

end Erdos822
