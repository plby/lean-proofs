/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.ShiftedMassFirstMoment

/-!
# Prime residue classes inside finite intervals

For one residue class modulo a prime, choose its least prime in the interval.
Every other member is that prime plus a nonnegative multiple of the modulus,
so the class injects into the duplicated affine-prime candidate set from the
previous file.
-/

namespace Erdos822

/-- Primes in an open-left closed-right interval, above the sieve cutoff,
lying in one residue class modulo p. -/
def primeResidueInterval (p a L U y : ℕ) : Finset ℕ :=
  (Finset.Ioc L U).filter fun q =>
    q.Prime ∧ y < q ∧ q % p = a % p

@[simp]
theorem mem_primeResidueInterval_iff
    {p a L U y q : ℕ} :
    q ∈ primeResidueInterval p a L U y ↔
      L < q ∧ q ≤ U ∧ q.Prime ∧ y < q ∧ q % p = a % p := by
  simp [primeResidueInterval, and_assoc]

/-- A nonempty prime residue interval injects into one duplicated affine
prime-candidate set, based at its least member. -/
theorem card_primeResidueInterval_le_duplicateCandidates_of_nonempty
    {p a L U y : ℕ} (hp : p.Prime)
    (hne : (primeResidueInterval p a L U y).Nonempty) :
    let q₀ := (primeResidueInterval p a L U y).min' hne
    (primeResidueInterval p a L U y).card ≤
      (twoAffinePrimeCandidates p q₀ p q₀ ((U - L) / p + 1) y).card := by
  classical
  let Q := primeResidueInterval p a L U y
  let q₀ := Q.min' hne
  dsimp only
  have hq₀mem : q₀ ∈ Q := Finset.min'_mem Q hne
  have hq₀data := mem_primeResidueInterval_iff.mp hq₀mem
  let f : ℕ → ℕ := fun q => (q - q₀) / p
  have hrepr : ∀ q ∈ Q, p * f q + q₀ = q := by
    intro q hq
    have hqdata := mem_primeResidueInterval_iff.mp hq
    have hq₀q : q₀ ≤ q := Finset.min'_le Q q hq
    have hmod : q₀ ≡ q [MOD p] := by
      show q₀ % p = q % p
      exact hq₀data.2.2.2.2.trans hqdata.2.2.2.2.symm
    have hdvd : p ∣ q - q₀ := hmod.dvd'
    have hmul : p * ((q - q₀) / p) = q - q₀ :=
      Nat.mul_div_cancel' hdvd
    dsimp [f]
    rw [hmul]
    exact Nat.sub_add_cancel hq₀q
  apply Finset.card_le_card_of_injOn f
  · intro q hq
    have hqdata := mem_primeResidueInterval_iff.mp hq
    have hq₀q : q₀ ≤ q := Finset.min'_le Q q hq
    have hreprq := hrepr q hq
    change f q ∈ twoAffinePrimeCandidates p q₀ p q₀ ((U - L) / p + 1) y
    rw [mem_twoAffinePrimeCandidates_iff]
    have hmul : p * f q ≤ U - L := by
      have hq₀L : L < q₀ := hq₀data.1
      omega
    have hf : f q ≤ (U - L) / p :=
      (Nat.le_div_iff_mul_le hp.pos).2 (by
        simpa [Nat.mul_comm] using hmul)
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · simpa [hreprq] using hqdata.2.2.1
    · simpa [hreprq] using hqdata.2.2.1
    · simpa [hreprq] using hqdata.2.2.2.1
    · simpa [hreprq] using hqdata.2.2.2.1
  · intro q hq q' hq' hf
    have hqrepr := hrepr q hq
    have hq'repr := hrepr q' hq'
    rw [hf] at hqrepr
    omega

/-- Uniform beta-sieve cardinality bound for one prime residue interval. -/
theorem exists_primeResidueInterval_card_upper_bound :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ p a L U y S : ℕ,
        p.Prime → 2 ≤ y → 101 ≤ S →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        ((primeResidueInterval p a L U y).card : ℝ) ≤
          (((U - L) / p + 1 : ℕ) : ℝ) *
            ((1 + eta) *
              (C * (Real.log (2 : ℝ) / Real.log (y : ℝ)) *
                Real.exp 3)) +
            ((y ^ S : ℕ) : ℝ) ^ 2 := by
  obtain ⟨A, C, hA, hC, hdup⟩ :=
    exists_duplicateAffinePrimeCandidates_upper_bound
  refine ⟨A, C, hA, hC, ?_⟩
  intro p a L U y S hp hy hS hlog
  dsimp only
  by_cases hne : (primeResidueInterval p a L U y).Nonempty
  · let q₀ := (primeResidueInterval p a L U y).min' hne
    have hq₀mem : q₀ ∈ primeResidueInterval p a L U y :=
      Finset.min'_mem _ hne
    have hq₀data := mem_primeResidueInterval_iff.mp hq₀mem
    have hcard :=
      card_primeResidueInterval_le_duplicateCandidates_of_nonempty hp hne
    have hbound := hdup p q₀ ((U - L) / p + 1) y S hp
      hq₀data.2.2.1 hq₀data.2.2.2.1 hy hS hlog
    dsimp only at hcard hbound
    have hcardR :
        ((primeResidueInterval p a L U y).card : ℝ) ≤
          ((twoAffinePrimeCandidates p q₀ p q₀ ((U - L) / p + 1) y).card : ℝ) := by
      exact_mod_cast hcard
    exact hcardR.trans hbound
  · have hempty : primeResidueInterval p a L U y = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hne
    rw [hempty]
    simp only [Finset.card_empty, Nat.cast_zero]
    have heta :
        0 ≤ 1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100) := by
      positivity
    have hlog2 : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
    have hlogy : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    positivity

/-- Reciprocal mass in one residue interval is bounded by its cardinality
divided by the first possible integer in the interval. -/
theorem sum_inv_primeResidueInterval_le_card_div
    (p a L U y : ℕ) :
    ∑ q ∈ primeResidueInterval p a L U y, (1 : ℝ) / q ≤
      ((primeResidueInterval p a L U y).card : ℝ) / (L + 1) := by
  calc
    (∑ q ∈ primeResidueInterval p a L U y, (1 : ℝ) / q) ≤
        ∑ q ∈ primeResidueInterval p a L U y,
          (1 : ℝ) / (L + 1) := by
      apply Finset.sum_le_sum
      intro q hq
      have hqdata := mem_primeResidueInterval_iff.mp hq
      have hLq : L + 1 ≤ q := by omega
      exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hLq)
    _ = ((primeResidueInterval p a L U y).card : ℝ) / (L + 1) := by
      rw [Finset.sum_const]
      simp
      ring

/-- Combining the cardinal beta-sieve bound with the preceding reciprocal
comparison gives a summation-ready bound for one residue interval. -/
theorem exists_sum_inv_primeResidueInterval_upper_bound :
    ∃ A C : ℝ, 1 ≤ A ∧ 0 < C ∧
      ∀ p a L U y S : ℕ,
        p.Prime → 2 ≤ y → 101 ≤ S →
        Real.log A ≤ 4 * (S - 100 : ℕ) / 99 →
        let eta := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
        ∑ q ∈ primeResidueInterval p a L U y, (1 : ℝ) / q ≤
          ((((U - L) / p + 1 : ℕ) : ℝ) *
              ((1 + eta) *
                (C * (Real.log (2 : ℝ) / Real.log (y : ℝ)) *
                  Real.exp 3)) +
              ((y ^ S : ℕ) : ℝ) ^ 2) / (L + 1) := by
  obtain ⟨A, C, hA, hC, hcard⟩ :=
    exists_primeResidueInterval_card_upper_bound
  refine ⟨A, C, hA, hC, ?_⟩
  intro p a L U y S hp hy hS hlog
  dsimp only
  calc
    (∑ q ∈ primeResidueInterval p a L U y, (1 : ℝ) / q) ≤
        ((primeResidueInterval p a L U y).card : ℝ) / (L + 1) :=
      sum_inv_primeResidueInterval_le_card_div p a L U y
    _ ≤ ((((U - L) / p + 1 : ℕ) : ℝ) *
            ((1 + (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
              (C * (Real.log (2 : ℝ) / Real.log (y : ℝ)) *
                Real.exp 3)) +
            ((y ^ S : ℕ) : ℝ) ^ 2) / (L + 1) := by
      exact div_le_div_of_nonneg_right
        (hcard p a L U y S hp hy hS hlog) (by positivity)

end Erdos822
