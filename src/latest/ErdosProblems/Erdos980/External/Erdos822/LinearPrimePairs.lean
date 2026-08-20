/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos980.External.Erdos822.LinearParameterization
import ErdosProblems.Erdos980.External.Erdos822.SlopeAwareRosser

/-!
# Primitive linear prime-pair fibers

Fix one base solution of a primitive equation.  Every later ordered prime
solution is injected into a parameter for two affine prime forms.  This is a
finite, assumption-free version of the parameterization used before the
Selberg upper bound.
-/

namespace Erdos822

open Erdos851.FiniteCombinatorialSieve

/-- Ordered large-prime solutions of the primitive equation through a fixed
base point, truncated by a common upper bound. -/
def orderedLinearPrimeSolutions
    (A B q q' U y : ℕ) : Finset (ℕ × ℕ) :=
  (((Finset.Icc q U).filter fun p ↦ p.Prime ∧ y < p).product
      ((Finset.Icc q' U).filter fun p' ↦ p'.Prime ∧ y < p')).filter
    fun z ↦ A * z.1 + B * q' = A * q + B * z.2

@[simp]
theorem mem_orderedLinearPrimeSolutions_iff
    {A B q q' U y p p' : ℕ} :
    (p, p') ∈ orderedLinearPrimeSolutions A B q q' U y ↔
      q ≤ p ∧ p ≤ U ∧ p.Prime ∧ y < p ∧
        q' ≤ p' ∧ p' ≤ U ∧ p'.Prime ∧ y < p' ∧
          A * p + B * q' = A * q + B * p' := by
  simp [orderedLinearPrimeSolutions, and_assoc]

/-- The parameter associated to a solution is its first-coordinate advance
divided by the opposite coefficient. -/
def linearSolutionParameter (B q : ℕ) (z : ℕ × ℕ) : ℕ :=
  (z.1 - q) / B

/-- Every ordered solution maps injectively into the corresponding pair of
affine prime candidates. -/
theorem card_orderedLinearPrimeSolutions_le_primeCandidates
    {A B q q' U y : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hcop : A.Coprime B) :
    (orderedLinearPrimeSolutions A B q q' U y).card ≤
      (twoAffinePrimeCandidates B q A q' (U + 1) y).card := by
  classical
  let f : ℕ × ℕ → ℕ := linearSolutionParameter B q
  apply Finset.card_le_card_of_injOn f
  · intro z hz
    rcases z with ⟨p, p'⟩
    change (p, p') ∈ orderedLinearPrimeSolutions A B q q' U y at hz
    rw [mem_orderedLinearPrimeSolutions_iff] at hz
    rcases hz with ⟨hqp, hpU, hpPrime, hyp, hq'p', hp'U,
      hp'Prime, hyp', heq⟩
    obtain ⟨k, hpk, hp'k⟩ :=
      exists_common_parameter_of_coprime_linear_eq hA hB hcop
        hqp hq'p' heq
    have hf : f (p, p') = k := by
      simp [f, linearSolutionParameter, hpk, hB.ne']
    change f (p, p') ∈ twoAffinePrimeCandidates B q A q' (U + 1) y
    rw [hf, mem_twoAffinePrimeCandidates_iff]
    have hkU : k < U + 1 := by
      have hkBk : k ≤ B * k := Nat.le_mul_of_pos_left k hB
      have hkp : k ≤ p := by omega
      omega
    refine ⟨hkU, ?_, ?_, ?_, ?_⟩
    · simpa [hpk, Nat.add_comm] using hpPrime
    · simpa [hp'k, Nat.add_comm] using hp'Prime
    · simpa [hpk, Nat.add_comm] using hyp
    · simpa [hp'k, Nat.add_comm] using hyp'
  · intro z hz w hw hfw
    rcases z with ⟨p, p'⟩
    rcases w with ⟨r, r'⟩
    change (p, p') ∈ orderedLinearPrimeSolutions A B q q' U y at hz
    change (r, r') ∈ orderedLinearPrimeSolutions A B q q' U y at hw
    rw [mem_orderedLinearPrimeSolutions_iff] at hz hw
    rcases hz with ⟨hqp, _hpU, _hpPrime, _hyp, hq'p', _hp'U,
      _hp'Prime, _hyp', heq⟩
    rcases hw with ⟨hqr, _hrU, _hrPrime, _hyr, hq'r', _hr'U,
      _hr'Prime, _hyr', heqr⟩
    obtain ⟨k, hpk, hp'k⟩ :=
      exists_common_parameter_of_coprime_linear_eq hA hB hcop
        hqp hq'p' heq
    obtain ⟨l, hrl, hr'l⟩ :=
      exists_common_parameter_of_coprime_linear_eq hA hB hcop
        hqr hq'r' heqr
    have hfk : f (p, p') = k := by
      simp [f, linearSolutionParameter, hpk, hB.ne']
    have hfl : f (r, r') = l := by
      simp [f, linearSolutionParameter, hrl, hB.ne']
    have hkl : k = l := by
      rw [hfk, hfl] at hfw
      exact hfw
    rw [← hkl] at hrl hr'l
    have hpr : p = r := hpk.trans hrl.symm
    have hp'r' : p' = r' := hp'k.trans hr'l.symm
    simp [hpr, hp'r']

/-- The first-coordinate upper bound also bounds the common parameter after
division by the opposite primitive slope.  This is the scale-sensitive form
needed when summing fixed-cofactor collision fibers. -/
theorem card_orderedLinearPrimeSolutions_le_primeCandidates_div
    {A B q q' U y : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hcop : A.Coprime B) :
    (orderedLinearPrimeSolutions A B q q' U y).card ≤
      (twoAffinePrimeCandidates B q A q' (U / B + 1) y).card := by
  classical
  let f : ℕ × ℕ → ℕ := linearSolutionParameter B q
  apply Finset.card_le_card_of_injOn f
  · intro z hz
    rcases z with ⟨p, p'⟩
    change (p, p') ∈ orderedLinearPrimeSolutions A B q q' U y at hz
    rw [mem_orderedLinearPrimeSolutions_iff] at hz
    rcases hz with ⟨hqp, hpU, hpPrime, hyp, hq'p', _hp'U,
      hp'Prime, hyp', heq⟩
    obtain ⟨k, hpk, hp'k⟩ :=
      exists_common_parameter_of_coprime_linear_eq hA hB hcop
        hqp hq'p' heq
    have hf : f (p, p') = k := by
      simp [f, linearSolutionParameter, hpk, hB.ne']
    change f (p, p') ∈ twoAffinePrimeCandidates B q A q' (U / B + 1) y
    rw [hf, mem_twoAffinePrimeCandidates_iff]
    have hBkU : B * k ≤ U := by
      omega
    have hkdiv : k ≤ U / B := by
      apply (Nat.le_div_iff_mul_le hB).2
      simpa [Nat.mul_comm] using hBkU
    refine ⟨by omega, ?_, ?_, ?_, ?_⟩
    · simpa [hpk, Nat.add_comm] using hpPrime
    · simpa [hp'k, Nat.add_comm] using hp'Prime
    · simpa [hpk, Nat.add_comm] using hyp
    · simpa [hp'k, Nat.add_comm] using hyp'
  · intro z hz w hw hfw
    rcases z with ⟨p, p'⟩
    rcases w with ⟨r, r'⟩
    change (p, p') ∈ orderedLinearPrimeSolutions A B q q' U y at hz
    change (r, r') ∈ orderedLinearPrimeSolutions A B q q' U y at hw
    rw [mem_orderedLinearPrimeSolutions_iff] at hz hw
    rcases hz with ⟨hqp, _hpU, _hpPrime, _hyp, hq'p', _hp'U,
      _hp'Prime, _hyp', heq⟩
    rcases hw with ⟨hqr, _hrU, _hrPrime, _hyr, hq'r', _hr'U,
      _hr'Prime, _hyr', heqr⟩
    obtain ⟨k, hpk, hp'k⟩ :=
      exists_common_parameter_of_coprime_linear_eq hA hB hcop
        hqp hq'p' heq
    obtain ⟨l, hrl, hr'l⟩ :=
      exists_common_parameter_of_coprime_linear_eq hA hB hcop
        hqr hq'r' heqr
    have hfk : f (p, p') = k := by
      simp [f, linearSolutionParameter, hpk, hB.ne']
    have hfl : f (r, r') = l := by
      simp [f, linearSolutionParameter, hrl, hB.ne']
    have hkl : k = l := by
      rw [hfk, hfl] at hfw
      exact hfw
    rw [← hkl] at hrl hr'l
    have hpr : p = r := hpk.trans hrl.symm
    have hp'r' : p' = r' := hp'k.trans hr'l.symm
    simp [hpr, hp'r']

/-- The preceding injection and the affine beta sieve give a concrete
dimension-two upper bound for every primitive ordered linear prime fiber. -/
theorem exists_orderedLinearPrimeSolutions_concrete_upper_bound :
    ∃ C : ℝ, 1 ≤ C ∧
      ∀ A B q q' U z y S : ℕ,
        0 < A → 0 < B → A.Coprime B →
        (∀ p : ℕ, p.Prime →
          p ∣ Erdos387.sievePrimeProduct z (y + 1) → ¬ p ∣ B ∧ ¬ p ∣ A) →
        2 ≤ z → z ≤ y → 1 < y → 101 ≤ S →
        Real.log C ≤ 4 * (S - 100 : ℕ) / 99 →
        let V := Erdos851.localEulerProduct
          (Erdos851.pairShiftDensity (affineDetNat B q A q')) z y
        let eta := (4 * C / 3) * (1 / 4 : ℝ) ^ (S - 100)
        let D := y ^ S
        ((orderedLinearPrimeSolutions A B q q' U y).card : ℝ) ≤
          ((U + 1 : ℕ) : ℝ) * ((1 + eta) * V) + (D : ℝ) ^ 2 := by
  obtain ⟨C, hC, hprime⟩ :=
    exists_twoAffinePrimeCandidates_concrete_upper_bound
  refine ⟨C, hC, ?_⟩
  intro A B q q' U z y S hA hB hcop hadmissible hz hzy hy hS hlog
  dsimp only
  calc
    ((orderedLinearPrimeSolutions A B q q' U y).card : ℝ) ≤
        ((twoAffinePrimeCandidates B q A q' (U + 1) y).card : ℝ) := by
      exact_mod_cast card_orderedLinearPrimeSolutions_le_primeCandidates
        hA hB hcop
    _ ≤ ((U + 1 : ℕ) : ℝ) *
          ((1 + (4 * C / 3) * (1 / 4 : ℝ) ^ (S - 100)) *
            Erdos851.localEulerProduct
              (Erdos851.pairShiftDensity (affineDetNat B q A q')) z y) +
          ((y ^ S : ℕ) : ℝ) ^ 2 :=
      hprime B q A q' (U + 1) z y S hadmissible hz hzy hy hS hlog

/-- The slope-aware Rosser sieve gives an unconditional finite upper-main
bound once the fixed base constants are large primes. -/
theorem card_orderedLinearPrimeSolutions_le_slopeAware_upperMain
    {A B q q' U z y S : ℕ}
    (hA : 0 < A) (hB : 0 < B) (hcop : A.Coprime B)
    (hq : q.Prime) (hq' : q'.Prime) (hyq : y < q) (hyq' : y < q')
    (hz : 2 ≤ z) (hy : 1 < y) (hS : 1 ≤ S) :
    let P := ascendingSlopeAwareSievePrimes B A z (y + 1)
    let D := y ^ S
    let stop := rosserStoppingPredicate 100 D
    ((orderedLinearPrimeSolutions A B q q' U y).card : ℝ) ≤
      ((U + 1 : ℕ) : ℝ) *
        upperMainTerm stop (twoAffineNu B q A q') P +
          (D : ℝ) ^ 2 := by
  dsimp only
  calc
    ((orderedLinearPrimeSolutions A B q q' U y).card : ℝ) ≤
        ((twoAffinePrimeCandidates B q A q' (U + 1) y).card : ℝ) := by
      exact_mod_cast card_orderedLinearPrimeSolutions_le_primeCandidates
        hA hB hcop
    _ ≤ ((U + 1 : ℕ) : ℝ) *
          upperMainTerm
            (rosserStoppingPredicate 100 (y ^ S))
            (twoAffineNu B q A q')
            (ascendingSlopeAwareSievePrimes B A z (y + 1)) +
          ((y ^ S : ℕ) : ℝ) ^ 2 :=
      twoAffinePrimeCandidates_card_le_slopeAware_upperMain
        hq hq' hyq hyq' hz hy hS

end Erdos822
