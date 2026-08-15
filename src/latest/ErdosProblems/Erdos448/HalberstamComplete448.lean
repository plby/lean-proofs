import ErdosProblems.Erdos448.HalberstamLean
import ErdosProblems.Erdos448.PrimePowerConvolution448
import ErdosProblems.Erdos448.PrimePowerMassLinear448

/-!
A fully explicit, unconditional finite Halberstam--Richert mean-value bound.
This file assembles the three independently checked ingredients:

* the exact logarithmic prime-power convolution;
* the linear bound for the prime-power logarithmic mass;
* partial summation and the finite Euler-product majorant.

The first theorem uses the shifted prime-power indexing
`h (p^(j+1)) ≤ lambda1 * lambda2^j`.  The second restates the result in
the source-style indexing `h (p^nu) ≤ A * B^nu`.
-/

open scoped BigOperators
open Finset

namespace HalberstamComplete448

/-- An explicit Halberstam--Richert mean-value theorem, with the prime-power
hypothesis indexed from the first nontrivial power. -/
theorem halberstam_richert_explicit
    (h : ℕ → ℝ)
    (h0 : h 0 = 0)
    (h1 : h 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → h (m * n) = h m * h n)
    (hnonneg : ∀ n, 0 ≤ h n)
    (lambda1 lambda2 : ℝ)
    (hlambda1 : 0 ≤ lambda1)
    (hlambda2 : 0 ≤ lambda2)
    (hlambda2_lt : lambda2 < 2)
    (hpow : ∀ (p : ℕ), p.Prime → ∀ j : ℕ,
      h (p ^ (j + 1)) ≤ lambda1 * lambda2 ^ j)
    (N : ℕ) (hN : 2 ≤ N) :
    HalberstamScratch.partialSum h N ≤
      (HalberstamScratch.explicitMassConstant lambda1 lambda2 + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          ∏ p ∈ (N + 1).primesBelow,
            ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  apply HalberstamScratch.halberstam_richert_of_mass_convolution
      h h0 h1 hmul hnonneg
      (W := PrimePowerConvolution448.primePowerMass h)
      (K := HalberstamScratch.explicitMassConstant lambda1 lambda2)
      (N := N)
  · intro p hp
    exact (HalberstamScratch.prime_power_local_mass h p lambda1 lambda2 hp
      hnonneg h1 hlambda1 hlambda2 hlambda2_lt (hpow p hp)).1
  · exact HalberstamScratch.explicitMassConstant_nonneg hlambda1 hlambda2
  · exact hN
  · simpa [HalberstamScratch.logPartialSum,
        PrimePowerConvolution448.logPartialSum] using
      (PrimePowerConvolution448.logPartialSum_le_primePowerMass_convolution
        h hnonneg hmul N)
  · intro Q
    simpa [HalberstamScratch.explicitMassConstant,
        PrimePowerConvolution448.primePowerMass,
        PrimePowerMassLinear448.primePowerMass,
        PrimePowerMassLinear448.massConstant] using
      (PrimePowerMassLinear448.primePowerMass_le_linear h lambda1 lambda2
        hlambda1 hlambda2 hlambda2_lt (fun p j hp => hpow p hp j) Q)

/-- The same theorem with the prime-power hypothesis in the source-paper
indexing `h (p^nu) ≤ A * B^nu`. -/
theorem halberstam_richert_explicit_source_indexing
    (h : ℕ → ℝ)
    (h0 : h 0 = 0)
    (h1 : h 1 = 1)
    (hmul : ∀ {m n : ℕ}, m.Coprime n → h (m * n) = h m * h n)
    (hnonneg : ∀ n, 0 ≤ h n)
    (A B : ℝ)
    (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (hB_lt : B < 2)
    (hpow : ∀ (p : ℕ), p.Prime → ∀ nu : ℕ,
      h (p ^ nu) ≤ A * B ^ nu)
    (N : ℕ) (hN : 2 ≤ N) :
    HalberstamScratch.partialSum h N ≤
      (HalberstamScratch.explicitMassConstant (A * B) B + 1) *
        (N : ℝ) / Real.log (N : ℝ) *
          ∏ p ∈ (N + 1).primesBelow,
            ∑' j : ℕ, h (p ^ j) / ((p ^ j : ℕ) : ℝ) := by
  apply halberstam_richert_explicit h h0 h1 hmul hnonneg (A * B) B
      (mul_nonneg hA hB) hB hB_lt _ N hN
  intro p hp j
  calc
    h (p ^ (j + 1)) ≤ A * B ^ (j + 1) := hpow p hp (j + 1)
    _ = (A * B) * B ^ j := by rw [pow_succ]; ring

end HalberstamComplete448

#print axioms HalberstamComplete448.halberstam_richert_explicit
#print axioms HalberstamComplete448.halberstam_richert_explicit_source_indexing
