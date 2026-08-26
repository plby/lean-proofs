import ErdosProblems.Erdos67b.MRHalaszOrdinaryBands
import ErdosProblems.Erdos67b.MRIntervalSieve

/-!
# Sieve square-mass bounds for complementary prime bands

An arithmetic coefficient supported on integers all of whose prime factors
lie in a band `Q` automatically avoids every prime packet disjoint from
`Q`.  Combining this observation with the arbitrary-interval Selberg bound
gives the concrete `L²` estimate used for the medium and large factors in
the cheap Halász decomposition.
-/

open scoped BigOperators ComplexConjugate
open Finset

namespace Erdos67b.MRHalaszBands

noncomputable section

open Erdos67b.SelbergSupport
open Erdos67b.MRIntervalSieve

/-- A positive integer supported on `Q` is not divisible by a prime from a
packet disjoint from `Q`. -/
theorem not_dvd_of_primeSupported_of_disjoint
    {Q : ℕ → Prop} {P : Finset ℕ}
    (hdisj : ∀ p ∈ P, ¬ Q p) {n p : ℕ}
    (hn : PrimeSupported Q n) (hpP : p ∈ P) (hp : p.Prime) :
    ¬ p ∣ n := by
  intro hpn
  have hmem : p ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hp, hpn, hn.1⟩
  exact hdisj p hpP (hn.2 p hmem)

/-- A one-bounded coefficient restricted to a prime band has arbitrary-
interval square mass bounded by the reciprocal mass of any disjoint prime
packet, with the explicit finite endpoint loss. -/
theorem sum_normSq_primeBandCoefficient_le
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hmass : 0 < reciprocalMass P)
    (Q : ℕ → Prop) [DecidablePred Q]
    (hdisj : ∀ p ∈ P, ¬ Q p)
    (a : ℕ → ℂ) (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {L U : ℕ} (hLU : L ≤ U) :
    (∑ n ∈ Finset.Ioc L U,
        Complex.normSq (primeBandCoefficient a Q n)) ≤
      ((U - L : ℕ) : ℝ) / (1 + reciprocalMass P) +
        2 * P.card + P.card ^ 2 := by
  apply sum_normSq_le_of_prime_avoiding_support P hprime hmass
  · intro n hn
    unfold primeBandCoefficient
    split_ifs with hsupp
    · exact ha n hn
    · simp
  · exact hLU
  · intro n hn hncoeff p hpP
    unfold primeBandCoefficient at hncoeff
    split_ifs at hncoeff with hsupp
    · exact not_dvd_of_primeSupported_of_disjoint hdisj hsupp hpP
        (hprime p hpP)
    · exact (hncoeff rfl).elim

/-- The same estimate for the complementary band. -/
theorem sum_normSq_primeBandCoefficient_compl_le
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime)
    (hmass : 0 < reciprocalMass P)
    (Q : ℕ → Prop) [DecidablePred Q]
    (hpacket : ∀ p ∈ P, Q p)
    (a : ℕ → ℂ) (ha : ∀ n, 0 < n → ‖a n‖ ≤ 1)
    {L U : ℕ} (hLU : L ≤ U) :
    (∑ n ∈ Finset.Ioc L U,
        Complex.normSq
          (primeBandCoefficient a (fun p ↦ ¬ Q p) n)) ≤
      ((U - L : ℕ) : ℝ) / (1 + reciprocalMass P) +
        2 * P.card + P.card ^ 2 := by
  apply sum_normSq_primeBandCoefficient_le P hprime hmass
    (fun p ↦ ¬ Q p)
  · intro p hp hnot
    exact hnot (hpacket p hp)
  · exact ha
  · exact hLU

end

end Erdos67b.MRHalaszBands
