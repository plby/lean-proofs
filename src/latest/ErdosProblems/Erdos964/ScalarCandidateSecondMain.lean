import ErdosProblems.Erdos964.ScalarAffineModel
import ErdosProblems.Erdos964.ScalarAffineS2Main

/-!
# The explicit fixed-modulus second main term

The prime-removal kernel for the concrete linear coefficient family is a
squarefree sum coprime to the fixed normalization modulus. This is the
arithmetic expression whose moment asymptotics remain to be evaluated.
-/

namespace Erdos964

open scoped BigOperators

noncomputable def scalarCandidatePrimeKernel (M R p : ℕ) : ℝ :=
  ∑ r ∈ (Finset.Ico 1 R).filter (fun r => Squarefree r ∧ r.Coprime M),
    if p ∣ r then 0 else semiprimeSelbergWeight 3 r *
      (scalarSemiprimeTransform (scalarSievePrimeProduct M R) (scalarLinearY R) r -
        scalarSemiprimeTransform (scalarSievePrimeProduct M R) (scalarLinearY R) (p * r)) ^ 2

noncomputable def scalarCandidateSecondMain (M R : ℕ) (P Q : Finset ℕ) (x z : ℕ) : ℝ :=
  ∑ p ∈ P, (primeSlice Q p x z).card * scalarCandidatePrimeKernel M R p

theorem scalarCandidatePrimeKernel_eq_scalarKernel (M R p : ℕ) (hp : p.Prime)
    (s t : BoundingSieve) (hsP : s.prodPrimes = scalarSievePrimeProduct M R)
    (htP : t.prodPrimes = s.prodPrimes)
    (hs : ∀ q, q.Prime → q ∣ s.prodPrimes → s.nu q = (3 : ℝ) / q)
    (ht : ∀ q, q.Prime → q ∣ s.prodPrimes → t.nu q = (2 : ℝ) / ((q : ℝ) - 1)) :
    scalarCandidatePrimeKernel M R p =
      scalarPrimeRemovedKernel t p (scalarSelbergCoefficient s (scalarLinearY R)) := by
  rw [scalarSelberg_semiprime_kernel_diagonal_all_primes s t htP hs ht (scalarLinearY R) p hp,
    hsP]
  symm
  apply sum_scalarSievePrimeProduct_divisors_eq_fixed_modulus_sum
  intro r hr
  by_cases hpr : p ∣ r
  · exact if_pos hpr
  · rw [if_neg hpr,
      scalarSemiprimeTransform_eq_zero_of_radius (scalarSievePrimeProduct M R) R
        (scalarLinearY R) (scalarLinearY_eq_zero_of_radius R) r hr,
      scalarSemiprimeTransform_eq_zero_of_radius (scalarSievePrimeProduct M R) R
        (scalarLinearY R) (scalarLinearY_eq_zero_of_radius R) (p * r)
        (hr.trans (Nat.le_mul_of_pos_left r hp.pos))]
    simp only [sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero]

theorem scalarCandidateSecondMain_eq_kernel_sum (M R : ℕ) (P Q : Finset ℕ) (x z : ℕ)
    (hP : ∀ p ∈ P, p.Prime)
    (s t : BoundingSieve) (hsP : s.prodPrimes = scalarSievePrimeProduct M R)
    (htP : t.prodPrimes = s.prodPrimes)
    (hs : ∀ q, q.Prime → q ∣ s.prodPrimes → s.nu q = (3 : ℝ) / q)
    (ht : ∀ q, q.Prime → q ∣ s.prodPrimes → t.nu q = (2 : ℝ) / ((q : ℝ) - 1)) :
    scalarCandidateSecondMain M R P Q x z =
      ∑ p ∈ P, (primeSlice Q p x z).card *
        scalarPrimeRemovedKernel t p (scalarSelbergCoefficient s (scalarLinearY R)) := by
  unfold scalarCandidateSecondMain
  apply Finset.sum_congr rfl
  intro p hp
  rw [scalarCandidatePrimeKernel_eq_scalarKernel M R p (hP p hp) s t hsP htP hs ht]

end Erdos964
