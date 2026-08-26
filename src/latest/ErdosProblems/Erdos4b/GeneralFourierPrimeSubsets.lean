/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierPrimeChoices

/-!
# Squarefree divisor coordinates at a finite prime cutoff

Every divisor of a finite product of distinct primes is represented exactly
once by a prime subset. Its Möbius--Fourier weight factors prime by prime.
These are arithmetic identities, with no analytic convergence assumption.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem primeFinsetProduct_squarefree (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) : Squarefree (∏ p ∈ P, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro p hp q hq hpq
    change IsRelPrime p q
    rw [← Nat.coprime_iff_isRelPrime]
    exact (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq
  · exact fun p hp ↦ (hP p hp).squarefree

theorem primeFinsetProduct_pos (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) : 0 < ∏ p ∈ P, p :=
  Finset.prod_pos fun p hp ↦ (hP p hp).pos

theorem prime_dvd_primeFinsetProduct_iff (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {p : ℕ} (hp : p.Prime) :
    p ∣ ∏ q ∈ P, q ↔ p ∈ P := by
  calc
    _ ↔ p ∈ (∏ q ∈ P, q).primeFactors := by
      simp [Nat.mem_primeFactors, hp, (primeFinsetProduct_pos P hP).ne']
    _ ↔ _ := by rw [Nat.primeFactors_prod hP]

theorem primeFinsetProduct_injective_on_subsets (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) {S T : Finset ℕ}
    (hS : S ⊆ P) (hT : T ⊆ P)
    (hprod : (∏ p ∈ S, p) = ∏ p ∈ T, p) : S = T := by
  have h := congrArg Nat.primeFactors hprod
  simpa only [Nat.primeFactors_prod (fun p hp ↦ hP p (hS hp)),
    Nat.primeFactors_prod (fun p hp ↦ hP p (hT hp))] using h

theorem divisors_primeFinsetProduct_eq_image (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    (∏ p ∈ P, p).divisors = P.powerset.image (fun S ↦ ∏ p ∈ S, p) := by
  ext d
  constructor
  · intro hd
    have hdvd := Nat.dvd_of_mem_divisors hd
    have hsq := (primeFinsetProduct_squarefree P hP).squarefree_of_dvd hdvd
    refine Finset.mem_image.mpr ⟨d.primeFactors, ?_, Nat.prod_primeFactors_of_squarefree hsq⟩
    rw [Finset.mem_powerset]
    simpa only [Nat.primeFactors_prod hP] using
      Nat.primeFactors_mono hdvd (primeFinsetProduct_pos P hP).ne'
  · rintro hd
    obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hd
    exact Nat.mem_divisors.mpr
      ⟨Finset.prod_dvd_prod_of_subset _ _ id (Finset.mem_powerset.mp hS),
        (primeFinsetProduct_pos P hP).ne'⟩

def primeSubsetDivisorEquiv (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    P.powerset ≃ (∏ p ∈ P, p).divisors where
  toFun S := ⟨∏ p ∈ S.val, p, Nat.mem_divisors.mpr
    ⟨Finset.prod_dvd_prod_of_subset _ _ id (Finset.mem_powerset.mp S.property),
      (primeFinsetProduct_pos P hP).ne'⟩⟩
  invFun d := ⟨d.val.primeFactors, Finset.mem_powerset.mpr (by
    simpa only [Nat.primeFactors_prod hP] using
      Nat.primeFactors_mono (Nat.dvd_of_mem_divisors d.property)
        (primeFinsetProduct_pos P hP).ne')⟩
  left_inv S := by
    apply Subtype.ext
    exact Nat.primeFactors_prod fun p hp ↦ hP p (Finset.mem_powerset.mp S.property hp)
  right_inv d := by
    apply Subtype.ext
    exact Nat.prod_primeFactors_of_squarefree
      ((primeFinsetProduct_squarefree P hP).squarefree_of_dvd
        (Nat.dvd_of_mem_divisors d.property))

theorem sum_divisors_primeFinsetProduct {M : Type*} [AddCommMonoid M]
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (f : ℕ → M) :
    (∑ d ∈ (∏ p ∈ P, p).divisors, f d) =
      ∑ S ∈ P.powerset, f (∏ p ∈ S, p) := by
  rw [divisors_primeFinsetProduct_eq_image P hP]
  exact Finset.sum_image fun S hS T hT h ↦
    primeFinsetProduct_injective_on_subsets P hP
      (Finset.mem_powerset.mp hS) (Finset.mem_powerset.mp hT) h

theorem primeFourierPower_mul {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (s : ℂ) :
    primeFourierPower (a * b) s = primeFourierPower a s * primeFourierPower b s := by
  simp only [primeFourierPower, Real.log_mul ha.ne' hb.ne', Complex.ofReal_add,
    mul_add, neg_add, Complex.exp_add]

theorem primeFourierPower_prod {ι : Type*} (S : Finset ι)
    (f : ι → ℝ) (hf : ∀ i ∈ S, 0 < f i) (s : ℂ) :
    primeFourierPower (∏ i ∈ S, f i) s = ∏ i ∈ S, primeFourierPower (f i) s := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [primeFourierPower]
  | @insert a S ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        primeFourierPower_mul (hf a (Finset.mem_insert_self _ _))
          (Finset.prod_pos fun i hi ↦ hf i (Finset.mem_insert_of_mem hi)),
        ih (fun i hi ↦ hf i (Finset.mem_insert_of_mem hi))]

theorem moebius_primeFinsetProduct (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) :
    ArithmeticFunction.moebius (∏ p ∈ P, p) = ∏ _p ∈ P, (-1 : ℤ) := by
  rw [ArithmeticFunction.isMultiplicative_moebius.map_prod_of_prime P hP]
  exact Finset.prod_congr rfl fun p hp ↦ ArithmeticFunction.moebius_apply_prime (hP p hp)

theorem moebius_mul_primeFourierPower_product
    (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (s : ℂ) :
    (ArithmeticFunction.moebius (∏ p ∈ P, p) : ℂ) *
        primeFourierPower ((∏ p ∈ P, p : ℕ) : ℝ) s =
      ∏ p ∈ P, -primeFourierPower p s := by
  rw [moebius_primeFinsetProduct P hP]
  push_cast
  rw [primeFourierPower_prod P (fun p : ℕ ↦ (p : ℝ))
    (fun p hp ↦ by exact_mod_cast (hP p hp).pos)]
  rw [← Finset.prod_mul_distrib]
  simp

end

end Erdos4b
