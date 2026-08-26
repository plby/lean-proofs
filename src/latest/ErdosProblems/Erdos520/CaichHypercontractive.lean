import ErdosProblems.Erdos520.BonamiModel
import ErdosProblems.Erdos520.CaichDivisorBounds

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory
open scoped ArithmeticFunction.zeta BigOperators ENNReal

namespace Erdos
namespace Problem520

/-!
# Hypercontractive moments for finite Rademacher multiplicative sums

This file joins the coefficient-weighted Bonami inequality already proved for
the finite Boolean cube to the generalized divisor bound in
`CaichDivisorBounds`.  It supplies the precise finite-short-sum estimate used
in Caich's bounds for `W`, `lambda^(2)`, and `lambda^(3)`.
-/

open ArithmeticFunction

/-! ## The Bonami weight is the generalized divisor function -/

/-- Every Dirichlet-convolution power of zeta is multiplicative. -/
theorem orderedDivisorCount_isMultiplicative (m : ℕ) :
    IsMultiplicative (ζ ^ m : ArithmeticFunction ℕ) := by
  induction m with
  | zero =>
      simpa only [pow_zero] using!
        (isMultiplicative_one : IsMultiplicative (1 : ArithmeticFunction ℕ))
  | succ m ih =>
      rw [pow_succ]
      exact ih.mul isMultiplicative_zeta

/-- On a prime, the ordered `m`-fold divisor function has value `m`. -/
theorem orderedDivisorCount_prime (m : ℕ) {p : ℕ} (hp : p.Prime) :
    orderedDivisorCount m p = m := by
  induction m with
  | zero =>
      simp [orderedDivisorCount, hp.ne_one]
  | succ m ih =>
      rw [orderedDivisorCount_succ, hp.divisors]
      have hone : orderedDivisorCount m 1 = 1 :=
        (orderedDivisorCount_isMultiplicative m).map_one
      rw [Finset.sum_insert (by simpa using! hp.ne_one.symm)]
      simp [hone, ih]
      omega

/-- For a product of distinct primes, the generalized divisor weight is
exactly the Bonami degree weight. -/
theorem orderedDivisorCount_freshProduct (m : ℕ) {S : Finset ℕ}
    (hS : ∀ p ∈ S, p.Prime) :
    orderedDivisorCount m (freshProduct S) = m ^ S.card := by
  change (ζ ^ m : ArithmeticFunction ℕ) (∏ p ∈ S, p) = m ^ S.card
  rw [(orderedDivisorCount_isMultiplicative m).map_prod_of_prime S hS]
  calc
    (∏ p ∈ S, (ζ ^ m : ArithmeticFunction ℕ) p) =
        ∏ p ∈ S, m := by
      apply Finset.prod_congr rfl
      intro p hp
      simpa only [orderedDivisorCount] using!
        orderedDivisorCount_prime m (hS p hp)
    _ = m ^ S.card := by simp

/-- Equivalent squarefree-integer form of the preceding identity. -/
theorem orderedDivisorCount_eq_pow_card_primeFactors_of_squarefree
    (m : ℕ) {n : ℕ} (hn : Squarefree n) :
    orderedDivisorCount m n = m ^ n.primeFactors.card := by
  have hprime : ∀ p ∈ n.primeFactors, p.Prime :=
    fun p hp => Nat.prime_of_mem_primeFactors hp
  calc
    orderedDivisorCount m n =
        orderedDivisorCount m (freshProduct n.primeFactors) := by
      rw [freshProduct, Nat.prod_primeFactors_of_squarefree hn]
    _ = m ^ n.primeFactors.card :=
      orderedDivisorCount_freshProduct m hprime

/-! ## Duplicate-free encoding of a finite integer support -/

/-- Squarefree members of `s`, represented by their sets of prime factors
inside the ambient range up to `x`. -/
def caichSquarefreeEncoding (x : ℕ) (s : Finset ℕ) : Finset (Finset ℕ) :=
  ((x + 1).primesBelow.powerset).filter fun S => freshProduct S ∈ s

/-- Reindexing a squarefree integer sum by its unique prime-factor set. -/
theorem sum_squarefree_filter_eq_sum_caichSquarefreeEncoding
    (x : ℕ) (s : Finset ℕ) (F : ℕ → ℝ)
    (hs : s ⊆ Finset.Ioc 0 x) :
    (∑ n ∈ s.filter Squarefree, F n) =
      ∑ S ∈ caichSquarefreeEncoding x s, F (freshProduct S) := by
  classical
  exact Finset.sum_bij
    (fun n _hn => n.primeFactors)
    (fun n hn => by
      rw [Finset.mem_filter] at hn
      rw [caichSquarefreeEncoding, Finset.mem_filter, Finset.mem_powerset]
      have hnx := Finset.mem_Ioc.mp (hs hn.1)
      constructor
      · intro p hp
        rw [Nat.mem_primesBelow]
        exact ⟨by
          have hpn : p ≤ n := Nat.le_of_dvd hnx.1 (Nat.dvd_of_mem_primeFactors hp)
          omega, Nat.prime_of_mem_primeFactors hp⟩
      · simpa [freshProduct, Nat.prod_primeFactors_of_squarefree hn.2] using! hn.1)
    (fun n₁ hn₁ n₂ hn₂ heq => by
      rw [Finset.mem_filter] at hn₁ hn₂
      calc
        n₁ = freshProduct n₁.primeFactors := by
          rw [freshProduct, Nat.prod_primeFactors_of_squarefree hn₁.2]
        _ = freshProduct n₂.primeFactors := congrArg freshProduct heq
        _ = n₂ := by
          rw [freshProduct, Nat.prod_primeFactors_of_squarefree hn₂.2])
    (fun S hS => by
      rw [caichSquarefreeEncoding, Finset.mem_filter,
        Finset.mem_powerset] at hS
      have hprime : ∀ p ∈ S, p.Prime :=
        fun p hp => Nat.prime_of_mem_primesBelow (hS.1 hp)
      refine ⟨freshProduct S, ?_, freshProduct_primeFactors hprime⟩
      rw [Finset.mem_filter]
      exact ⟨hS.2, freshProduct_squarefree hprime⟩)
    (fun n hn => by
      apply congrArg F
      rw [Finset.mem_filter] at hn
      rw [freshProduct, Nat.prod_primeFactors_of_squarefree hn.2])

/-! ## The finite integer sum as a Walsh polynomial -/

/-- A finite weighted sum of the Rademacher multiplicative function. -/
noncomputable def caichFiniteRMFSum
    (s : Finset ℕ) (a : ℕ → ℝ) (omega : Omega) : ℝ :=
  ∑ n ∈ s, a n * f omega n

/-- Walsh coefficient attached to the squarefree integer represented by a
prime subset. -/
noncomputable def caichIntegerWalshCoefficient
    (s : Finset ℕ) (a : ℕ → ℝ) (S : Finset ℕ) : ℝ :=
  if freshProduct S ∈ s then a (freshProduct S) else 0

/-- The corresponding polynomial on the finite cube of primes at most `x`. -/
noncomputable def caichIntegerWalshEval
    (x : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (eta : (x + 1).primesBelow → Bool) : ℝ :=
  powersetWalshEval (x + 1).primesBelow
    (caichIntegerWalshCoefficient s a) eta

/-- Nonsquarefree terms may be removed because the Rademacher model vanishes
on them. -/
theorem caichFiniteRMFSum_eq_sum_squarefree
    (s : Finset ℕ) (a : ℕ → ℝ) (omega : Omega) :
    caichFiniteRMFSum s a omega =
      ∑ n ∈ s.filter Squarefree, a n * f omega n := by
  unfold caichFiniteRMFSum
  symm
  apply Finset.sum_filter_of_ne
  intro n hn hne
  by_contra hsq
  exact hne (by simp [f_eq_zero_of_not_squarefree omega hsq])

/-- Restricting a global sign configuration to the relevant prime
coordinates evaluates exactly the original integer sum. -/
theorem caichIntegerWalshEval_restrict
    (x : ℕ) (s : Finset ℕ) (a : ℕ → ℝ) (omega : Omega)
    (hs : s ⊆ Finset.Ioc 0 x) :
    caichIntegerWalshEval x s a ((x + 1).primesBelow.restrict omega) =
      caichFiniteRMFSum s a omega := by
  classical
  let P : Finset ℕ := (x + 1).primesBelow
  calc
    caichIntegerWalshEval x s a ((x + 1).primesBelow.restrict omega) =
        ∑ S ∈ P.powerset,
          (if freshProduct S ∈ s then a (freshProduct S) else 0) *
            freshCharacter omega S := by
      unfold caichIntegerWalshEval powersetWalshEval
      change (∑ S ∈ P.powerset,
        caichIntegerWalshCoefficient s a S *
          finsetFiberCharacter P (P.restrict omega) S) = _
      apply Finset.sum_congr rfl
      intro S hS
      rw [finsetFiberCharacter_restrict (Finset.mem_powerset.mp hS)]
      rfl
    _ = ∑ S ∈ P.powerset,
          if freshProduct S ∈ s then
            a (freshProduct S) * freshCharacter omega S else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hmem : freshProduct S ∈ s <;>
        simp [hmem]
    _ = ∑ S ∈ caichSquarefreeEncoding x s,
          a (freshProduct S) * freshCharacter omega S := by
      unfold caichSquarefreeEncoding
      rw [Finset.sum_filter]
    _ = ∑ S ∈ caichSquarefreeEncoding x s,
          a (freshProduct S) * f omega (freshProduct S) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [caichSquarefreeEncoding, Finset.mem_filter,
        Finset.mem_powerset] at hS
      have hprime : ∀ p ∈ S, p.Prime :=
        fun p hp => Nat.prime_of_mem_primesBelow (hS.1 hp)
      rw [f_freshProduct omega hprime]
    _ = ∑ n ∈ s.filter Squarefree, a n * f omega n :=
      (sum_squarefree_filter_eq_sum_caichSquarefreeEncoding
        x s (fun n => a n * f omega n) hs).symm
    _ = caichFiniteRMFSum s a omega :=
      (caichFiniteRMFSum_eq_sum_squarefree s a omega).symm

/-! ## Coefficient energy and hypercontractivity -/

/-- Bonami's coefficient energy for the integer-indexed Walsh polynomial. -/
noncomputable def caichIntegerWalshEnergy
    (r x : ℕ) (s : Finset ℕ) (a : ℕ → ℝ) : ℝ :=
  powersetWalshEnergy r (x + 1).primesBelow
    (caichIntegerWalshCoefficient s a)

/-- Exact reindexing of the Walsh coefficient energy by squarefree integers. -/
theorem caichIntegerWalshEnergy_eq_sum_squarefree
    (r x : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : s ⊆ Finset.Ioc 0 x) :
    caichIntegerWalshEnergy r x s a =
      ∑ n ∈ s.filter Squarefree,
        (((2 * r - 1 : ℕ) : ℝ) ^ n.primeFactors.card) * a n ^ 2 := by
  classical
  let P : Finset ℕ := (x + 1).primesBelow
  calc
    caichIntegerWalshEnergy r x s a =
        ∑ S ∈ P.powerset,
          if freshProduct S ∈ s then
            (((2 * r - 1 : ℕ) : ℝ) ^ S.card) *
              a (freshProduct S) ^ 2 else 0 := by
      unfold caichIntegerWalshEnergy powersetWalshEnergy
      change (∑ S ∈ P.powerset,
        (((2 * r - 1 : ℕ) : ℝ) ^ S.card) *
          caichIntegerWalshCoefficient s a S ^ 2) = _
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hmem : freshProduct S ∈ s
      · rw [show caichIntegerWalshCoefficient s a S = a (freshProduct S) by
          simp [caichIntegerWalshCoefficient, hmem]]
        rw [if_pos hmem]
      · rw [show caichIntegerWalshCoefficient s a S = 0 by
          simp [caichIntegerWalshCoefficient, hmem]]
        rw [if_neg hmem]
        simp
    _ = ∑ S ∈ caichSquarefreeEncoding x s,
          (((2 * r - 1 : ℕ) : ℝ) ^ S.card) *
            a (freshProduct S) ^ 2 := by
      unfold caichSquarefreeEncoding
      rw [Finset.sum_filter]
    _ = ∑ S ∈ caichSquarefreeEncoding x s,
          (((2 * r - 1 : ℕ) : ℝ) ^
            (freshProduct S).primeFactors.card) *
              a (freshProduct S) ^ 2 := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [caichSquarefreeEncoding, Finset.mem_filter,
        Finset.mem_powerset] at hS
      have hprime : ∀ p ∈ S, p.Prime :=
        fun p hp => Nat.prime_of_mem_primesBelow (hS.1 hp)
      rw [freshProduct_primeFactors hprime]
    _ = ∑ n ∈ s.filter Squarefree,
          (((2 * r - 1 : ℕ) : ℝ) ^ n.primeFactors.card) * a n ^ 2 :=
      (sum_squarefree_filter_eq_sum_caichSquarefreeEncoding x s
        (fun n => (((2 * r - 1 : ℕ) : ℝ) ^ n.primeFactors.card) * a n ^ 2)
        hs).symm

/-- On squarefree support, the Bonami energy is exactly weighted by the
ordered divisor function `tau_(2r-1)`. -/
theorem caichIntegerWalshEnergy_eq_divisorWeight
    (r x : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : s ⊆ Finset.Ioc 0 x) :
    caichIntegerWalshEnergy r x s a =
      ∑ n ∈ s.filter Squarefree,
        (orderedDivisorCount (2 * r - 1) n : ℝ) * a n ^ 2 := by
  rw [caichIntegerWalshEnergy_eq_sum_squarefree r x s a hs]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mem_filter] at hn
  congr 1
  exact_mod_cast
    (orderedDivisorCount_eq_pow_card_primeFactors_of_squarefree
      (2 * r - 1) hn.2).symm

/-- Dropping the squarefree restriction only enlarges the nonnegative
divisor-weighted energy. -/
theorem caichIntegerWalshEnergy_le_divisorWeight
    (r x : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : s ⊆ Finset.Ioc 0 x) :
    caichIntegerWalshEnergy r x s a ≤
      ∑ n ∈ s, (orderedDivisorCount (2 * r - 1) n : ℝ) * a n ^ 2 := by
  rw [caichIntegerWalshEnergy_eq_divisorWeight r x s a hs]
  apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
  intro n hn hnot
  positivity

/-- Finite-product-space Bonami inequality for the encoded integer sum. -/
theorem caichIntegerWalshEval_bonami_integral
    (r : ℕ) (hr : 1 ≤ r) (x : ℕ) (s : Finset ℕ) (a : ℕ → ℝ) :
    (∫ eta, |caichIntegerWalshEval x s a eta| ^ (2 * r)
        ∂Measure.pi (fun _ : (x + 1).primesBelow => coin)) ^
          (1 / (r : ℝ)) ≤ caichIntegerWalshEnergy r x s a := by
  rw [integral_coin_eq_fintypeAverage]
  exact powerset_bonami r hr (x + 1).primesBelow
    (caichIntegerWalshCoefficient s a)

/-- Global-product-space Bonami inequality for a finite weighted
Rademacher-multiplicative sum. -/
theorem caichFiniteRMFSum_bonami_energy
    (r : ℕ) (hr : 1 ≤ r) (x : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : s ⊆ Finset.Ioc 0 x) :
    (∫ omega, |caichFiniteRMFSum s a omega| ^ (2 * r) ∂μ) ^
        (1 / (r : ℝ)) ≤ caichIntegerWalshEnergy r x s a := by
  let P : Finset ℕ := (x + 1).primesBelow
  let g : (P → Bool) → ℝ := fun eta =>
    |caichIntegerWalshEval x s a eta| ^ (2 * r)
  have hg : AEStronglyMeasurable g (Measure.pi (fun _ : P => coin)) :=
    (measurable_of_finite g).aestronglyMeasurable
  have hrestrict :
      (∫ omega, g (P.restrict omega) ∂μ) =
        ∫ eta, g eta ∂Measure.pi (fun _ : P => coin) := by
    simpa only [μ] using!
      (integral_restrict_infinitePi (μ := fun _ : ℕ => coin) hg)
  have heq :
      (∫ omega, |caichFiniteRMFSum s a omega| ^ (2 * r) ∂μ) =
        ∫ omega, g (P.restrict omega) ∂μ := by
    apply integral_congr_ae
    exact ae_of_all μ fun omega => by
      unfold g P
      change |caichFiniteRMFSum s a omega| ^ (2 * r) =
        |caichIntegerWalshEval x s a
          ((x + 1).primesBelow.restrict omega)| ^ (2 * r)
      rw [caichIntegerWalshEval_restrict x s a omega hs]
  rw [heq, hrestrict]
  exact caichIntegerWalshEval_bonami_integral r hr x s a

/-- Hypercontractivity in the exact generalized-divisor form quoted by
Caich: the `L^(2r)` norm squared is bounded by the `tau_(2r-1)` coefficient
energy. -/
theorem caichFiniteRMFSum_hypercontractive
    (r : ℕ) (hr : 1 ≤ r) (x : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (hs : s ⊆ Finset.Ioc 0 x) :
    (∫ omega, |caichFiniteRMFSum s a omega| ^ (2 * r) ∂μ) ^
        (1 / (r : ℝ)) ≤
      ∑ n ∈ s, (orderedDivisorCount (2 * r - 1) n : ℝ) * a n ^ 2 :=
  (caichFiniteRMFSum_bonami_energy r hr x s a hs).trans
    (caichIntegerWalshEnergy_le_divisorWeight r x s a hs)

@[simp]
theorem caichFiniteRMFSum_one
    (s : Finset ℕ) (omega : Omega) :
    caichFiniteRMFSum s (fun _ => 1) omega = ∑ n ∈ s, f omega n := by
  simp [caichFiniteRMFSum]

/-- Combining finite-sum hypercontractivity with the elementary generalized
divisor estimate gives Caich's explicit short-sum moment budget. -/
theorem caichFiniteRMFSum_one_hypercontractive_divisorBound
    (r : ℕ) (hr : 1 ≤ r) (x : ℕ) (s : Finset ℕ)
    (hx : 3 ≤ x) (hs : s ⊆ Finset.Ioc 0 x) :
    (∫ omega, |∑ n ∈ s, f omega n| ^ (2 * r) ∂μ) ^
        (1 / (r : ℝ)) ≤
      (x : ℝ) * (2 * Real.log (x : ℝ)) ^ (2 * r - 2) := by
  have hm : 1 ≤ 2 * r - 1 := by omega
  have hhyper := caichFiniteRMFSum_hypercontractive
    r hr x s (fun _ => 1) hs
  simp only [caichFiniteRMFSum_one, one_pow, mul_one] at hhyper
  have hcast :
      (∑ n ∈ s, (orderedDivisorCount (2 * r - 1) n : ℝ)) =
        ((∑ n ∈ s, orderedDivisorCount (2 * r - 1) n : ℕ) : ℝ) := by
    norm_cast
  rw [hcast] at hhyper
  exact hhyper.trans (by
    simpa only [show (2 * r - 1) - 1 = 2 * r - 2 by omega] using!
      sum_orderedDivisorCount_le_two_log
        (2 * r - 1) x s hm hx hs)

/-- Raw `2r`-th-moment version of the preceding root-moment estimate. -/
theorem integral_caichFiniteRMFSum_one_pow_le
    (r : ℕ) (hr : 1 ≤ r) (x : ℕ) (s : Finset ℕ)
    (hx : 3 ≤ x) (hs : s ⊆ Finset.Ioc 0 x) :
    (∫ omega, |∑ n ∈ s, f omega n| ^ (2 * r) ∂μ) ≤
      ((x : ℝ) * (2 * Real.log (x : ℝ)) ^ (2 * r - 2)) ^ r := by
  let I : ℝ := ∫ omega, |∑ n ∈ s, f omega n| ^ (2 * r) ∂μ
  let B : ℝ := (x : ℝ) * (2 * Real.log (x : ℝ)) ^ (2 * r - 2)
  have hI : 0 ≤ I := integral_nonneg fun omega => by positivity
  have hroot : I ^ (1 / (r : ℝ)) ≤ B := by
    simpa only [I, B] using!
      caichFiniteRMFSum_one_hypercontractive_divisorBound r hr x s hx hs
  have hpow := pow_le_pow_left₀ (Real.rpow_nonneg hI _) hroot r
  have hr0 : r ≠ 0 := by omega
  simpa only [I, B, one_div, Real.rpow_inv_natCast_pow hI hr0] using! hpow

end Problem520
end Erdos
