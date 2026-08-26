import ErdosProblems.Erdos394.SymmetricTail
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Squarefree

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Algebra of products indexed by finite prime subsets
-/

open Nat Finset

namespace Erdos394

/-- Product of a finite set of natural numbers. -/
def primeProduct (T : Finset ℕ) : ℕ := ∏ p ∈ T, p

@[simp]
theorem primeProduct_empty : primeProduct ∅ = 1 := by simp [primeProduct]

@[simp]
theorem primeProduct_insert {p : ℕ} {T : Finset ℕ} (hpT : p ∉ T) :
    primeProduct (insert p T) = p * primeProduct T := by
  simp [primeProduct, hpT]

/-- Distinct primes give a squarefree product. -/
theorem squarefree_primeProduct (T : Finset ℕ)
    (hprime : ∀ p ∈ T, p.Prime) : Squarefree (primeProduct T) := by
  induction T using Finset.induction_on with
  | empty => simp [primeProduct, squarefree_one]
  | @insert p T hpT ih =>
      have hp : p.Prime := hprime p (Finset.mem_insert_self p T)
      have hTprime : ∀ q ∈ T, q.Prime := by
        intro q hq
        exact hprime q (Finset.mem_insert_of_mem hq)
      have hcop : p.Coprime (primeProduct T) := by
        rw [hp.coprime_iff_not_dvd]
        intro hdiv
        rw [primeProduct] at hdiv
        obtain ⟨q, hq, hpq⟩ :=
          (_root_.Prime.dvd_finsetProd_iff hp.prime (fun q : ℕ ↦ q)).mp hdiv
        have heq : p = q := (Nat.prime_dvd_prime_iff_eq hp (hTprime q hq)).mp hpq
        exact hpT (heq ▸ hq)
      rw [primeProduct_insert hpT, Nat.squarefree_mul_iff]
      exact ⟨hcop, hp.prime.squarefree, ih hTprime⟩

/-- If every prime in the set is different from two, its product is odd. -/
theorem odd_primeProduct (T : Finset ℕ)
    (hprime : ∀ p ∈ T, p.Prime) (hne2 : ∀ p ∈ T, p ≠ 2) :
    Odd (primeProduct T) := by
  induction T using Finset.induction_on with
  | empty => simp [primeProduct]
  | @insert p T hpT ih =>
      have hp : p.Prime := hprime p (Finset.mem_insert_self p T)
      have hpodd : Odd p := hp.odd_of_ne_two (hne2 p (Finset.mem_insert_self p T))
      have hTodd : Odd (primeProduct T) := ih
        (fun q hq ↦ hprime q (Finset.mem_insert_of_mem hq))
        (fun q hq ↦ hne2 q (Finset.mem_insert_of_mem hq))
      rw [primeProduct_insert hpT]
      exact hpodd.mul hTodd

/-- The prime factors of a finite prime product are exactly its indexing set. -/
theorem primeFactors_primeProduct (T : Finset ℕ)
    (hprime : ∀ p ∈ T, p.Prime) :
    (primeProduct T).primeFactors = T := by
  exact Nat.primeFactors_prod hprime

/-- Products distinguish finite sets of primes. -/
theorem primeProduct_injective_on_prime_sets {T U : Finset ℕ}
    (hT : ∀ p ∈ T, p.Prime) (hU : ∀ p ∈ U, p.Prime)
    (hprod : primeProduct T = primeProduct U) : T = U := by
  calc
    T = (primeProduct T).primeFactors := (primeFactors_primeProduct T hT).symm
    _ = (primeProduct U).primeFactors := by rw [hprod]
    _ = U := primeFactors_primeProduct U hU

/-- The product is at most `y` to the cardinality when every factor is at
most `y`. -/
theorem primeProduct_le_pow_card (T : Finset ℕ) {y : ℕ}
    (hTy : ∀ p ∈ T, p ≤ y) :
    primeProduct T ≤ y ^ T.card := by
  unfold primeProduct
  calc
    (∏ p ∈ T, p) ≤ ∏ _p ∈ T, y := by
      apply Finset.prod_le_prod
      · intro p hp
        omega
      · exact hTy
    _ = y ^ T.card := by simp

/-- Real Euler product formula for the totient of a finite prime product. -/
theorem totient_primeProduct_real (T : Finset ℕ)
    (hprime : ∀ p ∈ T, p.Prime) :
    ((primeProduct T).totient : ℝ) =
      (primeProduct T : ℝ) *
        localEulerProduct T (fun p ↦ 1 / (p : ℝ)) := by
  induction T using Finset.induction_on with
  | empty => simp [primeProduct, localEulerProduct, Nat.totient_one]
  | @insert p T hpT ih =>
      have hp : p.Prime := hprime p (Finset.mem_insert_self p T)
      have hTprime : ∀ q ∈ T, q.Prime := by
        intro q hq
        exact hprime q (Finset.mem_insert_of_mem hq)
      have hcop : p.Coprime (primeProduct T) := by
        rw [hp.coprime_iff_not_dvd]
        intro hdiv
        rw [primeProduct] at hdiv
        obtain ⟨q, hq, hpq⟩ :=
          (_root_.Prime.dvd_finsetProd_iff hp.prime (fun q : ℕ ↦ q)).mp hdiv
        exact hpT (((Nat.prime_dvd_prime_iff_eq hp (hTprime q hq)).mp hpq) ▸ hq)
      rw [primeProduct_insert hpT, Nat.totient_mul hcop, Nat.totient_prime hp]
      unfold localEulerProduct
      rw [Finset.prod_insert hpT]
      push_cast
      rw [Nat.cast_sub hp.one_le, ih hTprime]
      unfold localEulerProduct
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      field_simp
      ring

/-- Splitting a finite Euler product between a subset and its complement. -/
theorem localEulerProduct_mul_sdiff [DecidableEq α]
    (P T : Finset α) (hTP : T ⊆ P) (x : α → ℝ) :
    localEulerProduct T x * localEulerProduct (P \ T) x =
      localEulerProduct P x := by
  unfold localEulerProduct
  rw [← Finset.prod_union (Finset.disjoint_sdiff),
    Finset.union_sdiff_of_subset hTP]

/-- A local Euler product with weights in `[0,1]` is nonnegative. -/
theorem localEulerProduct_nonneg (P : Finset α) (x : α → ℝ)
    (hx0 : ∀ i ∈ P, 0 ≤ x i) (hx1 : ∀ i ∈ P, x i ≤ 1) :
    0 ≤ localEulerProduct P x := by
  unfold localEulerProduct
  apply Finset.prod_nonneg
  intro i hi
  exact sub_nonneg.mpr (hx1 i hi)

/-- A local Euler product with nonnegative weights is at most one. -/
theorem localEulerProduct_le_one (P : Finset α) (x : α → ℝ)
    (hx0 : ∀ i ∈ P, 0 ≤ x i) (hx1 : ∀ i ∈ P, x i ≤ 1) :
    localEulerProduct P x ≤ 1 := by
  unfold localEulerProduct
  calc
    (∏ i ∈ P, (1 - x i)) ≤ ∏ _i ∈ P, (1 : ℝ) := by
      apply Finset.prod_le_prod
      · intro i hi
        exact sub_nonneg.mpr (hx1 i hi)
      · intro i hi
        linarith [hx0 i hi]
    _ = 1 := by simp

/-- Removing factors in `[0,1]` can only increase a local Euler product. -/
theorem localEulerProduct_le_sdiff [DecidableEq α]
    (P T : Finset α) (hTP : T ⊆ P) (x : α → ℝ)
    (hx0 : ∀ i ∈ P, 0 ≤ x i) (hx1 : ∀ i ∈ P, x i ≤ 1) :
    localEulerProduct P x ≤ localEulerProduct (P \ T) x := by
  rw [← localEulerProduct_mul_sdiff P T hTP x]
  have hTle : localEulerProduct T x ≤ 1 :=
    localEulerProduct_le_one T x (fun i hi ↦ hx0 i (hTP hi))
      (fun i hi ↦ hx1 i (hTP hi))
  have hcomp0 : 0 ≤ localEulerProduct (P \ T) x :=
    localEulerProduct_nonneg (P \ T) x
      (fun i hi ↦ hx0 i (Finset.mem_sdiff.mp hi).1)
      (fun i hi ↦ hx1 i (Finset.mem_sdiff.mp hi).1)
  nlinarith

/-- The factorial-tail condition passes from a prime set to every complement
of a subset. -/
theorem factorial_tail_le_localEulerProduct_sdiff
    (P T : Finset ℕ) (hTP : T ⊆ P) (R : ℕ)
    (htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct P (fun p ↦ 1 / (p : ℝ)))
    (hprime : ∀ p ∈ P, p.Prime) :
      (∑ p ∈ P \ T, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
        localEulerProduct (P \ T) (fun p ↦ 1 / (p : ℝ)) := by
  have hx0 : ∀ p ∈ P, 0 ≤ (1 / (p : ℝ)) := by
    intro p hp
    positivity
  have hx1 : ∀ p ∈ P, (1 / (p : ℝ)) ≤ 1 := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
    exact (div_le_one hp0).2 (by exact_mod_cast (hprime p hp).one_le)
  have hsum : (∑ p ∈ P \ T, (1 / (p : ℝ))) ≤
      ∑ p ∈ P, (1 / (p : ℝ)) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
    intro p hp hnot
    positivity
  have hpow := pow_le_pow_left₀ (Finset.sum_nonneg fun p hp ↦ by positivity)
    hsum (R + 1)
  have hdiv :
      (∑ p ∈ P \ T, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) :=
    div_le_div_of_nonneg_right hpow (by positivity)
  exact hdiv.trans <| htail.trans <|
    localEulerProduct_le_sdiff P T hTP _ hx0 hx1

/-- Exact subset expansion of `∏(1+x_i)`. -/
theorem sum_powerset_prod_eq_prod_one_add [DecidableEq α]
    (P : Finset α) (x : α → ℝ) :
    (∑ T ∈ P.powerset, ∏ i ∈ T, x i) = ∏ i ∈ P, (1 + x i) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert a P ha ih =>
      have hinj : Set.InjOn (insert a) (↑P.powerset : Set (Finset α)) := by
        intro U hU V hV huv
        have hUa : a ∉ U := fun h ↦ ha (Finset.mem_powerset.mp hU h)
        have hVa : a ∉ V := fun h ↦ ha (Finset.mem_powerset.mp hV h)
        calc
          U = (insert a U).erase a := (Finset.erase_insert hUa).symm
          _ = (insert a V).erase a := by rw [huv]
          _ = V := Finset.erase_insert hVa
      have hdisj : Disjoint P.powerset (P.powerset.image (insert a)) := by
        rw [Finset.disjoint_left]
        intro U hUP hUimg
        obtain ⟨V, hVP, hVU⟩ := Finset.mem_image.mp hUimg
        have haU : a ∈ U := hVU ▸ Finset.mem_insert_self a V
        exact ha (Finset.mem_powerset.mp hUP haU)
      rw [Finset.powerset_insert P a, Finset.sum_union hdisj,
        Finset.sum_image hinj, Finset.prod_insert ha]
      have himage : (∑ U ∈ P.powerset, ∏ i ∈ insert a U, x i) =
          x a * (∑ U ∈ P.powerset, ∏ i ∈ U, x i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro U hU
        rw [Finset.prod_insert]
        exact fun haU ↦ ha (Finset.mem_powerset.mp hU haU)
      rw [himage, ih]
      ring

/-- Prime subsets whose product is at most `Q`. -/
def smallPrimeSubsets (P : Finset ℕ) (Q : ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter (fun T ↦ primeProduct T ≤ Q)

/-- There are at most `Q+1` prime subsets with product at most `Q`. -/
theorem card_smallPrimeSubsets_le
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (Q : ℕ) :
    (smallPrimeSubsets P Q).card ≤ Q + 1 := by
  have hcard := Finset.card_le_card_of_injOn
    (s := smallPrimeSubsets P Q) (t := Finset.range (Q + 1)) primeProduct
    (by
      intro T hT
      exact Finset.mem_range.mpr <| Nat.lt_succ_iff.mpr
        (Finset.mem_filter.mp hT).2)
    (by
      intro T hT U hU hprod
      have hTP := Finset.mem_powerset.mp (Finset.mem_filter.mp hT).1
      have hUP := Finset.mem_powerset.mp (Finset.mem_filter.mp hU).1
      exact primeProduct_injective_on_prime_sets
        (fun p hp ↦ hprime p (hTP hp))
        (fun p hp ↦ hprime p (hUP hp)) hprod)
  simpa using hcard

/-- A half-reciprocal product is the reciprocal of the prime product times
`2^|T|`. -/
theorem prod_half_prime_eq (T : Finset ℕ)
    (hprime : ∀ p ∈ T, p.Prime) :
    (∏ p ∈ T, (1 / (2 * (p : ℝ)))) =
      1 / ((primeProduct T : ℝ) * ((2 ^ T.card : ℕ) : ℝ)) := by
  induction T using Finset.induction_on with
  | empty => simp [primeProduct]
  | @insert p T hpT ih =>
      have hp : p.Prime := hprime p (Finset.mem_insert_self p T)
      have hTprime : ∀ r ∈ T, r.Prime := by
        intro r hr
        exact hprime r (Finset.mem_insert_of_mem hr)
      rw [Finset.prod_insert hpT, ih hTprime, primeProduct_insert hpT,
        Finset.card_insert_of_notMem hpT, pow_succ]
      have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
      have hqR : (primeProduct T : ℝ) ≠ 0 := by
        exact_mod_cast (Finset.prod_ne_zero_iff.mpr
          (fun r hr ↦ (hTprime r hr).ne_zero))
      push_cast
      field_simp

/-- Exact root-count subset Euler expansion. -/
theorem sum_powerset_half_prime_products
    (P : Finset ℕ) :
    (∑ T ∈ P.powerset, ∏ p ∈ T, (1 / (2 * (p : ℝ)))) =
      ∏ p ∈ P, (1 + 1 / (2 * (p : ℝ))) :=
  sum_powerset_prod_eq_prod_one_add P (fun p ↦ 1 / (2 * (p : ℝ)))

/-- Crude aggregate totient bound over product-truncated prime subsets. -/
theorem sum_smallPrimeSubsets_totient_div_pow_le
    (P : Finset ℕ) (hprime : ∀ p ∈ P, p.Prime) (Q : ℕ) :
    (∑ T ∈ smallPrimeSubsets P Q,
      ((primeProduct T).totient : ℝ) / ((2 ^ T.card : ℕ) : ℝ)) ≤
      (Q : ℝ) * (Q + 1 : ℕ) := by
  have hterm : ∀ T ∈ smallPrimeSubsets P Q,
      ((primeProduct T).totient : ℝ) / ((2 ^ T.card : ℕ) : ℝ) ≤
        (Q : ℝ) := by
    intro T hT
    have hqQ : primeProduct T ≤ Q := (Finset.mem_filter.mp hT).2
    have hphi : (primeProduct T).totient ≤ primeProduct T := Nat.totient_le _
    have hden : (1 : ℝ) ≤ ((2 ^ T.card : ℕ) : ℝ) := by
      exact_mod_cast Nat.one_le_pow T.card 2 (by norm_num)
    have hnonneg : (0 : ℝ) ≤ (primeProduct T).totient := by positivity
    calc
      ((primeProduct T).totient : ℝ) / ((2 ^ T.card : ℕ) : ℝ) ≤
          ((primeProduct T).totient : ℝ) :=
        (div_le_iff₀ (by positivity)).2 (by nlinarith)
      _ ≤ (primeProduct T : ℝ) := by exact_mod_cast hphi
      _ ≤ (Q : ℝ) := by exact_mod_cast hqQ
  calc
    (∑ T ∈ smallPrimeSubsets P Q,
      ((primeProduct T).totient : ℝ) / ((2 ^ T.card : ℕ) : ℝ)) ≤
        ∑ _T ∈ smallPrimeSubsets P Q, (Q : ℝ) :=
      Finset.sum_le_sum hterm
    _ = (Q : ℝ) * (smallPrimeSubsets P Q).card := by simp [mul_comm]
    _ ≤ (Q : ℝ) * (Q + 1 : ℕ) := by
      gcongr
      exact_mod_cast card_smallPrimeSubsets_le P hprime Q

end Erdos394
