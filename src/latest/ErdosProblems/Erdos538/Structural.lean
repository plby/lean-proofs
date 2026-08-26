import ErdosProblems.Erdos538.Problem538

/- Ported from Lean 4.31.0 to 4.33.0; imports, namespaces, and elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos538

open ArithmeticFunction

/-- Multiplication by one prime raises the total prime-factor count by one. -/
theorem cardFactors_prime_mul {p a : ℕ} (hp : p.Prime) (ha : a ≠ 0) :
    cardFactors (p * a) = cardFactors a + 1 := by
  rw [cardFactors_mul hp.ne_zero ha, cardFactors_apply_prime hp]
  omega

/-- Every predecessor `a` occurring in a representation of the same `m` lies
in the single `Ω = Ω(m)-1` layer. -/
theorem representation_cardFactors {A : Finset ℕ} {m p a : ℕ}
    (hpos : ∀ x ∈ A, 1 ≤ x)
    (hpa : (p, a) ∈ representations A m) :
    cardFactors m = cardFactors a + 1 := by
  rcases Finset.mem_filter.mp hpa with ⟨hprod, hp, hm⟩
  have haA : a ∈ A := (Finset.mem_product.mp hprod).2
  have ha0 : a ≠ 0 := by
    have := hpos a haA
    omega
  rw [hm]
  exact cardFactors_prime_mul hp ha0

/-- In particular, any two members represented at one `m` have equal total
prime-factor count. -/
theorem representations_same_cardFactors {A : Finset ℕ} {m p q a b : ℕ}
    (hpos : ∀ x ∈ A, 1 ≤ x)
    (hpa : (p, a) ∈ representations A m)
    (hqb : (q, b) ∈ representations A m) :
    cardFactors a = cardFactors b := by
  have ha := representation_cardFactors hpos hpa
  have hb := representation_cardFactors hpos hqb
  omega

/-- Distinct solution pairs for a fixed `m` necessarily use distinct primes. -/
theorem representation_prime_injective {A : Finset ℕ} {m p q a b : ℕ}
    (hpa : (p, a) ∈ representations A m)
    (hqb : (q, b) ∈ representations A m)
    (hpq : p = q) : a = b := by
  rcases Finset.mem_filter.mp hpa with ⟨_, hp, hmpa⟩
  rcases Finset.mem_filter.mp hqb with ⟨_, _, hmqb⟩
  subst q
  have hmul : p * a = p * b := hmpa.symm.trans hmqb
  exact Nat.eq_of_mul_eq_mul_left hp.pos hmul

/-- The number of representation pairs at `m` is no larger than the number of
distinct prime factors of `m`. -/
theorem representations_card_le_primeFactors {A : Finset ℕ} {m : ℕ}
    (hpos : ∀ x ∈ A, 1 ≤ x) :
    (representations A m).card ≤ m.primeFactors.card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro pa hpa
    rcases Finset.mem_filter.mp hpa with ⟨hprod, hp, hm⟩
    have haA : pa.2 ∈ A := (Finset.mem_product.mp hprod).2
    have ha0 : pa.2 ≠ 0 := by
      have := hpos pa.2 haA
      omega
    apply hp.mem_primeFactors
    · exact ⟨pa.2, hm⟩
    · rw [hm]
      exact Nat.mul_ne_zero hp.ne_zero ha0
  · intro pa hpa qb hqb hpq
    apply Prod.ext hpq
    exact representation_prime_injective hpa hqb hpq

/-- Hence a representation edge has size at most `Ω(m)`. -/
theorem representations_card_le_cardFactors {A : Finset ℕ} {m : ℕ}
    (hpos : ∀ x ∈ A, 1 ≤ x) :
    (representations A m).card ≤ cardFactors m := by
  calc
    (representations A m).card ≤ m.primeFactors.card :=
      representations_card_le_primeFactors hpos
    _ = m.primeFactorsList.dedup.length := by
      rw [← Nat.toFinset_factors, List.card_toFinset]
    _ ≤ m.primeFactorsList.length :=
      (List.dedup_sublist m.primeFactorsList).length_le
    _ = cardFactors m := cardFactors_apply.symm

/-- Prime divisors `p` of `m` whose complementary quotient `m/p` lies in `A`. -/
def quotientPrimes (A : Finset ℕ) (m : ℕ) : Finset ℕ :=
  m.primeFactors.filter (fun p => m / p ∈ A)

/-- For positive candidate sets, counting solution pairs is exactly the same as
counting their prime quotient coordinates. -/
theorem representations_card_eq_quotientPrimes {A : Finset ℕ} {m : ℕ} :
    (representations A m).card = (quotientPrimes A m).card := by
  by_cases hm : m = 0
  · subst m
    simp [representations, quotientPrimes]
    exact fun _ _ => Nat.not_prime_zero
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hinj : Set.InjOn Prod.fst (representations A m : Set (ℕ × ℕ)) := by
      intro pa hpa qb hqb hpq
      apply Prod.ext hpq
      exact representation_prime_injective hpa hqb hpq
    rw [← Finset.card_image_of_injOn hinj]
    congr 1
    ext p
    constructor
    · intro hpImage
      rcases Finset.mem_image.mp hpImage with ⟨pa, hpa, hp⟩
      rcases Finset.mem_filter.mp hpa with ⟨hprod, hprime, hmul⟩
      have haA : pa.2 ∈ A := (Finset.mem_product.mp hprod).2
      have hdiv : m / pa.1 = pa.2 := by
        rw [hmul]
        simpa [Nat.mul_comm] using Nat.mul_div_left pa.2 hprime.pos
      apply Finset.mem_filter.mpr
      subst p
      exact ⟨hprime.mem_primeFactors ⟨pa.2, hmul⟩ hm, hdiv ▸ haA⟩
    · intro hpFilter
      rcases Finset.mem_filter.mp hpFilter with ⟨hpFactor, hquotA⟩
      have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hpFactor
      have hpdvd : p ∣ m := Nat.dvd_of_mem_primeFactors hpFactor
      apply Finset.mem_image.mpr
      refine ⟨(p, m / p), ?_, rfl⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_product.mpr
          ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_dvd hmpos hpdvd)), hquotA⟩,
        hpprime, (Nat.mul_div_cancel' hpdvd).symm⟩

/-- The part of `A` in the exact `Ω=k` layer. -/
def omegaSlice (A : Finset ℕ) (k : ℕ) : Finset ℕ :=
  A.filter (fun a => cardFactors a = k)

/-- Admissibility can be checked independently in every Omega layer. -/
theorem admissible_of_omegaSlices {A : Finset ℕ} {r N : ℕ}
    (hrange : ∀ a ∈ A, 1 ≤ a ∧ a ≤ N)
    (hslices : ∀ k m : ℕ, (representations (omegaSlice A k) m).card ≤ r) :
    Admissible r N A := by
  refine ⟨hrange, ?_⟩
  intro m
  by_cases hempty : representations A m = ∅
  · simp [hempty]
  · have hne : (representations A m).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hempty
    rcases hne with ⟨pa, hpa⟩
    let k := cardFactors pa.2
    have hpos : ∀ x ∈ A, 1 ≤ x := fun x hx => (hrange x hx).1
    have heq : representations A m = representations (omegaSlice A k) m := by
      ext qa
      constructor
      · intro hqa
        rcases Finset.mem_filter.mp hqa with ⟨hprod, hprime, hmul⟩
        have hqA : qa.2 ∈ A := (Finset.mem_product.mp hprod).2
        have homega : cardFactors qa.2 = k := by
          exact representations_same_cardFactors hpos hqa hpa
        apply Finset.mem_filter.mpr
        constructor
        · apply Finset.mem_product.mpr
          exact ⟨(Finset.mem_product.mp hprod).1,
            Finset.mem_filter.mpr ⟨hqA, homega⟩⟩
        · exact ⟨hprime, hmul⟩
      · intro hqa
        rcases Finset.mem_filter.mp hqa with ⟨hprod, hprime, hmul⟩
        have hqSlice : qa.2 ∈ omegaSlice A k :=
          (Finset.mem_product.mp hprod).2
        have hqA : qa.2 ∈ A := (Finset.mem_filter.mp hqSlice).1
        apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_product.mpr ⟨(Finset.mem_product.mp hprod).1, hqA⟩,
          hprime, hmul⟩
    rw [heq]
    exact hslices k m

/-- More than `r` selected prime quotients of one integer are a direct forbidden
configuration.  This is the arithmetic form of a daisy of facets. -/
theorem inadmissible_of_prime_quotients {A P : Finset ℕ} {r N m : ℕ}
    (hm : 0 < m)
    (hcard : r < P.card)
    (hprime : ∀ p ∈ P, p.Prime)
    (hdvd : ∀ p ∈ P, p ∣ m)
    (hquot : ∀ p ∈ P, m / p ∈ A) :
    ¬ Admissible r N A := by
  intro hA
  let f : ℕ → ℕ × ℕ := fun p => (p, m / p)
  have hmaps : Set.MapsTo f (P : Set ℕ) (representations A m : Set (ℕ × ℕ)) := by
    intro p hpP
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_product.mpr
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_dvd hm (hdvd p hpP))),
        hquot p hpP⟩
    · exact ⟨hprime p hpP, (Nat.mul_div_cancel' (hdvd p hpP)).symm⟩
  have hinj : Set.InjOn f (P : Set ℕ) := by
    intro p _ q _ hpq
    exact congrArg Prod.fst hpq
  have hle : P.card ≤ (representations A m).card :=
    Finset.card_le_card_of_injOn f hmaps hinj
  have hcap := hA.2 m
  omega

end Erdos538
