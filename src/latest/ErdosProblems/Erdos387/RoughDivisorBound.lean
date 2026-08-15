/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.ReciprocalEnergy
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Finset.Sigma

/-!
# Divisor bounds for rough integers

These elementary estimates complement the squarefull reduction in
`ReciprocalEnergy.lean`.  They keep track of prime factors with multiplicity:
a `z`-rough integer has `z ^ Ω(n) ≤ n`, while its divisor count is at most
`2 ^ Ω(n)`.
-/

namespace Erdos387

open scoped ArithmeticFunction.Omega

theorem card_divisors_le_two_pow_cardFactors {n : ℕ} (hn : n ≠ 0) :
    n.divisors.card ≤ 2 ^ ArithmeticFunction.cardFactors n := by
  rw [Nat.card_divisors hn,
    ArithmeticFunction.cardFactors_eq_sum_factorization]
  calc
    ∏ p ∈ n.primeFactors, (n.factorization p + 1) ≤
        ∏ p ∈ n.primeFactors, 2 ^ n.factorization p := by
      apply Finset.prod_le_prod
      · intro p hp
        omega
      · intro p hp
        exact Nat.succ_le_iff.mpr (n.factorization p).lt_two_pow_self
    _ = 2 ^ n.factorization.sum (fun _ e => e) := by
      rw [Finsupp.sum]
      exact Finset.prod_pow_eq_pow_sum n.primeFactors
        (fun p => n.factorization p) 2

/-- Each prime factor in the factor list of a rough number is at least the
roughness threshold, so multiplying those inequalities gives the claimed
power bound. -/
theorem z_pow_cardFactors_le_of_rough {z n : ℕ} (hn : n ≠ 0)
    (hrough : IsZRough z n) :
    z ^ ArithmeticFunction.cardFactors n ≤ n := by
  rw [ArithmeticFunction.cardFactors_apply]
  calc
    z ^ n.primeFactorsList.length ≤ n.primeFactorsList.prod := by
      apply List.pow_card_le_prod
      intro p hp
      have hprime : p.Prime := Nat.prime_of_mem_primeFactorsList hp
      have hpn : p ∣ n := Nat.dvd_of_mem_primeFactorsList hp
      by_contra hpz
      exact hrough p hprime (Nat.lt_of_not_ge hpz) hpn
    _ = n := Nat.prod_primeFactorsList hn

/-- If a rough integer lies below the next `z`-power, then its number of
prime factors with multiplicity is at most the preceding exponent. -/
theorem cardFactors_le_of_rough_lt_pow
    {z n L : ℕ} (hz : 1 < z) (hn : n ≠ 0) (hrough : IsZRough z n)
    (hnPow : n < z ^ (L + 1)) :
    ArithmeticFunction.cardFactors n ≤ L := by
  by_contra hnot
  have hExp : L + 1 ≤ ArithmeticFunction.cardFactors n := by omega
  have hpow : z ^ (L + 1) ≤
      z ^ ArithmeticFunction.cardFactors n :=
    Nat.pow_le_pow_right hz.le hExp
  have hroughPow := z_pow_cardFactors_le_of_rough hn hrough
  omega

/-- Explicit divisor-fibre consequence used after bounding a squarefull
product by a fixed power of the ambient dyadic endpoint. -/
theorem card_divisors_le_two_pow_of_rough_lt_pow
    {z n L : ℕ} (hz : 1 < z) (hn : n ≠ 0) (hrough : IsZRough z n)
    (hnPow : n < z ^ (L + 1)) :
    n.divisors.card ≤ 2 ^ L := by
  exact (card_divisors_le_two_pow_cardFactors hn).trans
    (Nat.pow_le_pow_right (by omega)
      (cardFactors_le_of_rough_lt_pow hz hn hrough hnPow))

/-- The square part formed by taking half of every prime exponent. -/
def factorizationSquarePart (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ (n.factorization p / 2)

/-- The squarefree parity remainder of the prime exponents. -/
def factorizationOddPart (n : ℕ) : ℕ :=
  ∏ p ∈ n.primeFactors, p ^ (n.factorization p % 2)

theorem factorizationSquarePart_sq_mul_oddPart {n : ℕ} (hn : n ≠ 0) :
    factorizationSquarePart n ^ 2 * factorizationOddPart n = n := by
  rw [factorizationSquarePart, factorizationOddPart,
    ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  calc
    ∏ p ∈ n.primeFactors,
        (p ^ (n.factorization p / 2)) ^ 2 *
          p ^ (n.factorization p % 2) =
        ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
      apply Finset.prod_congr rfl
      intro p hp
      rw [← pow_mul, ← pow_add]
      congr 1
      omega
    _ = n := (Nat.prod_primeFactors_pow_factorization hn).symm

theorem factorizationSquarePart_pos (n : ℕ) :
    0 < factorizationSquarePart n := by
  unfold factorizationSquarePart
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors (by simpa using hp)).pos _

theorem factorizationOddPart_pos (n : ℕ) :
    0 < factorizationOddPart n := by
  unfold factorizationOddPart
  apply Finset.prod_pos
  intro p hp
  exact pow_pos (Nat.prime_of_mem_primeFactors (by simpa using hp)).pos _

/-- Squarefullness forces each odd parity factor to occur already in the
square part. -/
theorem factorizationOddPart_dvd_squarePart
    {n : ℕ} (hn : n ≠ 0) (hsq : IsSquarefull n) :
    factorizationOddPart n ∣ factorizationSquarePart n := by
  unfold factorizationOddPart factorizationSquarePart
  apply Finset.prod_dvd_prod_of_dvd
  intro p hp
  have hpPrime : p.Prime := Nat.prime_of_mem_primeFactors
    (by simpa using hp)
  have hpDvd : p ∣ n := Nat.dvd_of_mem_primeFactors
    (by simpa using hp)
  have hpSq : p ^ 2 ∣ n := hsq p hpPrime hpDvd
  have htwo : 2 ≤ n.factorization p :=
    (hpPrime.pow_dvd_iff_le_factorization hn).mp hpSq
  apply pow_dvd_pow p
  have hmod : n.factorization p % 2 < 2 := Nat.mod_lt _ (by omega)
  have hdiv : 1 ≤ n.factorization p / 2 := by omega
  omega

theorem factorizationSquarePart_dvd {n : ℕ} (hn : n ≠ 0) :
    factorizationSquarePart n ∣ n := by
  have hdiv : factorizationSquarePart n ∣
      factorizationSquarePart n ^ 2 * factorizationOddPart n :=
    dvd_mul_of_dvd_left
    (dvd_pow_self (factorizationSquarePart n) (by omega : (2 : ℕ) ≠ 0))
    (factorizationOddPart n)
  rw [factorizationSquarePart_sq_mul_oddPart hn] at hdiv
  exact hdiv

theorem factorizationOddPart_dvd {n : ℕ} (hn : n ≠ 0) :
    factorizationOddPart n ∣ n := by
  have hdiv : factorizationOddPart n ∣
      factorizationSquarePart n ^ 2 * factorizationOddPart n :=
    dvd_mul_left (factorizationOddPart n) (factorizationSquarePart n ^ 2)
  rw [factorizationSquarePart_sq_mul_oddPart hn] at hdiv
  exact hdiv

theorem factorizationSquarePart_sq_le {n R : ℕ} (hn : n ≠ 0)
    (hnR : n ≤ R) :
    factorizationSquarePart n ^ 2 ≤ R := by
  have hodd : 1 ≤ factorizationOddPart n :=
    factorizationOddPart_pos n
  rw [← factorizationSquarePart_sq_mul_oddPart hn] at hnR
  exact (Nat.le_mul_of_pos_right _ hodd).trans hnR

theorem factorizationSquarePart_le_sqrt {n R : ℕ} (hn : n ≠ 0)
    (hnR : n ≤ R) :
    factorizationSquarePart n ≤ Nat.sqrt R := by
  rw [Nat.le_sqrt']
  exact factorizationSquarePart_sq_le hn hnR

theorem factorizationSquarePart_rough {z n : ℕ} (hn : n ≠ 0)
    (hrough : IsZRough z n) :
    IsZRough z (factorizationSquarePart n) := by
  intro p hp hpz hpd
  exact hrough p hp hpz (hpd.trans (factorizationSquarePart_dvd hn))

theorem factorizationOddPart_rough {z n : ℕ} (hn : n ≠ 0)
    (hrough : IsZRough z n) :
    IsZRough z (factorizationOddPart n) := by
  intro p hp hpz hpd
  exact hrough p hp hpz (hpd.trans (factorizationOddPart_dvd hn))

/-- Positive rough integers up to `R`. -/
noncomputable def roughPositiveRange (z R : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 R).filter (IsZRough z)

/-- Positive squarefull `z`-rough integers up to `R`. -/
noncomputable def roughSquarefullRange (z R : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 R).filter fun n => IsSquarefull n ∧ IsZRough z n

/-- Canonical square/odd-part encoding of a rough squarefull integer. -/
def squarefullPair (n : ℕ) : Σ _a : ℕ, ℕ :=
  ⟨factorizationSquarePart n, factorizationOddPart n⟩

theorem squarefullPair_injective_on_positive :
    Set.InjOn squarefullPair (Set.Ici 1 : Set ℕ) := by
  intro m hm n hn hpair
  change 1 ≤ m at hm
  change 1 ≤ n at hn
  have hm0 : m ≠ 0 := by omega
  have hn0 : n ≠ 0 := by omega
  have ha : factorizationSquarePart m = factorizationSquarePart n :=
    congrArg Sigma.fst hpair
  have hb : factorizationOddPart m = factorizationOddPart n := by
    simpa [squarefullPair] using congrArg Sigma.snd hpair
  rw [← factorizationSquarePart_sq_mul_oddPart hm0,
    ← factorizationSquarePart_sq_mul_oddPart hn0, ha, hb]

theorem roughSquarefullRange_card_le_divisorSum (z R : ℕ) :
    (roughSquarefullRange z R).card ≤
      ∑ a ∈ roughPositiveRange z (Nat.sqrt R),
        a.divisors.card := by
  classical
  let A := roughPositiveRange z (Nat.sqrt R)
  let T : Finset (Σ _a : ℕ, ℕ) := A.sigma fun a => a.divisors
  calc
    (roughSquarefullRange z R).card ≤ T.card := by
      apply Finset.card_le_card_of_injOn squarefullPair
      · intro n hn
        change n ∈ roughSquarefullRange z R at hn
        rw [roughSquarefullRange, Finset.mem_filter, Finset.mem_Icc] at hn
        change squarefullPair n ∈ A.sigma (fun a => a.divisors)
        rw [Finset.mem_sigma]
        have hn0 : n ≠ 0 := by omega
        refine ⟨?_, ?_⟩
        · change factorizationSquarePart n ∈
            roughPositiveRange z (Nat.sqrt R)
          rw [roughPositiveRange, Finset.mem_filter, Finset.mem_Icc]
          exact ⟨⟨factorizationSquarePart_pos n,
            factorizationSquarePart_le_sqrt hn0 hn.1.2⟩,
            factorizationSquarePart_rough hn0 hn.2.2⟩
        · rw [Nat.mem_divisors]
          exact ⟨factorizationOddPart_dvd_squarePart hn0 hn.2.1,
            (factorizationSquarePart_pos n).ne'⟩
      · apply squarefullPair_injective_on_positive.mono
        intro n hn
        change n ∈ roughSquarefullRange z R at hn
        rw [roughSquarefullRange, Finset.mem_filter, Finset.mem_Icc] at hn
        exact hn.1.1
    _ = ∑ a ∈ roughPositiveRange z (Nat.sqrt R),
        a.divisors.card := by
      simp [T, A]

/-- A fully explicit rough-squarefull counting bound. -/
theorem roughSquarefullRange_card_le_sqrt_mul_two_pow
    {z R L : ℕ} (hz : 1 < z) (hRPow : R < z ^ (L + 1)) :
    (roughSquarefullRange z R).card ≤ Nat.sqrt R * 2 ^ L := by
  classical
  let A := roughPositiveRange z (Nat.sqrt R)
  calc
    (roughSquarefullRange z R).card ≤
        ∑ a ∈ A, a.divisors.card := by
      exact roughSquarefullRange_card_le_divisorSum z R
    _ ≤ ∑ _a ∈ A, 2 ^ L := by
      apply Finset.sum_le_sum
      intro a ha
      have haData := ha
      change a ∈ roughPositiveRange z (Nat.sqrt R) at haData
      rw [roughPositiveRange, Finset.mem_filter, Finset.mem_Icc] at haData
      apply card_divisors_le_two_pow_of_rough_lt_pow hz (by omega) haData.2
      exact lt_of_le_of_lt
        (haData.1.2.trans (Nat.sqrt_le_self R)) hRPow
    _ = A.card * 2 ^ L := by simp
    _ ≤ Nat.sqrt R * 2 ^ L := by
      gcongr
      dsimp [A]
      exact Finset.card_le_card (by
        intro a ha
        rw [roughPositiveRange, Finset.mem_filter] at ha
        exact ha.1) |>.trans (by simp)

/-- A product of rough positive coordinates is rough. -/
theorem reciprocalEnergyTuple_product_rough
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Finset ι} {U : Finset ℕ} {z : ℕ}
    (hUrough : ∀ u ∈ U, IsZRough z u)
    {s : ι → ℕ} (hs : s ∈ reciprocalEnergyTuples A U) :
    IsZRough z (∏ i : ι, s i) := by
  intro p hp hpz hpProd
  obtain ⟨i, _hi, hpi⟩ :=
    (hp.prime.dvd_finsetProd_iff s).mp hpProd
  exact hUrough (s i) (reciprocalEnergyTuple_coordinate_mem hs i)
    p hp hpz hpi

/-- Reciprocal energy is supported on the rough-squarefull product range. -/
theorem reciprocalEnergyTuple_product_mem_roughSquarefullRange
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Finset ι} {U : Finset ℕ} {z T : ℕ}
    (hUpos : ∀ u ∈ U, 0 < u) (hUle : ∀ u ∈ U, u ≤ T)
    (hUrough : ∀ u ∈ U, IsZRough z u)
    {s : ι → ℕ} (hs : s ∈ reciprocalEnergyTuples A U) :
    (∏ i : ι, s i) ∈
      roughSquarefullRange z (T ^ Fintype.card ι) := by
  classical
  rw [roughSquarefullRange, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨reciprocalEnergyTuple_product_pos hUpos hs,
      reciprocalEnergyTuple_product_le hUle hs⟩,
    reciprocalEnergyTuple_product_squarefull hUpos hs,
    reciprocalEnergyTuple_product_rough hUrough hs⟩

/-- Elementary reciprocal-energy bound obtained from squarefull support,
rough prime-factor multiplicity, and the divisor-box bound on every product
fibre. -/
theorem reciprocalEnergyTuples_card_le_roughSquarefull_envelope
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Finset ι) (U : Finset ℕ) {z T L : ℕ}
    (hz : 1 < z) (hUpos : ∀ u ∈ U, 0 < u)
    (hUle : ∀ u ∈ U, u ≤ T)
    (hUrough : ∀ u ∈ U, IsZRough z u)
    (hTPow : T ^ Fintype.card ι < z ^ (L + 1)) :
    (reciprocalEnergyTuples A U).card ≤
      Nat.sqrt (T ^ Fintype.card ι) * 2 ^ L *
        (2 ^ L) ^ Fintype.card ι := by
  classical
  let R := T ^ Fintype.card ι
  let Q := roughSquarefullRange z R
  let P : (ι → ℕ) → ℕ := fun s => ∏ i : ι, s i
  have hmap :
      ((reciprocalEnergyTuples A U : Finset (ι → ℕ)) : Set (ι → ℕ)).MapsTo
        P (Q : Set ℕ) := by
    intro s hs
    exact reciprocalEnergyTuple_product_mem_roughSquarefullRange
      hUpos hUle hUrough hs
  calc
    (reciprocalEnergyTuples A U).card =
        ∑ N ∈ Q,
          ((reciprocalEnergyTuples A U).filter (fun s => P s = N)).card :=
      Finset.card_eq_sum_card_fiberwise hmap
    _ ≤ ∑ _N ∈ Q, (2 ^ L) ^ Fintype.card ι := by
      apply Finset.sum_le_sum
      intro N hN
      have hNData := hN
      change N ∈ roughSquarefullRange z R at hNData
      rw [roughSquarefullRange, Finset.mem_filter, Finset.mem_Icc] at hNData
      have hNDiv : N.divisors.card ≤ 2 ^ L := by
        apply card_divisors_le_two_pow_of_rough_lt_pow hz (by omega) hNData.2.2
        exact lt_of_le_of_lt hNData.1.2 hTPow
      exact (reciprocalEnergy_productFiber_card_le A U (by omega)).trans
        (Nat.pow_le_pow_left hNDiv (Fintype.card ι))
    _ = Q.card * (2 ^ L) ^ Fintype.card ι := by simp
    _ ≤ (Nat.sqrt R * 2 ^ L) * (2 ^ L) ^ Fintype.card ι := by
      gcongr
      exact roughSquarefullRange_card_le_sqrt_mul_two_pow hz hTPow
    _ = Nat.sqrt (T ^ Fintype.card ι) * 2 ^ L *
        (2 ^ L) ^ Fintype.card ι := by rfl

/-- The first half of `Fin (2 * ell)`, used to put `ell` reciprocal terms on
each side of the energy equation. -/
def reciprocalLeftHalf (ell : ℕ) : Finset (Fin (2 * ell)) :=
  Finset.univ.filter fun i => i.val < ell

theorem sqrt_pow_two_mul (T ell : ℕ) :
    Nat.sqrt (T ^ (2 * ell)) = T ^ ell := by
  rw [show T ^ (2 * ell) = (T ^ ell) ^ 2 by
    rw [← pow_mul]
    congr 1
    omega]
  exact Nat.sqrt_eq' _

/-- Symmetric `2*ell`-variable form of the elementary energy estimate. -/
theorem reciprocalHalfEnergy_card_le_envelope
    (ell : ℕ) (U : Finset ℕ) {z T L : ℕ}
    (hz : 1 < z) (hUpos : ∀ u ∈ U, 0 < u)
    (hUle : ∀ u ∈ U, u ≤ T)
    (hUrough : ∀ u ∈ U, IsZRough z u)
    (hTPow : T ^ (2 * ell) < z ^ (L + 1)) :
    (reciprocalEnergyTuples (reciprocalLeftHalf ell) U).card ≤
      T ^ ell * 2 ^ L * (2 ^ L) ^ (2 * ell) := by
  have hTPow' : T ^ Fintype.card (Fin (2 * ell)) < z ^ (L + 1) := by
    simpa using hTPow
  simpa [sqrt_pow_two_mul] using
    (reciprocalEnergyTuples_card_le_roughSquarefull_envelope
      (reciprocalLeftHalf ell) U hz hUpos hUle hUrough hTPow')

end Erdos387
