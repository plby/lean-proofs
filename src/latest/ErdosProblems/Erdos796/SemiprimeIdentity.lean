import ErdosProblems.Erdos796.Baseline
import Mathlib.Data.Finset.Sym

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# The exact semiprime bucket identity

This file proves the finite identity which turns the prime-weighted bucket
sum into the semiprime counting function.  The proof separates a semiprime
`p * q ≤ n`, with `p ≤ q`, according as its larger prime factor is at
most or greater than `√n`.
-/

namespace Erdos796

open scoped BigOperators Nat.Prime

/-- Prime pairs below the square-root threshold, written in increasing
order. -/
def smallSemiprimePairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (Nat.primesLE n.sqrt ×ˢ Nat.primesLE n.sqrt).filter fun pq => pq.1 ≤ pq.2

/-- Dependent parameters for semiprimes whose larger prime factor exceeds
the square-root threshold. -/
def largeSemiprimeParameters (n : ℕ) : Finset (Σ _q : ℕ, ℕ) :=
  (largePrimes n).sigma fun q => Nat.primesLE (n / q)

/-- Prime pairs whose larger prime factor exceeds the square-root threshold. -/
def largeSemiprimePairs (n : ℕ) : Finset (ℕ × ℕ) :=
  (largeSemiprimeParameters n).image fun qp => (qp.2, qp.1)

@[simp] theorem mem_smallSemiprimePairs {n p q : ℕ} :
    (p, q) ∈ smallSemiprimePairs n ↔
      p.Prime ∧ p ≤ n.sqrt ∧ q.Prime ∧ q ≤ n.sqrt ∧ p ≤ q := by
  simp [smallSemiprimePairs, Nat.mem_primesLE, and_assoc, and_left_comm,
    and_comm]

@[simp] theorem mem_largeSemiprimeParameters {n q p : ℕ} :
    (⟨q, p⟩ : Σ _q : ℕ, ℕ) ∈ largeSemiprimeParameters n ↔
      q ∈ largePrimes n ∧ p ∈ Nat.primesLE (n / q) := by
  simp [largeSemiprimeParameters]

@[simp] theorem mem_largeSemiprimePairs {n p q : ℕ} :
    (p, q) ∈ largeSemiprimePairs n ↔
      q ∈ largePrimes n ∧ p ∈ Nat.primesLE (n / q) := by
  classical
  constructor
  · intro hpq
    rcases Finset.mem_image.mp hpq with ⟨⟨r, a⟩, hra, heq⟩
    have hr : r ∈ largePrimes n ∧ a ∈ Nat.primesLE (n / r) :=
      mem_largeSemiprimeParameters.mp hra
    have hap : a = p := congrArg Prod.fst heq
    have hrq : r = q := congrArg Prod.snd heq
    simpa [hap, hrq] using! hr
  · rintro ⟨hq, hp⟩
    exact Finset.mem_image.mpr
      ⟨⟨q, p⟩, mem_largeSemiprimeParameters.mpr ⟨hq, hp⟩, rfl⟩

/-- The two square-root regimes are disjoint. -/
theorem disjoint_small_largeSemiprimePairs (n : ℕ) :
    Disjoint (smallSemiprimePairs n) (largeSemiprimePairs n) := by
  rw [Finset.disjoint_left]
  intro pq hsmall hlarge
  rcases pq with ⟨p, q⟩
  have hs := mem_smallSemiprimePairs.mp hsmall
  have hl := mem_largeSemiprimePairs.mp hlarge
  exact (Nat.not_lt_of_ge hs.2.2.2.1) (mem_largePrimes.mp hl.1).1

/-- Every semiprime pair belongs to exactly one of the two square-root
regimes. -/
theorem semiprimePairs_eq_small_union_large (n : ℕ) :
    semiprimePairs n = smallSemiprimePairs n ∪ largeSemiprimePairs n := by
  classical
  ext pq
  rcases pq with ⟨p, q⟩
  simp only [semiprimePairs, Finset.mem_filter, Finset.mem_product,
    Finset.mem_union, mem_smallSemiprimePairs, mem_largeSemiprimePairs]
  constructor
  · rintro ⟨⟨hp, hq⟩, hpq, hprod⟩
    by_cases hqs : q ≤ n.sqrt
    · left
      exact ⟨(Nat.mem_primesLE.mp hp).2,
        hpq.trans hqs,
        (Nat.mem_primesLE.mp hq).2, hqs, hpq⟩
    · right
      have hqprime := (Nat.mem_primesLE.mp hq).2
      have hqpos : 0 < q := hqprime.pos
      exact ⟨mem_largePrimes.mpr
          ⟨Nat.lt_of_not_ge hqs, (Nat.mem_primesLE.mp hq).1, hqprime⟩,
        Nat.mem_primesLE.mpr ⟨
          (Nat.le_div_iff_mul_le hqpos).mpr hprod,
          (Nat.mem_primesLE.mp hp).2⟩⟩
  · rintro (hsmall | hlarge)
    · rcases hsmall with ⟨hpprime, hps, hqprime, hqs, hpq⟩
      have hsle : n.sqrt ≤ n := Nat.sqrt_le_self n
      exact ⟨⟨Nat.mem_primesLE.mpr ⟨hps.trans hsle, hpprime⟩,
          Nat.mem_primesLE.mpr ⟨hqs.trans hsle, hqprime⟩⟩,
        hpq,
        (Nat.mul_le_mul hps hqs).trans (Nat.sqrt_le n)⟩
    · rcases hlarge with ⟨hq, hp⟩
      have hq' := mem_largePrimes.mp hq
      have hp' := Nat.mem_primesLE.mp hp
      have hqpos : 0 < q := hq'.2.2.pos
      have hpqprod : p * q ≤ n := (Nat.le_div_iff_mul_le hqpos).mp hp'.1
      have hpqorder : p ≤ q := by
        exact hp'.1.trans (div_le_sqrt_of_sqrt_lt hq'.1) |>.trans hq'.1.le
      have hpleprod : p ≤ p * q := Nat.le_mul_of_pos_right p hqpos
      exact ⟨⟨Nat.mem_primesLE.mpr ⟨hpleprod.trans hpqprod, hp'.2⟩,
          Nat.mem_primesLE.mpr ⟨hq'.2.1, hq'.2.2⟩⟩,
        hpqorder, hpqprod⟩

/-- Sorting a pair makes the quotient map to `Sym2` injective. -/
theorem sym2Mk_injOn_sorted :
    Set.InjOn (fun pq : ℕ × ℕ => s(pq.1, pq.2))
      {pq : ℕ × ℕ | pq.1 ≤ pq.2} := by
  rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd heq
  rw [Sym2.mk_eq_mk_iff] at heq
  rcases heq with heq | heq
  · exact heq
  · have hac : a = d := congrArg Prod.fst heq
    have hbc : b = c := congrArg Prod.snd heq
    subst d
    subst c
    have hab' : a = b := Nat.le_antisymm hab hcd
    subst b
    rfl

/-- The small semiprime regime is the symmetric square of the primes at
most `√n`. -/
theorem image_smallSemiprimePairs (n : ℕ) :
    (smallSemiprimePairs n).image (fun pq => s(pq.1, pq.2)) =
      (Nat.primesLE n.sqrt).sym2 := by
  classical
  ext z
  constructor
  · intro hz
    rcases Finset.mem_image.mp hz with ⟨⟨p, q⟩, hpq, rfl⟩
    exact Finset.mk_mem_sym2_iff.mpr
      ⟨Nat.mem_primesLE.mpr
          ⟨(mem_smallSemiprimePairs.mp hpq).2.1,
            (mem_smallSemiprimePairs.mp hpq).1⟩,
        Nat.mem_primesLE.mpr
          ⟨(mem_smallSemiprimePairs.mp hpq).2.2.2.1,
            (mem_smallSemiprimePairs.mp hpq).2.2.1⟩⟩
  · intro hz
    induction z using Sym2.inductionOn with
    | _ p q =>
      have hpq := Finset.mk_mem_sym2_iff.mp hz
      rcases le_total p q with hpqle | hqple
      · exact Finset.mem_image.mpr ⟨(p, q),
          mem_smallSemiprimePairs.mpr
            ⟨(Nat.mem_primesLE.mp hpq.1).2,
              (Nat.mem_primesLE.mp hpq.1).1,
              (Nat.mem_primesLE.mp hpq.2).2,
              (Nat.mem_primesLE.mp hpq.2).1, hpqle⟩,
          rfl⟩
      · exact Finset.mem_image.mpr ⟨(q, p),
          mem_smallSemiprimePairs.mpr
            ⟨(Nat.mem_primesLE.mp hpq.2).2,
              (Nat.mem_primesLE.mp hpq.2).1,
              (Nat.mem_primesLE.mp hpq.1).2,
              (Nat.mem_primesLE.mp hpq.1).1, hqple⟩,
          Sym2.eq_swap⟩

/-- The small regime contains `r(r+1)/2` prime pairs, where
`r = π(√n)`. -/
theorem card_smallSemiprimePairs (n : ℕ) :
    (smallSemiprimePairs n).card =
      Nat.primeCounting n.sqrt * (Nat.primeCounting n.sqrt + 1) / 2 := by
  classical
  have himage :
      ((smallSemiprimePairs n).image (fun pq => s(pq.1, pq.2))).card =
        (smallSemiprimePairs n).card := by
    rw [Finset.card_image_iff.mpr]
    intro a ha b hb hab
    exact sym2Mk_injOn_sorted
      (by simpa using! (mem_smallSemiprimePairs.mp ha).2.2.2.2)
      (by simpa using! (mem_smallSemiprimePairs.mp hb).2.2.2.2) hab
  rw [image_smallSemiprimePairs, Finset.card_sym2] at himage
  rw [← himage, Nat.primesLE_card_eq_primeCounting, Nat.choose_two_right]
  simp [Nat.mul_comm]

/-- The large regime has cardinality equal to the prime-weighted bucket
sum. -/
theorem card_largeSemiprimePairs (n : ℕ) :
    (largeSemiprimePairs n).card =
      ∑ j ∈ Finset.Icc 1 n.sqrt,
        bucketCount n j * Nat.primeCounting j := by
  classical
  have hinj : Function.Injective
      (fun qp : Σ _q : ℕ, ℕ => (qp.2, qp.1)) := by
    rintro ⟨q, p⟩ ⟨r, a⟩ h
    cases h
    rfl
  calc
    (largeSemiprimePairs n).card = (largeSemiprimeParameters n).card := by
      rw [largeSemiprimePairs, Finset.card_image_iff.mpr]
      exact fun _ _ _ _ h => hinj h
    _ = ∑ q ∈ largePrimes n, (Nat.primesLE (n / q)).card := by
      exact Finset.card_sigma _ _
    _ = ∑ q ∈ largePrimes n, Nat.primeCounting (n / q) := by simp
    _ = ∑ j ∈ Finset.Icc 1 n.sqrt,
        bucketCount n j * Nat.primeCounting j := by
      simpa [modelScore] using!
        (sum_primes_eq_modelScore n (fun j => Nat.primesLE j))

/-- Exact finite identity underlying the second-order semiprime baseline. -/
theorem sum_bucketCount_mul_primeCounting (n : ℕ) :
    (∑ j ∈ Finset.Icc 1 n.sqrt,
        bucketCount n j * Nat.primeCounting j) =
      semiprimeCount n -
        Nat.primeCounting n.sqrt * (Nat.primeCounting n.sqrt + 1) / 2 := by
  have hcard :
      semiprimeCount n =
        (smallSemiprimePairs n).card + (largeSemiprimePairs n).card := by
    rw [semiprimeCount, semiprimePairs_eq_small_union_large,
      Finset.card_union_of_disjoint (disjoint_small_largeSemiprimePairs n)]
  rw [card_smallSemiprimePairs, card_largeSemiprimePairs] at hcard
  omega

end Erdos796
