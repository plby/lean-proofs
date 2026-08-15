/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import Mathlib
import ErdosProblems.Erdos469

/-!
# Erdős Problem 442

The answer is negative.  We use the elementary counterexample consisting of the
squarefree semiprimes `p * q` with `p < q`, as described in the introduction of
Tao's paper *Dense sets of natural numbers with unusually large least common
multiples* (2024).

The reciprocal-prime Mertens estimate used below is the unconditional theorem
`Erdos469.abs_primeReciprocalSum_sub_logLog_le` already proved in this repository.
-/

namespace Erdos442

open Filter Set
open scoped BigOperators Topology

syntax (name := answerSyntax442) "answer(" term ")" : term

macro_rules
  | `(answer($t)) => `($t)

section Specification

/-- The truncated logarithm used in the upstream statement. -/
noncomputable def Real.maxLogOne (x : ℝ) : ℝ := max x.log 1

namespace Set

variable (A : Set ℕ) (x : ℝ)

/-- The finite upper-triangular set of pairs in `A ∩ [1, x]`. -/
@[inline]
abbrev bddProdUpper : Set (ℕ × ℕ) :=
  {y ∈ (A ∩ Icc 1 ⌊x⌋₊) ×ˢ (A ∩ Icc 1 ⌊x⌋₊) | y.1 < y.2}

noncomputable instance boundedIccFintype : Fintype ↥(A ∩ Icc 1 ⌊x⌋₊) :=
  ((Set.finite_Icc 1 ⌊x⌋₊).subset inter_subset_right).fintype

noncomputable instance : Fintype ↥(bddProdUpper A x) :=
  (((Set.finite_Icc 1 ⌊x⌋₊).prod (Set.finite_Icc 1 ⌊x⌋₊)).subset <| by
    rintro ⟨a, b⟩ hab
    exact ⟨hab.1.1.2, hab.1.2.2⟩).fintype

end Set

end Specification

section Counterexample

/-- Strictly upper-triangular pairs from a finite linearly ordered set. -/
def ltPairs {α : Type*} [LinearOrder α] (s : Finset α) : Finset (α × α) :=
  (s ×ˢ s).filter fun z ↦ z.1 < z.2

private def gtPairs {α : Type*} [LinearOrder α] (s : Finset α) : Finset (α × α) :=
  (s ×ˢ s).filter fun z ↦ z.2 < z.1

private lemma offDiag_eq_ltPairs_union_gtPairs {α : Type*} [LinearOrder α]
    (s : Finset α) : s.offDiag = ltPairs s ∪ gtPairs s := by
  ext z
  simp only [Finset.mem_offDiag, Finset.mem_union, ltPairs, gtPairs,
    Finset.mem_filter, Finset.mem_product]
  constructor
  · rintro ⟨h1, h2, hne⟩
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl ⟨⟨h1, h2⟩, hlt⟩
    · exact Or.inr ⟨⟨h1, h2⟩, hgt⟩
  · rintro (⟨⟨h1, h2⟩, hlt⟩ | ⟨⟨h1, h2⟩, hgt⟩)
    · exact ⟨h1, h2, ne_of_lt hlt⟩
    · exact ⟨h1, h2, ne_of_gt hgt⟩

private lemma disjoint_ltPairs_gtPairs {α : Type*} [LinearOrder α]
    (s : Finset α) : Disjoint (ltPairs s) (gtPairs s) := by
  rw [Finset.disjoint_left]
  intro z hz hz'
  simp only [ltPairs, gtPairs, Finset.mem_filter] at hz hz'
  exact not_lt_of_ge hz'.2.le hz.2

private lemma sum_gtPairs_eq_sum_ltPairs {α : Type*} [LinearOrder α]
    (s : Finset α) (f : α → ℝ) :
    (∑ z ∈ gtPairs s, f z.1 * f z.2) =
      ∑ z ∈ ltPairs s, f z.1 * f z.2 := by
  refine Finset.sum_bij (fun z _ ↦ (z.2, z.1)) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [gtPairs, Finset.mem_filter, Finset.mem_product] at hz
    simp only [ltPairs, Finset.mem_filter, Finset.mem_product]
    aesop
  · intro a ha b hb hab
    exact Prod.ext (congrArg Prod.snd hab) (congrArg Prod.fst hab)
  · intro b hb
    refine ⟨(b.2, b.1), ?_, rfl⟩
    simp only [ltPairs, Finset.mem_filter, Finset.mem_product] at hb
    simp only [gtPairs, Finset.mem_filter, Finset.mem_product]
    aesop
  · intro z hz
    ring

/-- The square of a finite sum splits into its diagonal and twice its upper triangle. -/
lemma two_mul_sum_ltPairs {α : Type*} [LinearOrder α]
    (s : Finset α) (f : α → ℝ) :
    2 * (∑ z ∈ ltPairs s, f z.1 * f z.2) =
      (∑ x ∈ s, f x) ^ 2 - ∑ x ∈ s, (f x) ^ 2 := by
  have hprod : (∑ z ∈ s ×ˢ s, f z.1 * f z.2) = (∑ x ∈ s, f x) ^ 2 := by
    rw [Finset.sum_product]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
    ring
  have hdiag : (∑ z ∈ s.diag, f z.1 * f z.2) = ∑ x ∈ s, (f x) ^ 2 := by
    rw [Finset.sum_diag]
    simp [pow_two]
  have hoff : (∑ z ∈ s.offDiag, f z.1 * f z.2) =
      (∑ z ∈ ltPairs s, f z.1 * f z.2) +
        ∑ z ∈ gtPairs s, f z.1 * f z.2 := by
    rw [offDiag_eq_ltPairs_union_gtPairs,
      Finset.sum_union (disjoint_ltPairs_gtPairs s)]
  have htotal :
      (∑ z ∈ s.diag, f z.1 * f z.2) +
          (∑ z ∈ s.offDiag, f z.1 * f z.2) =
        ∑ z ∈ s ×ˢ s, f z.1 * f z.2 := by
    rw [← Finset.sum_union (Finset.disjoint_diag_offDiag s),
      Finset.diag_union_offDiag]
  rw [hdiag, hoff, sum_gtPairs_eq_sum_ltPairs, hprod] at htotal
  linarith

/-- The counterexample: squarefree natural numbers with exactly two prime factors. -/
def squarefreeSemiprimes : Set ℕ :=
  {n | ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p < q ∧ n = p * q}

/-- Prime pairs whose product is at most `N`.  The ordering makes the factorization unique. -/
def primePairs (N : ℕ) : Finset (ℕ × ℕ) :=
  ((Erdos469.primesThrough N) ×ˢ (Erdos469.primesThrough N)).filter
    fun pq ↦ pq.1 < pq.2 ∧ pq.1 * pq.2 ≤ N

@[simp] lemma mem_primePairs {N p q : ℕ} :
    (p, q) ∈ primePairs N ↔ p.Prime ∧ q.Prime ∧ p < q ∧ p * q ≤ N := by
  rw [show (p, q) ∈ primePairs N ↔
      p.Prime ∧ p ≤ N ∧ q.Prime ∧ q ≤ N ∧ p < q ∧ p * q ≤ N by
    simp [primePairs, and_assoc]]
  constructor
  · rintro ⟨hp, -, hq, -, hpq, hprod⟩
    exact ⟨hp, hq, hpq, hprod⟩
  · rintro ⟨hp, hq, hpq, hprod⟩
    have hpN : p ≤ N := (Nat.le_mul_of_pos_right p hq.pos).trans hprod
    have hqN : q ≤ N := (Nat.le_mul_of_pos_left q hp.pos).trans
      (by simpa [mul_comm] using hprod)
    exact ⟨hp, hpN, hq, hqN, hpq, hprod⟩

/-- Ordered products of two distinct primes have unique coordinates. -/
lemma prime_product_unique {p q r s : ℕ}
    (hp : p.Prime) (_hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p < q) (hrs : r < s) (hprod : p * q = r * s) :
    p = r ∧ q = s := by
  have hpdvd : p ∣ r * s := by
    rw [← hprod]
    exact dvd_mul_right p q
  rcases (hp.dvd_mul.mp hpdvd) with hpr | hps
  · have hpr' : p = r := (Nat.dvd_prime hr).mp hpr |>.resolve_left hp.ne_one
    subst r
    exact ⟨rfl, Nat.eq_of_mul_eq_mul_left hp.pos hprod⟩
  · have hps' : p = s := (Nat.dvd_prime hs).mp hps |>.resolve_left hp.ne_one
    subst s
    have hqr : q = r := by
      apply Nat.eq_of_mul_eq_mul_right hp.pos
      simpa [mul_comm] using hprod
    subst r
    omega

lemma primePair_product_injective (N : ℕ) :
    Set.InjOn (fun pq : ℕ × ℕ ↦ pq.1 * pq.2) (primePairs N : Set (ℕ × ℕ)) := by
  intro a ha b hb hab
  rcases a with ⟨p, q⟩
  rcases b with ⟨r, s⟩
  simp only [Finset.mem_coe, mem_primePairs] at ha hb
  obtain ⟨hpr, hqs⟩ := prime_product_unique ha.1 ha.2.1 hb.1 hb.2.1
    ha.2.2.1 hb.2.2.1 hab
  simp [hpr, hqs]

/-- The finite set of squarefree semiprimes in `[1, N]`. -/
def boundedSemiprimes (N : ℕ) : Finset ℕ :=
  (primePairs N).image fun pq ↦ pq.1 * pq.2

@[simp] lemma mem_boundedSemiprimes {N n : ℕ} :
    n ∈ boundedSemiprimes N ↔ n ∈ squarefreeSemiprimes ∧ 1 ≤ n ∧ n ≤ N := by
  constructor
  · intro hn
    simp only [boundedSemiprimes, Finset.mem_image] at hn
    rcases hn with ⟨⟨p, q⟩, hpq, rfl⟩
    simp only [mem_primePairs] at hpq
    exact ⟨⟨p, q, hpq.1, hpq.2.1, hpq.2.2.1, rfl⟩,
      Nat.mul_pos hpq.1.pos hpq.2.1.pos, hpq.2.2.2⟩
  · rintro ⟨⟨p, q, hp, hq, hpq, rfl⟩, -, hN⟩
    simp only [boundedSemiprimes, Finset.mem_image]
    exact ⟨(p, q), mem_primePairs.mpr ⟨hp, hq, hpq, hN⟩, rfl⟩

/-- The bounded semiprimes are exactly the images of the bounded prime pairs. -/
lemma boundedSemiprimes_eq_image_primePairs (N : ℕ) :
    boundedSemiprimes N = (primePairs N).image fun pq ↦ pq.1 * pq.2 := by
  rfl

/-- Reciprocal mass of the squarefree semiprimes up to a natural frontier. -/
noncomputable def semiprimeMass (N : ℕ) : ℝ :=
  ∑ n ∈ boundedSemiprimes N, (1 : ℝ) / n

/-- Reciprocal mass of the primes up to a natural frontier. -/
noncomputable abbrev primeMass (N : ℕ) : ℝ := Erdos469.primeReciprocalSum N

lemma semiprimeMass_eq_sum_primePairs (N : ℕ) :
    semiprimeMass N = ∑ pq ∈ primePairs N, (1 : ℝ) / (pq.1 * pq.2) := by
  rw [semiprimeMass, show boundedSemiprimes N =
    (primePairs N).image (fun pq ↦ pq.1 * pq.2) from boundedSemiprimes_eq_image_primePairs N]
  rw [Finset.sum_image (primePair_product_injective N)]
  simp only [Nat.cast_mul]

lemma ltPairs_primesThrough_sqrt_subset_primePairs (N : ℕ) :
    ltPairs (Erdos469.primesThrough N.sqrt) ⊆ primePairs N := by
  intro pq hpq
  rcases pq with ⟨p, q⟩
  simp only [ltPairs, Finset.mem_filter, Finset.mem_product,
    Erdos469.mem_primesThrough] at hpq
  exact mem_primePairs.mpr ⟨hpq.1.1.1, hpq.1.2.1, hpq.2,
    (Nat.mul_le_mul hpq.1.1.2 hpq.1.2.2).trans (Nat.sqrt_le N)⟩

lemma sum_primeSquares_le_primeMass (N : ℕ) :
    (∑ p ∈ Erdos469.primesThrough N, ((p : ℝ)⁻¹) ^ 2) ≤ primeMass N := by
  change (∑ p ∈ Erdos469.primesThrough N, ((p : ℝ)⁻¹) ^ 2) ≤
    ∑ p ∈ Erdos469.primesThrough N, (p : ℝ)⁻¹
  apply Finset.sum_le_sum
  intro p hp
  have hp' := (Erdos469.mem_primesThrough.mp hp).1
  have hpinv : 0 ≤ (p : ℝ)⁻¹ := by positivity
  have hple : (p : ℝ)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact_mod_cast hp'.one_le
  nlinarith

/-- A coarse but uniform lower bound for the semiprime reciprocal mass. -/
lemma primeMass_sqrt_sq_sub_le_two_mul_semiprimeMass (N : ℕ) :
    primeMass N.sqrt ^ 2 - primeMass N.sqrt ≤ 2 * semiprimeMass N := by
  let s := Erdos469.primesThrough N.sqrt
  let small : ℝ := ∑ pq ∈ ltPairs s, (1 : ℝ) / (pq.1 * pq.2)
  have hsmall : small ≤ semiprimeMass N := by
    rw [semiprimeMass_eq_sum_primePairs]
    apply Finset.sum_le_sum_of_subset_of_nonneg
      (ltPairs_primesThrough_sqrt_subset_primePairs N)
    intro pq hpq hnot
    positivity
  have hid : 2 * small = primeMass N.sqrt ^ 2 -
      ∑ p ∈ s, ((p : ℝ)⁻¹) ^ 2 := by
    simpa only [small, s, one_div, Nat.cast_mul, mul_inv_rev, mul_comm,
      primeMass, Erdos469.primeReciprocalSum] using
      two_mul_sum_ltPairs s (fun p : ℕ ↦ (p : ℝ)⁻¹)
  have hsquares : (∑ p ∈ s, ((p : ℝ)⁻¹) ^ 2) ≤ primeMass N.sqrt := by
    simpa only [s] using sum_primeSquares_le_primeMass N.sqrt
  linarith

/-- A divisor of a product of two primes is one of the four evident divisors. -/
lemma dvd_prime_mul_prime_cases {d p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hd : d ∣ p * q) : d = 1 ∨ d = p ∨ d = q ∨ d = p * q := by
  rcases Nat.dvd_mul.mp hd with ⟨a, b, ha, hb, rfl⟩
  rcases (Nat.dvd_prime hp).mp ha with rfl | rfl <;>
    rcases (Nat.dvd_prime hq).mp hb with rfl | rfl <;> simp

/-- Divisibility between two products of distinct primes forces equality. -/
lemma prime_mul_prime_eq_of_dvd {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≠ q) (_hrs : r ≠ s) (h : p * q ∣ r * s) : p * q = r * s := by
  have hp_dvd : p ∣ r * s := (Nat.dvd_mul_right p q).trans h
  have hq_dvd : q ∣ r * s := (dvd_mul_left q p).trans h
  rcases hp.dvd_mul.mp hp_dvd with hpr | hps
  · have hpr' : p = r := (Nat.dvd_prime hr).mp hpr |>.resolve_left hp.ne_one
    rcases hq.dvd_mul.mp hq_dvd with hqr | hqs
    · have hqr' : q = r := (Nat.dvd_prime hr).mp hqr |>.resolve_left hq.ne_one
      exact (hpq (hpr'.trans hqr'.symm)).elim
    · have hqs' : q = s := (Nat.dvd_prime hs).mp hqs |>.resolve_left hq.ne_one
      simp [hpr', hqs']
  · have hps' : p = s := (Nat.dvd_prime hs).mp hps |>.resolve_left hp.ne_one
    rcases hq.dvd_mul.mp hq_dvd with hqr | hqs
    · have hqr' : q = r := (Nat.dvd_prime hr).mp hqr |>.resolve_left hq.ne_one
      simp [hps', hqr', mul_comm]
    · have hqs' : q = s := (Nat.dvd_prime hs).mp hqs |>.resolve_left hq.ne_one
      exact (hpq (hps'.trans hqs'.symm)).elim

/-- The GCD of two distinct squarefree semiprimes is either one or a shared prime. -/
lemma gcd_semiprimes_le_collision_sum {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hne : p * q ≠ r * s) :
    (p * q).gcd (r * s) ≤
      1 + (if p = r then p else 0) + (if p = s then p else 0) +
        (if q = r then q else 0) + (if q = s then q else 0) := by
  rcases dvd_prime_mul_prime_cases hp hq (Nat.gcd_dvd_left (p * q) (r * s)) with
    hd | hd | hd | hd
  · rw [hd]
    omega
  · have hdrs : p ∣ r * s := by
      rw [← hd]
      exact Nat.gcd_dvd_right (p * q) (r * s)
    rcases hp.dvd_mul.mp hdrs with hpr | hps
    · have hpr' : p = r := (Nat.dvd_prime hr).mp hpr |>.resolve_left hp.ne_one
      rw [hd, hpr']
      simp
      omega
    · have hps' : p = s := (Nat.dvd_prime hs).mp hps |>.resolve_left hp.ne_one
      rw [hd, hps']
      simp
      omega
  · have hdrs : q ∣ r * s := by
      rw [← hd]
      exact Nat.gcd_dvd_right (p * q) (r * s)
    rcases hq.dvd_mul.mp hdrs with hqr | hqs
    · have hqr' : q = r := (Nat.dvd_prime hr).mp hqr |>.resolve_left hq.ne_one
      rw [hd, hqr']
      simp
      omega
    · have hqs' : q = s := (Nat.dvd_prime hs).mp hqs |>.resolve_left hq.ne_one
      rw [hd, hqs']
      simp
  · have hdiv : p * q ∣ r * s := by
      have := Nat.gcd_dvd_right (p * q) (r * s)
      rwa [hd] at this
    exact (hne (prime_mul_prime_eq_of_dvd hp hq hr hs hpq hrs hdiv)).elim

lemma one_div_lcm_eq_gcd_div {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (1 : ℝ) / a.lcm b = (a.gcd b : ℝ) / ((a : ℝ) * b) := by
  have hlcm : a.lcm b ≠ 0 := Nat.lcm_ne_zero ha.ne' hb.ne'
  have hab : (a : ℝ) * b ≠ 0 := by positivity
  have hreal : (a.gcd b : ℝ) * (a.lcm b : ℝ) = (a : ℝ) * b := by
    exact_mod_cast Nat.gcd_mul_lcm a b
  field_simp
  nlinarith [hreal]

/-- Pointwise collision bound for the LCM reciprocal of two distinct prime pairs. -/
lemma one_div_lcm_prime_products_le {p q r s : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hs : s.Prime)
    (hpq : p ≠ q) (hrs : r ≠ s) (hne : p * q ≠ r * s) :
    (1 : ℝ) / (p * q).lcm (r * s) ≤
      (1 + (if p = r then p else 0) + (if p = s then p else 0) +
        (if q = r then q else 0) + (if q = s then q else 0)) /
          ((p : ℝ) * q * ((r : ℝ) * s)) := by
  rw [one_div_lcm_eq_gcd_div (Nat.mul_pos hp.pos hq.pos) (Nat.mul_pos hr.pos hs.pos)]
  push_cast
  gcongr
  exact_mod_cast gcd_semiprimes_le_collision_sum hp hq hr hs hpq hrs hne

/-- Upper-triangular pairs of bounded semiprimes. -/
def boundedSemiprimeUpper (N : ℕ) : Finset (ℕ × ℕ) :=
  ((boundedSemiprimes N) ×ˢ (boundedSemiprimes N)).filter fun ab ↦ ab.1 < ab.2

/-- The same upper triangle in unique prime-pair coordinates. -/
def primePairUpper (N : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  ((primePairs N) ×ˢ (primePairs N)).filter fun zw ↦
    zw.1.1 * zw.1.2 < zw.2.1 * zw.2.2

@[simp] lemma mem_primePairUpper {N : ℕ} {z w : ℕ × ℕ} :
    (z, w) ∈ primePairUpper N ↔
      z ∈ primePairs N ∧ w ∈ primePairs N ∧ z.1 * z.2 < w.1 * w.2 := by
  simp only [primePairUpper, Finset.mem_filter, Finset.mem_product]
  tauto

lemma primePairPair_product_injective (N : ℕ) :
    Set.InjOn
      (fun zw : (ℕ × ℕ) × (ℕ × ℕ) ↦
        (zw.1.1 * zw.1.2, zw.2.1 * zw.2.2))
      (primePairUpper N : Set ((ℕ × ℕ) × (ℕ × ℕ))) := by
  intro zw hzw uv huv heq
  have hzw' := mem_primePairUpper.mp hzw
  have huv' := mem_primePairUpper.mp huv
  have hleft := congrArg Prod.fst heq
  have hright := congrArg Prod.snd heq
  have hz := primePair_product_injective N hzw'.1 huv'.1 hleft
  have hw := primePair_product_injective N hzw'.2.1 huv'.2.1 hright
  exact Prod.ext hz hw

lemma boundedSemiprimeUpper_eq_image_primePairUpper (N : ℕ) :
    boundedSemiprimeUpper N = (primePairUpper N).image fun zw ↦
      (zw.1.1 * zw.1.2, zw.2.1 * zw.2.2) := by
  ext ab
  rcases ab with ⟨a, b⟩
  constructor
  · intro hab
    simp only [boundedSemiprimeUpper, Finset.mem_filter, Finset.mem_product] at hab
    simp only [Finset.mem_image]
    rw [boundedSemiprimes_eq_image_primePairs] at hab
    rcases Finset.mem_image.mp hab.1.1 with ⟨z, hz, rfl⟩
    rcases Finset.mem_image.mp hab.1.2 with ⟨w, hw, rfl⟩
    exact ⟨(z, w), mem_primePairUpper.mpr ⟨hz, hw, hab.2⟩, rfl⟩
  · intro hab
    simp only [Finset.mem_image] at hab
    rcases hab with ⟨⟨z, w⟩, hzw, hab⟩
    injection hab with ha hb
    subst a
    subst b
    have hzw' := mem_primePairUpper.mp hzw
    simp only [boundedSemiprimeUpper, Finset.mem_filter, Finset.mem_product]
    rw [boundedSemiprimes_eq_image_primePairs]
    exact ⟨⟨Finset.mem_image.mpr ⟨z, hzw'.1, rfl⟩,
      Finset.mem_image.mpr ⟨w, hzw'.2.1, rfl⟩⟩, hzw'.2.2⟩

/-- The upper-triangular LCM energy at a natural frontier. -/
noncomputable def semiprimeEnergy (N : ℕ) : ℝ :=
  ∑ ab ∈ boundedSemiprimeUpper N, (1 : ℝ) / ab.1.lcm ab.2

lemma semiprimeEnergy_eq_sum_primePairUpper (N : ℕ) :
    semiprimeEnergy N = ∑ zw ∈ primePairUpper N,
      (1 : ℝ) / (zw.1.1 * zw.1.2).lcm (zw.2.1 * zw.2.2) := by
  rw [semiprimeEnergy, boundedSemiprimeUpper_eq_image_primePairUpper]
  rw [Finset.sum_image (primePairPair_product_injective N)]

private lemma sum_product_weight (s : Finset ℕ) (f : ℕ → ℝ) :
    (∑ z ∈ s ×ˢ s, f z.1 * f z.2) = (∑ x ∈ s, f x) ^ 2 := by
  rw [Finset.sum_product]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]
  ring

private lemma sum_triple_weight (s : Finset ℕ) (f : ℕ → ℝ) :
    (∑ z ∈ (s ×ˢ s) ×ˢ s, f z.1.1 * f z.1.2 * f z.2) =
      (∑ x ∈ s, f x) ^ 3 := by
  rw [Finset.sum_product]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul, sum_product_weight]
  ring

private lemma sum_quad_weight (s : Finset ℕ) (f : ℕ → ℝ) :
    (∑ z ∈ (s ×ˢ s) ×ˢ (s ×ˢ s),
      f z.1.1 * f z.1.2 * f z.2.1 * f z.2.2) = (∑ x ∈ s, f x) ^ 4 := by
  rw [Finset.sum_product]
  have hp (z : ℕ × ℕ) :
      (∑ w ∈ s ×ˢ s, f z.1 * f z.2 * f w.1 * f w.2) =
        (f z.1 * f z.2) * ∑ w ∈ s ×ˢ s, f w.1 * f w.2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro w hw
    ring
  simp_rw [hp]
  rw [← Finset.sum_mul, sum_product_weight]
  ring

private noncomputable def lcmBaseTerm
    (z : (ℕ × ℕ) × (ℕ × ℕ)) : ℝ :=
  1 / ((z.1.1 : ℝ) * z.1.2 * ((z.2.1 : ℝ) * z.2.2))

private noncomputable def collision11
    (z : (ℕ × ℕ) × (ℕ × ℕ)) : ℝ :=
  ((if z.1.1 = z.2.1 then z.1.1 else 0 : ℕ) : ℝ) /
    ((z.1.1 : ℝ) * z.1.2 * ((z.2.1 : ℝ) * z.2.2))

private noncomputable def collision12
    (z : (ℕ × ℕ) × (ℕ × ℕ)) : ℝ :=
  ((if z.1.1 = z.2.2 then z.1.1 else 0 : ℕ) : ℝ) /
    ((z.1.1 : ℝ) * z.1.2 * ((z.2.1 : ℝ) * z.2.2))

private noncomputable def collision21
    (z : (ℕ × ℕ) × (ℕ × ℕ)) : ℝ :=
  ((if z.1.2 = z.2.1 then z.1.2 else 0 : ℕ) : ℝ) /
    ((z.1.1 : ℝ) * z.1.2 * ((z.2.1 : ℝ) * z.2.2))

private noncomputable def collision22
    (z : (ℕ × ℕ) × (ℕ × ℕ)) : ℝ :=
  ((if z.1.2 = z.2.2 then z.1.2 else 0 : ℕ) : ℝ) /
    ((z.1.1 : ℝ) * z.1.2 * ((z.2.1 : ℝ) * z.2.2))

private noncomputable def lcmMajorant
    (z : (ℕ × ℕ) × (ℕ × ℕ)) : ℝ :=
  lcmBaseTerm z + collision11 z + collision12 z + collision21 z + collision22 z

private lemma one_div_lcm_le_lcmMajorant {z w : ℕ × ℕ}
    (hz : z ∈ primePairs N) (hw : w ∈ primePairs N)
    (hne : z.1 * z.2 ≠ w.1 * w.2) :
    (1 : ℝ) / (z.1 * z.2).lcm (w.1 * w.2) ≤ lcmMajorant (z, w) := by
  rcases z with ⟨p, q⟩
  rcases w with ⟨r, s⟩
  simp only [mem_primePairs] at hz hw
  have h := one_div_lcm_prime_products_le hz.1 hz.2.1 hw.1 hw.2.1
    (ne_of_lt hz.2.2.1) (ne_of_lt hw.2.2.1) hne
  rw [lcmMajorant, lcmBaseTerm, collision11, collision12, collision21, collision22]
  convert h using 1
  all_goals ring

private lemma sum_lcmBaseTerm (s : Finset ℕ) :
    (∑ z ∈ (s ×ˢ s) ×ˢ (s ×ˢ s), lcmBaseTerm z) =
      (∑ p ∈ s, (p : ℝ)⁻¹) ^ 4 := by
  have hterm (p q r t : ℕ) : lcmBaseTerm ((p, q), (r, t)) =
      (p : ℝ)⁻¹ * (q : ℝ)⁻¹ * (r : ℝ)⁻¹ * (t : ℝ)⁻¹ := by
    simp only [lcmBaseTerm, one_div]
    rw [mul_inv_rev, mul_inv_rev, mul_inv_rev]
    ring
  simp_rw [hterm]
  exact sum_quad_weight s fun p ↦ (p : ℝ)⁻¹

private lemma sum_collision11 (s : Finset ℕ) (hpos : ∀ p ∈ s, 0 < p) :
    (∑ z ∈ (s ×ˢ s) ×ˢ (s ×ˢ s), collision11 z) =
      (∑ p ∈ s, (p : ℝ)⁻¹) ^ 3 := by
  rw [Finset.sum_product]
  simp_rw [Finset.sum_product]
  simp only [collision11]
  have hone (p : ℕ) (hp : p ∈ s) (q t : ℕ) :
      (∑ r ∈ s, ((if p = r then p else 0 : ℕ) : ℝ) /
        ((p : ℝ) * q * ((r : ℝ) * t))) =
          (p : ℝ)⁻¹ * (q : ℝ)⁻¹ * (t : ℝ)⁻¹ := by
    rw [Finset.sum_eq_single p]
    · simp only [if_pos]
      have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (hpos p hp).ne'
      field_simp
    · intro b hb hbp
      simp [hbp.symm]
    · intro hnot
      exact (hnot hp).elim
  have hinner (p : ℕ) (hp : p ∈ s) (q : ℕ) :
      (∑ r ∈ s, ∑ t ∈ s, ((if p = r then p else 0 : ℕ) : ℝ) /
        ((p : ℝ) * q * ((r : ℝ) * t))) =
          ∑ t ∈ s, (p : ℝ)⁻¹ * (q : ℝ)⁻¹ * (t : ℝ)⁻¹ := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t ht
    exact hone p hp q t
  rw [show (∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s, ∑ t ∈ s,
      ((if p = r then p else 0 : ℕ) : ℝ) / ((p : ℝ) * q * ((r : ℝ) * t))) =
      ∑ p ∈ s, ∑ q ∈ s, ∑ t ∈ s,
        (p : ℝ)⁻¹ * (q : ℝ)⁻¹ * (t : ℝ)⁻¹ by
    apply Finset.sum_congr rfl
    intro p hp
    apply Finset.sum_congr rfl
    intro q hq
    exact hinner p hp q]
  simpa only [Finset.sum_product] using
    sum_triple_weight s fun p ↦ (p : ℝ)⁻¹

private lemma sum_collision12_eq_sum_collision11 (s : Finset ℕ) :
    (∑ z ∈ (s ×ˢ s) ×ˢ (s ×ˢ s), collision12 z) =
      ∑ z ∈ (s ×ˢ s) ×ˢ (s ×ˢ s), collision11 z := by
  refine Finset.sum_bij (fun z _ ↦ (z.1, (z.2.2, z.2.1))) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_product] at hz ⊢
    aesop
  · intro a ha b hb hab
    exact Prod.ext (congrArg (fun z ↦ z.1) hab)
      (Prod.ext (congrArg (fun z ↦ z.2.2) hab) (congrArg (fun z ↦ z.2.1) hab))
  · intro b hb
    refine ⟨(b.1, (b.2.2, b.2.1)), ?_, rfl⟩
    simp only [Finset.mem_product] at hb ⊢
    exact ⟨hb.1, hb.2.2, hb.2.1⟩
  · intro z hz
    simp only [collision12, collision11]
    ring

private lemma sum_collision21_eq_sum_collision11 (s : Finset ℕ) :
    (∑ z ∈ (s ×ˢ s) ×ˢ (s ×ˢ s), collision21 z) =
      ∑ z ∈ (s ×ˢ s) ×ˢ (s ×ˢ s), collision11 z := by
  refine Finset.sum_bij (fun z _ ↦ ((z.1.2, z.1.1), z.2)) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_product] at hz ⊢
    aesop
  · intro a ha b hb hab
    exact Prod.ext
      (Prod.ext (congrArg (fun z ↦ z.1.2) hab) (congrArg (fun z ↦ z.1.1) hab))
      (congrArg (fun z ↦ z.2) hab)
  · intro b hb
    refine ⟨((b.1.2, b.1.1), b.2), ?_, rfl⟩
    simp only [Finset.mem_product] at hb ⊢
    exact ⟨⟨hb.1.2, hb.1.1⟩, hb.2⟩
  · intro z hz
    simp only [collision21, collision11]
    ring

private lemma sum_collision22_eq_sum_collision11 (s : Finset ℕ) :
    (∑ z ∈ (s ×ˢ s) ×ˢ (s ×ˢ s), collision22 z) =
      ∑ z ∈ (s ×ˢ s) ×ˢ (s ×ˢ s), collision11 z := by
  refine Finset.sum_bij
    (fun z _ ↦ ((z.1.2, z.1.1), (z.2.2, z.2.1))) ?_ ?_ ?_ ?_
  · intro z hz
    simp only [Finset.mem_product] at hz ⊢
    aesop
  · intro a ha b hb hab
    exact Prod.ext
      (Prod.ext (congrArg (fun z ↦ z.1.2) hab) (congrArg (fun z ↦ z.1.1) hab))
      (Prod.ext (congrArg (fun z ↦ z.2.2) hab) (congrArg (fun z ↦ z.2.1) hab))
  · intro b hb
    refine ⟨((b.1.2, b.1.1), (b.2.2, b.2.1)), ?_, rfl⟩
    simp only [Finset.mem_product] at hb ⊢
    exact ⟨⟨hb.1.2, hb.1.1⟩, hb.2.2, hb.2.1⟩
  · intro z hz
    simp only [collision22, collision11]
    ring

private lemma lcmMajorant_nonneg (z : (ℕ × ℕ) × (ℕ × ℕ)) :
    0 ≤ lcmMajorant z := by
  simp only [lcmMajorant, lcmBaseTerm, collision11, collision12, collision21, collision22]
  positivity

private lemma sum_lcmMajorant_primesThrough (N : ℕ) :
    (∑ z ∈ ((Erdos469.primesThrough N) ×ˢ (Erdos469.primesThrough N)) ×ˢ
        ((Erdos469.primesThrough N) ×ˢ (Erdos469.primesThrough N)), lcmMajorant z) =
      primeMass N ^ 4 + 4 * primeMass N ^ 3 := by
  let s := Erdos469.primesThrough N
  have hpos : ∀ p ∈ s, 0 < p := fun p hp ↦
    (Erdos469.mem_primesThrough.mp hp).1.pos
  simp only [lcmMajorant, Finset.sum_add_distrib]
  rw [sum_lcmBaseTerm, sum_collision12_eq_sum_collision11,
    sum_collision21_eq_sum_collision11, sum_collision22_eq_sum_collision11,
    sum_collision11 s hpos]
  dsimp [s, primeMass, Erdos469.primeReciprocalSum]
  ring

/-- The semiprime LCM energy is bounded by a fourth and a third power of prime mass. -/
lemma semiprimeEnergy_le_primeMass (N : ℕ) :
    semiprimeEnergy N ≤ primeMass N ^ 4 + 4 * primeMass N ^ 3 := by
  rw [semiprimeEnergy_eq_sum_primePairUpper]
  calc
    (∑ zw ∈ primePairUpper N,
        (1 : ℝ) / (zw.1.1 * zw.1.2).lcm (zw.2.1 * zw.2.2)) ≤
        ∑ zw ∈ primePairUpper N, lcmMajorant zw := by
      apply Finset.sum_le_sum
      intro zw hzw
      have hzw' := mem_primePairUpper.mp hzw
      exact one_div_lcm_le_lcmMajorant hzw'.1 hzw'.2.1 (ne_of_lt hzw'.2.2)
    _ ≤ ∑ zw ∈ ((Erdos469.primesThrough N) ×ˢ (Erdos469.primesThrough N)) ×ˢ
        ((Erdos469.primesThrough N) ×ˢ (Erdos469.primesThrough N)), lcmMajorant zw := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro zw hzw
        have hzw' := mem_primePairUpper.mp hzw
        rcases zw with ⟨⟨p, q⟩, ⟨r, s⟩⟩
        simp only [Finset.mem_product]
        simp only [mem_primePairs] at hzw'
        exact ⟨⟨Erdos469.mem_primesThrough.mpr ⟨hzw'.1.1,
          (Nat.le_mul_of_pos_right p hzw'.1.2.1.pos).trans hzw'.1.2.2.2⟩,
          Erdos469.mem_primesThrough.mpr ⟨hzw'.1.2.1,
            (Nat.le_mul_of_pos_left q hzw'.1.1.pos).trans
              (by simpa [mul_comm] using hzw'.1.2.2.2)⟩⟩,
          ⟨Erdos469.mem_primesThrough.mpr ⟨hzw'.2.1.1,
            (Nat.le_mul_of_pos_right r hzw'.2.1.2.1.pos).trans hzw'.2.1.2.2.2⟩,
          Erdos469.mem_primesThrough.mpr ⟨hzw'.2.1.2.1,
            (Nat.le_mul_of_pos_left s hzw'.2.1.1.pos).trans
              (by simpa [mul_comm] using hzw'.2.1.2.2.2)⟩⟩⟩
      · intro zw hzw hnot
        exact lcmMajorant_nonneg zw
    _ = primeMass N ^ 4 + 4 * primeMass N ^ 3 :=
      sum_lcmMajorant_primesThrough N

/-! ## Quantitative estimates -/

lemma tendsto_nat_sqrt_atTop : Tendsto Nat.sqrt atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop (b * b)] with N hN
  exact Nat.le_sqrt.mpr hN

lemma tendsto_natLogLog :
    Tendsto (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
  Real.tendsto_log_atTop.comp
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)

/-- A deliberately coarse comparison between `log N` and `log √N`. -/
lemma log_nat_le_three_mul_log_sqrt (N : ℕ) (hN : 16 ≤ N) :
    Real.log (N : ℝ) ≤ 3 * Real.log (N.sqrt : ℝ) := by
  have hM : 4 ≤ N.sqrt := Nat.le_sqrt.mpr hN
  have hMpos : (0 : ℝ) < N.sqrt := by exact_mod_cast (lt_of_lt_of_le (by omega) hM)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by omega) hN)
  have hsqrt : N < (N.sqrt + 1) * (N.sqrt + 1) := by
    simpa [pow_two] using Nat.lt_succ_sqrt N
  have hboundNat : N ≤ 4 * (N.sqrt * N.sqrt) := by
    nlinarith
  have hbound : (N : ℝ) ≤ 4 * ((N.sqrt : ℝ) * N.sqrt) := by
    exact_mod_cast hboundNat
  calc
    Real.log (N : ℝ) ≤ Real.log (4 * ((N.sqrt : ℝ) * N.sqrt)) :=
      Real.log_le_log hNpos hbound
    _ = Real.log 4 + 2 * Real.log (N.sqrt : ℝ) := by
      rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0)
          (mul_ne_zero hMpos.ne' hMpos.ne'),
        Real.log_mul hMpos.ne' hMpos.ne']
      ring
    _ ≤ 3 * Real.log (N.sqrt : ℝ) := by
      have hlog4 : Real.log (4 : ℝ) ≤ Real.log (N.sqrt : ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast hM)
      linarith

/-- On a sufficiently large range, taking a square root loses at most a factor two
in the second iterated logarithm. -/
lemma half_logLog_le_logLog_sqrt (N : ℕ) (hN : 16 ≤ N)
    (hlarge : 2 * Real.log 3 ≤ Real.log (Real.log (N : ℝ))) :
    (1 / 2 : ℝ) * Real.log (Real.log (N : ℝ)) ≤
      Real.log (Real.log (N.sqrt : ℝ)) := by
  have hM : 4 ≤ N.sqrt := Nat.le_sqrt.mpr hN
  have hlogMpos : 0 < Real.log (N.sqrt : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < N.sqrt by omega))
  have hlogNpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (lt_of_lt_of_le (by omega) hN))
  have hcmp := log_nat_le_three_mul_log_sqrt N hN
  have hlogcmp := Real.log_le_log hlogNpos hcmp
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hlogMpos.ne'] at hlogcmp
  linarith

lemma primeMass_nonneg (N : ℕ) : 0 ≤ primeMass N := by
  change 0 ≤ ∑ p ∈ Erdos469.primesThrough N, (p : ℝ)⁻¹
  positivity

/-- The repository's unconditional reciprocal-prime Mertens theorem, split into
the two inequalities used below. -/
lemma primeMass_mertens_bounds (N : ℕ) (hN : 2 ≤ N) :
    Real.log (Real.log (N : ℝ)) - Erdos469.reciprocalPrimeMertensConstant ≤
        primeMass N ∧
      primeMass N ≤ Real.log (Real.log (N : ℝ)) +
        Erdos469.reciprocalPrimeMertensConstant := by
  have h := Erdos469.abs_primeReciprocalSum_sub_logLog_le hN
  constructor <;> linarith [neg_le_abs
    (primeMass N - Real.log (Real.log (N : ℝ))),
    le_abs_self (primeMass N - Real.log (Real.log (N : ℝ)))]

/-- The quantitative estimates needed for the counterexample, with constants
chosen for easy formal arithmetic. -/
lemma semiprime_quantitative_bounds (N : ℕ) (hN : 16 ≤ N)
    (hlog3 : 2 * Real.log 3 ≤ Real.log (Real.log (N : ℝ)))
    (hMertens : 4 * Erdos469.reciprocalPrimeMertensConstant ≤
      Real.log (Real.log (N : ℝ)))
    (hlarge : 8 ≤ Real.log (Real.log (N : ℝ))) :
    let L := Real.log (Real.log (N : ℝ))
    L ^ 2 / 64 ≤ semiprimeMass N ∧
      semiprimeEnergy N ≤ 48 * L ^ 4 := by
  let L := Real.log (Real.log (N : ℝ))
  let M := N.sqrt
  have hM4 : 4 ≤ M := Nat.le_sqrt.mpr hN
  have hM2 : 2 ≤ M := hM4.trans' (by omega)
  have hhalf : (1 / 2 : ℝ) * L ≤
      Real.log (Real.log (M : ℝ)) := by
    exact half_logLog_le_logLog_sqrt N hN hlog3
  have hboundsM := primeMass_mertens_bounds M hM2
  have hboundsN := primeMass_mertens_bounds N (by omega)
  have hCnonneg := Erdos469.reciprocalPrimeMertensConstant_nonneg
  have hLnonneg : 0 ≤ L := by linarith
  have hMsqrtLower : L / 4 ≤ primeMass M := by
    dsimp [L] at hMertens ⊢
    dsimp [L, M] at hhalf hboundsM
    linarith
  have hMNupper : primeMass N ≤ 2 * L := by
    dsimp [L] at hboundsN ⊢
    linarith
  have hMsqrtTwo : 2 ≤ primeMass M := by
    calc
      (2 : ℝ) ≤ L / 4 := by linarith
      _ ≤ primeMass M := hMsqrtLower
  have hmassCore := primeMass_sqrt_sq_sub_le_two_mul_semiprimeMass N
  have hmass : L ^ 2 / 64 ≤ semiprimeMass N := by
    have hsq : (L / 4) ^ 2 ≤ primeMass M ^ 2 := by
      exact pow_le_pow_left₀ (by positivity) hMsqrtLower 2
    have hhalfSq : primeMass M ^ 2 / 2 ≤
        primeMass M ^ 2 - primeMass M := by
      nlinarith [mul_nonneg (primeMass_nonneg M) (sub_nonneg.mpr hMsqrtTwo)]
    nlinarith
  have henergyCore := semiprimeEnergy_le_primeMass N
  have hpow4 : primeMass N ^ 4 ≤ (2 * L) ^ 4 :=
    pow_le_pow_left₀ (primeMass_nonneg N) hMNupper 4
  have hpow3 : primeMass N ^ 3 ≤ (2 * L) ^ 3 :=
    pow_le_pow_left₀ (primeMass_nonneg N) hMNupper 3
  have hL3le4 : L ^ 3 ≤ L ^ 4 := by
    have h := mul_nonneg (pow_nonneg hLnonneg 3)
      (sub_nonneg.mpr (show (1 : ℝ) ≤ L by linarith))
    nlinarith
  have henergy : semiprimeEnergy N ≤ 48 * L ^ 4 := by
    calc
      semiprimeEnergy N ≤ primeMass N ^ 4 + 4 * primeMass N ^ 3 := henergyCore
      _ ≤ (2 * L) ^ 4 + 4 * (2 * L) ^ 3 := by linarith
      _ = 16 * L ^ 4 + 32 * L ^ 3 := by ring
      _ ≤ 48 * L ^ 4 := by linarith
  exact ⟨hmass, henergy⟩

lemma eventually_semiprime_quantitative_bounds :
    ∀ᶠ N : ℕ in atTop,
      let L := Real.log (Real.log (N : ℝ))
      8 ≤ L ∧ L ^ 2 / 64 ≤ semiprimeMass N ∧
        semiprimeEnergy N ≤ 48 * L ^ 4 := by
  have hlog3 := tendsto_natLogLog.eventually
    (eventually_ge_atTop (2 * Real.log 3))
  have hMertens := tendsto_natLogLog.eventually
    (eventually_ge_atTop (4 * Erdos469.reciprocalPrimeMertensConstant))
  have hlarge := tendsto_natLogLog.eventually (eventually_ge_atTop 8)
  filter_upwards [eventually_ge_atTop 16, hlog3, hMertens, hlarge] with
    N hN hlog3N hMertensN hlargeN
  exact ⟨hlargeN, semiprime_quantitative_bounds N hN hlog3N hMertensN hlargeN⟩

/-- The normalized LCM energy of the counterexample is eventually bounded by
an absolute constant. -/
lemma eventually_semiprime_normalizedEnergy_le :
    ∀ᶠ N : ℕ in atTop,
      1 / (semiprimeMass N) ^ 2 * semiprimeEnergy N ≤ 196608 := by
  filter_upwards [eventually_semiprime_quantitative_bounds] with N hN
  let L := Real.log (Real.log (N : ℝ))
  change 8 ≤ L ∧ L ^ 2 / 64 ≤ semiprimeMass N ∧
    semiprimeEnergy N ≤ 48 * L ^ 4 at hN
  rcases hN with ⟨hL, hmass, henergy⟩
  have hLpos : 0 < L := by linarith
  have hmasspos : 0 < semiprimeMass N := by
    have hsqpos : 0 < L ^ 2 / 64 := by positivity
    exact hsqpos.trans_le hmass
  have hmassSq : L ^ 4 / 4096 ≤ semiprimeMass N ^ 2 := by
    have hsq := pow_le_pow_left₀ (by positivity : 0 ≤ L ^ 2 / 64) hmass 2
    nlinarith
  have henergy' : semiprimeEnergy N ≤ 196608 * semiprimeMass N ^ 2 := by
    calc
      semiprimeEnergy N ≤ 48 * L ^ 4 := henergy
      _ ≤ 196608 * semiprimeMass N ^ 2 := by nlinarith
  rw [one_div, ← div_eq_inv_mul]
  exact (div_le_iff₀ (sq_pos_of_pos hmasspos)).2 henergy'

/-- The reciprocal mass of the squarefree semiprimes, normalized by the second
iterated logarithm, diverges along natural frontiers. -/
lemma tendsto_semiprimeMass_div_logLog :
    Tendsto (fun N : ℕ ↦
      1 / Real.log (Real.log (N : ℝ)) * semiprimeMass N) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have hscaled : Tendsto
      (fun N : ℕ ↦ (1 / 64 : ℝ) * Real.log (Real.log (N : ℝ))) atTop atTop :=
    tendsto_natLogLog.const_mul_atTop (by norm_num)
  have hb := hscaled.eventually (eventually_ge_atTop b)
  filter_upwards [eventually_semiprime_quantitative_bounds, hb] with N hN hbN
  let L := Real.log (Real.log (N : ℝ))
  change 8 ≤ L ∧ L ^ 2 / 64 ≤ semiprimeMass N ∧
    semiprimeEnergy N ≤ 48 * L ^ 4 at hN
  change b ≤ (1 / 64 : ℝ) * L at hbN
  have hLpos : 0 < L := by linarith [hN.1]
  calc
    b ≤ (1 / 64 : ℝ) * L := hbN
    _ ≤ 1 / L * semiprimeMass N := by
      rw [show 1 / L * semiprimeMass N = semiprimeMass N / L by ring,
        le_div_iff₀ hLpos]
      nlinarith [hN.2.1]

/-! ## Passage to the exact real-frontier specification -/

lemma sum_squarefreeSemiprimes_Icc_eq_semiprimeMass (x : ℝ) :
    (∑ n ∈ (squarefreeSemiprimes ∩ Icc 1 ⌊x⌋₊ : Set ℕ), (1 : ℝ) / n) =
      semiprimeMass ⌊x⌋₊ := by
  rw [semiprimeMass]
  apply Finset.sum_congr
  · ext n
    simp only [Set.mem_inter_iff, Set.mem_Icc, Set.mem_toFinset,
      mem_boundedSemiprimes]
  · intro n hn
    rfl

lemma sum_squarefreeSemiprime_bddProdUpper_eq_semiprimeEnergy (x : ℝ) :
    (∑ nm ∈ Set.bddProdUpper squarefreeSemiprimes x,
      (1 : ℝ) / nm.1.lcm nm.2) = semiprimeEnergy ⌊x⌋₊ := by
  rw [semiprimeEnergy]
  apply Finset.sum_congr
  · ext nm
    rcases nm with ⟨a, b⟩
    simp only [Set.mem_toFinset, Set.mem_sep_iff, Set.mem_prod, Set.mem_inter_iff,
      Set.mem_Icc, boundedSemiprimeUpper, Finset.mem_filter, Finset.mem_product,
      mem_boundedSemiprimes]
  · intro nm hnm
    rfl

lemma tendsto_maxLogOne_maxLogOne :
    Tendsto (fun x : ℝ ↦ Real.maxLogOne (Real.maxLogOne x)) atTop atTop := by
  have hlogLog : Tendsto (fun x : ℝ ↦ Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  refine hlogLog.congr' ?_
  have hlogOne := Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlogLogOne := hlogLog.eventually (eventually_ge_atTop 1)
  filter_upwards [hlogOne, hlogLogOne] with x hx hxx
  simp only [Real.maxLogOne, max_eq_left hx, max_eq_left hxx]

/-- Comparison of the truncated iterated logarithm at a real point with the
ordinary iterated logarithm at its natural floor. -/
lemma half_maxLogOne_le_logLog_floor (x : ℝ) (hx : 2 ≤ x)
    (hlogOne : 1 ≤ Real.log x)
    (hlogLogOne : 1 ≤ Real.log (Real.log x))
    (hlogTwo : 2 * Real.log 2 ≤ Real.log x)
    (hlogLogTwo : 2 * Real.log 2 ≤ Real.log (Real.log x)) :
    (1 / 2 : ℝ) * Real.maxLogOne (Real.maxLogOne x) ≤
      Real.log (Real.log (⌊x⌋₊ : ℝ)) := by
  have hxpos : 0 < x := by linarith
  have hhalfpos : 0 < x / 2 := by positivity
  have hfloor : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
    have hsub : x / 2 ≤ x - 1 := by linarith
    exact hsub.trans (Nat.sub_one_lt_floor x).le
  have hfloorpos : 0 < (⌊x⌋₊ : ℝ) := hhalfpos.trans_le hfloor
  have hlogFloor := Real.log_le_log hhalfpos hfloor
  have hhalfLog : (1 / 2 : ℝ) * Real.log x ≤
      Real.log (⌊x⌋₊ : ℝ) := by
    rw [Real.log_div hxpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hlogFloor
    linarith
  have hhalfLogPos : 0 < (1 / 2 : ℝ) * Real.log x := by
    have : 0 < Real.log x := by linarith [hlogTwo, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
    positivity
  have hlogLogFloor := Real.log_le_log hhalfLogPos hhalfLog
  change (1 / 2 : ℝ) *
      max (Real.log (max (Real.log x) 1)) 1 ≤ _
  rw [max_eq_left hlogOne, max_eq_left hlogLogOne]
  rw [Real.log_mul (by norm_num : (1 / 2 : ℝ) ≠ 0)
    (ne_of_gt (show 0 < Real.log x by linarith))] at hlogLogFloor
  have hlogInvTwo : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  rw [hlogInvTwo] at hlogLogFloor
  linarith

/-- The hypothesis in the Erdős problem holds for the squarefree-semiprime
counterexample, now with exactly the real frontier and truncated logarithm of
the specification. -/
lemma tendsto_real_semiprimeMass_ratio :
    Tendsto (fun x : ℝ ↦
      1 / Real.maxLogOne (Real.maxLogOne x) * semiprimeMass ⌊x⌋₊)
      atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have hlogLog : Tendsto (fun x : ℝ ↦ Real.log (Real.log x)) atTop atTop :=
    Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  have hfloorBounds := (tendsto_nat_floor_atTop (α := ℝ)).eventually
    eventually_semiprime_quantitative_bounds
  have hscaled : Tendsto (fun x : ℝ ↦
      (1 / 256 : ℝ) * Real.maxLogOne (Real.maxLogOne x)) atTop atTop :=
    tendsto_maxLogOne_maxLogOne.const_mul_atTop (by norm_num)
  have hb := hscaled.eventually (eventually_ge_atTop b)
  have hlogOne := Real.tendsto_log_atTop.eventually (eventually_ge_atTop 1)
  have hlogLogOne := hlogLog.eventually (eventually_ge_atTop 1)
  have hlogTwo := Real.tendsto_log_atTop.eventually
    (eventually_ge_atTop (2 * Real.log 2))
  have hlogLogTwo := hlogLog.eventually
    (eventually_ge_atTop (2 * Real.log 2))
  filter_upwards [eventually_ge_atTop 2, hfloorBounds, hb, hlogOne,
    hlogLogOne, hlogTwo, hlogLogTwo] with
    x hx hbounds hbX hlogOneX hlogLogOneX hlogTwoX hlogLogTwoX
  let K := Real.maxLogOne (Real.maxLogOne x)
  let L := Real.log (Real.log (⌊x⌋₊ : ℝ))
  change 8 ≤ L ∧ L ^ 2 / 64 ≤ semiprimeMass ⌊x⌋₊ ∧
    semiprimeEnergy ⌊x⌋₊ ≤ 48 * L ^ 4 at hbounds
  change b ≤ (1 / 256 : ℝ) * K at hbX
  have hK : (1 / 2 : ℝ) * K ≤ L := by
    exact half_maxLogOne_le_logLog_floor x hx hlogOneX hlogLogOneX
      hlogTwoX hlogLogTwoX
  have hKone : 1 ≤ K := le_max_right _ _
  have hKpos : 0 < K := lt_of_lt_of_le zero_lt_one hKone
  have hmass : K ^ 2 / 256 ≤ semiprimeMass ⌊x⌋₊ := by
    have hsq : ((1 / 2 : ℝ) * K) ^ 2 ≤ L ^ 2 :=
      pow_le_pow_left₀ (by positivity) hK 2
    nlinarith [hbounds.2.1]
  calc
    b ≤ (1 / 256 : ℝ) * K := hbX
    _ ≤ 1 / K * semiprimeMass ⌊x⌋₊ := by
      rw [show 1 / K * semiprimeMass ⌊x⌋₊ =
        semiprimeMass ⌊x⌋₊ / K by ring, le_div_iff₀ hKpos]
      nlinarith

lemma tendsto_squarefreeSemiprime_hypothesis :
    Tendsto (fun x : ℝ ↦
      1 / Real.maxLogOne (Real.maxLogOne x) *
        ∑ n ∈ (squarefreeSemiprimes ∩ Icc 1 ⌊x⌋₊ : Set ℕ), (1 : ℝ) / n)
      atTop atTop := by
  refine tendsto_real_semiprimeMass_ratio.congr' ?_
  filter_upwards [] with x
  rw [sum_squarefreeSemiprimes_Icc_eq_semiprimeMass]

lemma eventually_squarefreeSemiprime_normalizedEnergy_le :
    ∀ᶠ x : ℝ in atTop,
      1 / (∑ n ∈ (squarefreeSemiprimes ∩ Icc 1 ⌊x⌋₊ : Set ℕ),
          (1 : ℝ) / n) ^ 2 *
        ∑ nm ∈ Set.bddProdUpper squarefreeSemiprimes x,
          (1 : ℝ) / nm.1.lcm nm.2 ≤ 196608 := by
  have hbounds := (tendsto_nat_floor_atTop (α := ℝ)).eventually
    eventually_semiprime_normalizedEnergy_le
  filter_upwards [hbounds] with x hx
  rw [sum_squarefreeSemiprimes_Icc_eq_semiprimeMass,
    sum_squarefreeSemiprime_bddProdUpper_eq_semiprimeEnergy]
  exact hx

lemma not_tendsto_atTop_of_eventually_le {f : ℝ → ℝ} {C : ℝ}
    (hC : ∀ᶠ x in atTop, f x ≤ C) : ¬ Tendsto f atTop atTop := by
  intro hf
  have hlarge := hf.eventually (eventually_ge_atTop (C + 1))
  rcases (hC.and hlarge).exists with ⟨x, hx, h'x⟩
  linarith

/-! ## Resolution of Erdős Problem 442 -/

/-- Erdős Problem 442 has a negative answer.  The set of squarefree semiprimes
satisfies the hypothesis, while its normalized LCM energy is eventually bounded. -/
theorem erdos_442 : answer(False) ↔ ∀ (A : Set ℕ),
    Tendsto (fun x : ℝ ↦ 1 / Real.maxLogOne (Real.maxLogOne x) *
      ∑ n ∈ (A ∩ Icc 1 ⌊x⌋₊ : Set ℕ), (1 : ℝ) / n) atTop atTop →
    Tendsto (fun x : ℝ ↦ 1 / (∑ n ∈ (A ∩ Icc 1 ⌊x⌋₊ : Set ℕ),
      (1 : ℝ) / n) ^ 2 * ∑ nm ∈ Set.bddProdUpper A x,
        (1 : ℝ) / nm.1.lcm nm.2) atTop atTop := by
  constructor
  · intro h
    exact h.elim
  · intro hclaimed
    have hdiverges := hclaimed squarefreeSemiprimes
      tendsto_squarefreeSemiprime_hypothesis
    exact (not_tendsto_atTop_of_eventually_le
      eventually_squarefreeSemiprime_normalizedEnergy_le) hdiverges

end Counterexample

end Erdos442
