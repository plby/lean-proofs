/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperRoughShell
import ErdosProblems.Erdos446.FordClusterLogMoments

/-!
# Erdős Problem 446: the largest-prime shell decomposition

This is the exact arithmetic factorization used in the squarefree part of
Ford's Lemma 3.2.  Given a squarefree integer `n` and a distinguished prime
`p ∣ n`, split the prime support of `n` strictly below and strictly above
`p`.  Their products `a` and `b` satisfy

`n = a * p * b`,  `P⁺(a) < p < P⁻(b)`.

The second displayed assertion is expressed without total least/greatest
prime-factor functions: every prime divisor of `a` is below `p`, and `b` is
`p`-rough.  If `p` is the largest prime factor of a divisor `m ∣ n`, then
`m / p ∣ a`; hence the original divisor is reconstructed as `(m / p) * p`.
The last theorem places `n` in the literal rough-product shell used by the
finite Brun bound in `UpperRoughShell`.
-/

namespace Erdos446

open Finset
open scoped BigOperators

noncomputable section

/-- Prime support of `n` strictly below the pivot `p`. -/
def fordPrimeSupportBelow (n p : ℕ) : Finset ℕ :=
  n.primeFactors.filter fun q ↦ q < p

/-- Prime support of `n` strictly above the pivot `p`. -/
def fordPrimeSupportAbove (n p : ℕ) : Finset ℕ :=
  n.primeFactors.filter fun q ↦ p < q

/-- The product of all prime factors of `n` below `p`. -/
def fordLowerPrimePart (n p : ℕ) : ℕ :=
  (fordPrimeSupportBelow n p).prod id

/-- The product of all prime factors of `n` above `p`. -/
def fordUpperPrimePart (n p : ℕ) : ℕ :=
  (fordPrimeSupportAbove n p).prod id

theorem fordPrimeSupport_pivot_partition {n p : ℕ}
    (hp : p ∈ n.primeFactors) :
    (fordPrimeSupportBelow n p ∪ {p}) ∪
        fordPrimeSupportAbove n p = n.primeFactors := by
  ext q
  simp only [fordPrimeSupportBelow, fordPrimeSupportAbove,
    Finset.mem_union, Finset.mem_filter, Finset.mem_singleton]
  constructor
  · rintro ((⟨hqn, _⟩ | rfl) | ⟨hqn, _⟩)
    · exact hqn
    · exact hp
    · exact hqn
  · intro hqn
    rcases lt_trichotomy q p with hqp | rfl | hpq
    · exact Or.inl (Or.inl ⟨hqn, hqp⟩)
    · exact Or.inl (Or.inr rfl)
    · exact Or.inr ⟨hqn, hpq⟩

theorem fordLowerPrimePart_pos (n p : ℕ) :
    0 < fordLowerPrimePart n p := by
  unfold fordLowerPrimePart
  apply Finset.prod_pos
  intro q hq
  exact (Nat.prime_of_mem_primeFactors
    (Finset.mem_filter.mp hq).1).pos

theorem fordUpperPrimePart_pos (n p : ℕ) :
    0 < fordUpperPrimePart n p := by
  unfold fordUpperPrimePart
  apply Finset.prod_pos
  intro q hq
  exact (Nat.prime_of_mem_primeFactors
    (Finset.mem_filter.mp hq).1).pos

/-- Every prime divisor of the lower part is strictly below the pivot. -/
theorem prime_lt_of_dvd_fordLowerPrimePart {n p q : ℕ}
    (hq : q.Prime) (hqdvd : q ∣ fordLowerPrimePart n p) :
    q < p := by
  have hpos := fordLowerPrimePart_pos n p
  have hpf : (fordLowerPrimePart n p).primeFactors =
      fordPrimeSupportBelow n p := by
    unfold fordLowerPrimePart
    exact Nat.primeFactors_prod fun r hr ↦
      Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1
  have hqmem : q ∈ (fordLowerPrimePart n p).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, hqdvd, hpos.ne'⟩
  rw [hpf] at hqmem
  exact (Finset.mem_filter.mp hqmem).2

/-- The upper support product is genuinely `p`-rough. -/
theorem fordUpperPrimePart_isZRough (n p : ℕ) :
    Erdos387.IsZRough p (fordUpperPrimePart n p) := by
  intro q hqPrime hqp hqdvd
  have hpos := fordUpperPrimePart_pos n p
  have hpf : (fordUpperPrimePart n p).primeFactors =
      fordPrimeSupportAbove n p := by
    unfold fordUpperPrimePart
    exact Nat.primeFactors_prod fun r hr ↦
      Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1
  have hqmem : q ∈ (fordUpperPrimePart n p).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hqPrime, hqdvd, hpos.ne'⟩
  rw [hpf] at hqmem
  have hpq := (Finset.mem_filter.mp hqmem).2
  omega

/-- Exact support factorization around a prime pivot. -/
theorem fordLower_mul_pivot_mul_upper {n p : ℕ}
    (hn : Squarefree n) (hp : p ∈ n.primeFactors) :
    fordLowerPrimePart n p * p * fordUpperPrimePart n p = n := by
  have hbelowP : Disjoint (fordPrimeSupportBelow n p) ({p} : Finset ℕ) := by
    rw [Finset.disjoint_left]
    intro q hqBelow hqp
    have hlt := (Finset.mem_filter.mp hqBelow).2
    simp only [Finset.mem_singleton] at hqp
    omega
  have hleftAbove :
      Disjoint (fordPrimeSupportBelow n p ∪ ({p} : Finset ℕ))
        (fordPrimeSupportAbove n p) := by
    rw [Finset.disjoint_left]
    intro q hqLeft hqAbove
    have hgt := (Finset.mem_filter.mp hqAbove).2
    rcases Finset.mem_union.mp hqLeft with hqBelow | hqp
    · have hlt := (Finset.mem_filter.mp hqBelow).2
      omega
    · simp only [Finset.mem_singleton] at hqp
      omega
  calc
    fordLowerPrimePart n p * p * fordUpperPrimePart n p =
        ((fordPrimeSupportBelow n p ∪ {p}).prod id) *
          (fordPrimeSupportAbove n p).prod id := by
      rw [Finset.prod_union hbelowP]
      simp [fordLowerPrimePart, fordUpperPrimePart]
    _ = (((fordPrimeSupportBelow n p ∪ {p}) ∪
          fordPrimeSupportAbove n p).prod id) := by
      rw [Finset.prod_union hleftAbove]
    _ = n := by
      rw [fordPrimeSupport_pivot_partition hp]
      simpa using Nat.prod_primeFactors_of_squarefree hn

/-- A divisor's cofactor after deletion of its largest prime is contained
in the global lower support product. -/
theorem largestPrimeCofactor_dvd_fordLowerPrimePart
    {n m : ℕ} (hn : Squarefree n) (hm : m ∣ n) (hmOne : 1 < m) :
    m / Erdos469.largestPrimeFactor m ∣
      fordLowerPrimePart n (Erdos469.largestPrimeFactor m) := by
  let p := Erdos469.largestPrimeFactor m
  have hpSpec : Erdos469.IsLargestPrimeFactor m p :=
    Erdos469.largestPrimeFactor_spec hmOne
  have hmSq : Squarefree m := hn.squarefree_of_dvd hm
  have hpMem : p ∈ m.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hpSpec.prime, hpSpec.dvd, by omega⟩
  have hsub : m.primeFactors \ {p} ⊆ fordPrimeSupportBelow n p := by
    intro q hq
    have hqData := Finset.mem_sdiff.mp hq
    have hqPrime := Nat.prime_of_mem_primeFactors hqData.1
    have hqDvd := Nat.dvd_of_mem_primeFactors hqData.1
    have hqLe : q ≤ p := hpSpec.2.2 q hqPrime hqDvd
    have hqNe : q ≠ p := by
      simpa using hqData.2
    have hqLt : q < p := lt_of_le_of_ne hqLe hqNe
    rw [fordPrimeSupportBelow, Finset.mem_filter]
    exact ⟨Nat.primeFactors_mono hm hn.ne_zero hqData.1, hqLt⟩
  have hprodDvd := Finset.prod_dvd_prod_of_subset
    (m.primeFactors \ {p}) (fordPrimeSupportBelow n p) id hsub
  have hcofactor :
      (m.primeFactors \ {p}).prod id = m / p := by
    simpa using
      (Nat.prod_primeFactors_sdiff_of_squarefree hmSq
        (show ({p} : Finset ℕ) ⊆ m.primeFactors by simpa using hpMem))
  rw [hcofactor] at hprodDvd
  exact hprodDvd

/-- The distinguished largest prime is a prime factor of the ambient
squarefree integer. -/
theorem largestPrimeFactor_mem_ambientPrimeFactors
    {n m : ℕ} (hn : Squarefree n) (hm : m ∣ n) (hmOne : 1 < m) :
    Erdos469.largestPrimeFactor m ∈ n.primeFactors := by
  have hpSpec := Erdos469.largestPrimeFactor_spec hmOne
  exact Nat.mem_primeFactors.mpr
    ⟨hpSpec.prime, hpSpec.dvd.trans hm, hn.ne_zero⟩

/-- Complete largest-prime shell data attached to a squarefree divisor. -/
theorem squarefree_largestPrime_shell
    {n m : ℕ} (hn : Squarefree n) (hm : m ∣ n) (hmOne : 1 < m) :
    let p := Erdos469.largestPrimeFactor m
    let a := fordLowerPrimePart n p
    let b := fordUpperPrimePart n p
    p.Prime ∧ p ∈ n.primeFactors ∧ 0 < a ∧ 0 < b ∧
      n = a * p * b ∧ Erdos387.IsZRough p b ∧
      m / p ∈ a.divisors ∧ m = (m / p) * p := by
  dsimp only
  let p := Erdos469.largestPrimeFactor m
  have hpSpec : Erdos469.IsLargestPrimeFactor m p :=
    Erdos469.largestPrimeFactor_spec hmOne
  have hpAmbient : p ∈ n.primeFactors :=
    largestPrimeFactor_mem_ambientPrimeFactors hn hm hmOne
  have haPos := fordLowerPrimePart_pos n p
  have hbPos := fordUpperPrimePart_pos n p
  have hcofactor := largestPrimeCofactor_dvd_fordLowerPrimePart hn hm hmOne
  refine ⟨hpSpec.prime, hpAmbient, haPos, hbPos,
    (fordLower_mul_pivot_mul_upper hn hpAmbient).symm,
    fordUpperPrimePart_isZRough n p, ?_, ?_⟩
  · exact Nat.mem_divisors.mpr ⟨hcofactor, haPos.ne'⟩
  · exact (Nat.div_mul_cancel hpSpec.dvd).symm

/-- If a complementary factor has a larger largest prime, the rough
residual is nontrivial and is itself larger than the pivot. -/
theorem largestPrimeFactor_lt_fordUpperPrimePart_of_complement
    {n m e : ℕ} (hn : Squarefree n) (hm : m ∣ n) (hmOne : 1 < m)
    (he : e ∣ n) (heOne : 1 < e)
    (hmax : Erdos469.largestPrimeFactor m <
      Erdos469.largestPrimeFactor e) :
    Erdos469.largestPrimeFactor m <
      fordUpperPrimePart n (Erdos469.largestPrimeFactor m) := by
  let p := Erdos469.largestPrimeFactor m
  let r := Erdos469.largestPrimeFactor e
  have hrSpec : Erdos469.IsLargestPrimeFactor e r :=
    Erdos469.largestPrimeFactor_spec heOne
  have hrAmbient : r ∈ n.primeFactors := Nat.mem_primeFactors.mpr
    ⟨hrSpec.prime, hrSpec.dvd.trans he, hn.ne_zero⟩
  have hrAbove : r ∈ fordPrimeSupportAbove n p := by
    rw [fordPrimeSupportAbove, Finset.mem_filter]
    exact ⟨hrAmbient, hmax⟩
  have hrDvd : r ∣ fordUpperPrimePart n p := by
    exact Finset.dvd_prod_of_mem id hrAbove
  have hbPos := fordUpperPrimePart_pos n p
  exact hmax.trans_le (Nat.le_of_dvd hbPos hrDvd)

/-- A squarefree divisor-event integer belongs to the actual rough shell
at the largest prime of the selected divisor.  This is the finite covering
statement to which `card_roughProductShell_le_brun` applies. -/
theorem mem_roughProductShellValues_at_largestPrime
    {X₀ X₁ n m : ℕ} (hn : Squarefree n) (hm : m ∣ n) (hmOne : 1 < m)
    (hX₀ : X₀ < n) (hX₁ : n ≤ X₁) :
    n ∈ roughProductShellValues X₀ X₁
      (fordLowerPrimePart n (Erdos469.largestPrimeFactor m))
      (Erdos469.largestPrimeFactor m) := by
  let p := Erdos469.largestPrimeFactor m
  let a := fordLowerPrimePart n p
  let b := fordUpperPrimePart n p
  have hshell := squarefree_largestPrime_shell hn hm hmOne
  change n ∈ roughProductShellValues X₀ X₁ a p
  rw [roughProductShellValues, Finset.mem_image]
  refine ⟨b, ?_, ?_⟩
  · rw [mem_roughProductShell]
    have hbLeN : b ≤ n := by
      have hbDvd : b ∣ n := by
        use a * p
        simpa [mul_assoc, mul_comm, mul_left_comm] using hshell.2.2.2.2.1
      exact Nat.le_of_dvd (by omega) hbDvd
    refine ⟨hshell.2.2.2.1, hbLeN.trans hX₁,
      hshell.2.2.2.2.2.1, ?_, ?_⟩
    · rw [← hshell.2.2.2.2.1]
      exact hX₀
    · rw [← hshell.2.2.2.2.1]
      exact hX₁
  · exact hshell.2.2.2.2.1.symm

/-! ## The literal finite squarefree shell cover -/

/-- Squarefree integers in `(X₀,X₁]` which have a divisor in `(y,z]`. -/
def squarefreeDivisorShell (X₀ X₁ y z : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc X₀ X₁).filter fun n ↦
    Squarefree n ∧ 0 < divisorCountIoc y z n

theorem mem_squarefreeDivisorShell {X₀ X₁ y z n : ℕ} :
    n ∈ squarefreeDivisorShell X₀ X₁ y z ↔
      X₀ < n ∧ n ≤ X₁ ∧ Squarefree n ∧
        0 < divisorCountIoc y z n := by
  classical
  simp [squarefreeDivisorShell, and_assoc]

/-- All `(a,p)` shells obtained by marking the largest prime of an actual
divisor witness.  Keeping this as a finite image is important: the ensuing
union estimate is a theorem about literal finite sets, not an asymptotic
covering assertion. -/
def fordLargestPrimeShellPairs (X₁ y z : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((((Finset.Ioc 0 X₁).filter Squarefree).sigma fun n ↦
      (Finset.Ioc y z).filter fun m ↦ m ∣ n ∧ 1 < m).image fun nm ↦
        (fordLowerPrimePart nm.1 (Erdos469.largestPrimeFactor nm.2),
          Erdos469.largestPrimeFactor nm.2))

theorem fordLargestPrimeShellPairs_fst_pos
    {X₁ y z : ℕ} {ap : ℕ × ℕ}
    (hap : ap ∈ fordLargestPrimeShellPairs X₁ y z) :
    0 < ap.1 := by
  classical
  rw [fordLargestPrimeShellPairs, Finset.mem_image] at hap
  obtain ⟨⟨n, m⟩, hnm, rfl⟩ := hap
  exact fordLowerPrimePart_pos n (Erdos469.largestPrimeFactor m)

theorem fordLargestPrimeShellPairs_snd_prime
    {X₁ y z : ℕ} {ap : ℕ × ℕ}
    (hap : ap ∈ fordLargestPrimeShellPairs X₁ y z) :
    ap.2.Prime := by
  classical
  rw [fordLargestPrimeShellPairs, Finset.mem_image] at hap
  obtain ⟨⟨n, m⟩, hnm, rfl⟩ := hap
  have hmData := Finset.mem_filter.mp (Finset.mem_sigma.mp hnm).2
  exact (Erdos469.largestPrimeFactor_spec hmData.2.2).prime

theorem fordLargestPrimeShellPairs_snd_two_le
    {X₁ y z : ℕ} {ap : ℕ × ℕ}
    (hap : ap ∈ fordLargestPrimeShellPairs X₁ y z) :
    2 ≤ ap.2 :=
  (fordLargestPrimeShellPairs_snd_prime hap).two_le

/-- Every squarefree divisor-event integer in one dyadic shell is covered
by a largest-prime/rough-residual shell. -/
theorem squarefreeDivisorShell_subset_roughProductShellUnion
    {X₀ X₁ y z : ℕ} (hy : 1 ≤ y) :
    squarefreeDivisorShell X₀ X₁ y z ⊆
      roughProductShellUnion X₀ X₁
        (fordLargestPrimeShellPairs X₁ y z) := by
  classical
  intro n hn
  have hnData := mem_squarefreeDivisorShell.mp hn
  rw [divisorCountIoc, Finset.card_pos] at hnData
  obtain ⟨m, hm⟩ := hnData.2.2.2
  have hmData := Finset.mem_filter.mp hm
  have hmOne : 1 < m := hy.trans_lt (Finset.mem_Ioc.mp hmData.1).1
  let p := Erdos469.largestPrimeFactor m
  let a := fordLowerPrimePart n p
  rw [roughProductShellUnion, Finset.mem_biUnion]
  refine ⟨(a, p), ?_, ?_⟩
  · rw [fordLargestPrimeShellPairs, Finset.mem_image]
    refine ⟨⟨n, m⟩, ?_, rfl⟩
    rw [Finset.mem_sigma]
    exact ⟨Finset.mem_filter.mpr
        ⟨Finset.mem_Ioc.mpr
          ⟨Nat.zero_lt_of_lt hnData.1, hnData.2.1⟩, hnData.2.2.1⟩,
      Finset.mem_filter.mpr ⟨hmData.1, hmData.2, hmOne⟩⟩
  · exact mem_roughProductShellValues_at_largestPrime hnData.2.2.1
      hmData.2 hmOne hnData.1 hnData.2.1

/-- Ford's squarefree shell reduction followed by the exact finite Brun
upper sieve.  The only displayed hypotheses are the standard finite Brun
truncation inequality, uniformly for the finitely many generated shells. -/
theorem card_squarefreeDivisorShell_le_brun
    {X₀ X₁ y z L : ℕ}
    (hX : X₀ ≤ X₁) (hy : 1 ≤ y) (hL : Even L)
    (htail : ∀ ap ∈ fordLargestPrimeShellPairs X₁ y z,
      2 * Erdos387.brunSubsetTail
          (Erdos387.sievePrimeProduct 1 ap.2).primeFactors
          (fun q ↦ Erdos387.binomialSieveNu 1 q) L ≤
        Erdos387.finiteEulerProduct
          (Erdos387.sievePrimeProduct 1 ap.2).primeFactors
          (fun q ↦ Erdos387.binomialSieveNu 1 q)) :
    ((squarefreeDivisorShell X₀ X₁ y z).card : ℝ) ≤
      ∑ ap ∈ fordLargestPrimeShellPairs X₁ y z,
        (((X₁ / (ap.1 * ap.2) - X₀ / (ap.1 * ap.2) : ℕ) : ℝ) *
            (3 / (2 * Real.log (ap.2 : ℝ))) +
          2 * (ap.2 ^ L + 1 : ℕ)) := by
  calc
    ((squarefreeDivisorShell X₀ X₁ y z).card : ℝ) ≤
        ((roughProductShellUnion X₀ X₁
          (fordLargestPrimeShellPairs X₁ y z)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card
        (squarefreeDivisorShell_subset_roughProductShellUnion hy)
    _ ≤ ∑ ap ∈ fordLargestPrimeShellPairs X₁ y z,
        (((X₁ / (ap.1 * ap.2) - X₀ / (ap.1 * ap.2) : ℕ) : ℝ) *
            (3 / (2 * Real.log (ap.2 : ℝ))) +
          2 * (ap.2 ^ L + 1 : ℕ)) :=
      card_roughProductShellUnion_le_brun hX
        (fun ap hap ↦ fordLargestPrimeShellPairs_fst_pos hap)
        (fun ap hap ↦ fordLargestPrimeShellPairs_snd_two_le hap)
        hL htail

/-! ## Canonical Ford pairs -/

/-- The enlarged canonical family occurring in Ford's two-variable shell
sum.  Unlike `fordLargestPrimeShellPairs`, its definition no longer mentions
the ambient integer `n`; it retains exactly the conditions needed for the
prime-window and cluster estimates. -/
def fordAdmissibleLargestPrimePairs (X y z : ℕ) : Finset (ℕ × ℕ) := by
  classical
  exact ((Finset.Icc 1 X ×ˢ Nat.primesLE z).filter fun ap ↦
    Squarefree ap.1 ∧
      (∀ q : ℕ, q.Prime → q ∣ ap.1 → q < ap.2) ∧
      ap.1 * ap.2 ≤ X ∧
      ∃ f ∈ ap.1.divisors,
        y < f * ap.2 ∧ f * ap.2 ≤ z)

theorem mem_fordAdmissibleLargestPrimePairs
    {X y z a p : ℕ} :
    (a, p) ∈ fordAdmissibleLargestPrimePairs X y z ↔
      1 ≤ a ∧ a ≤ X ∧ p ≤ z ∧ p.Prime ∧ Squarefree a ∧
        (∀ q : ℕ, q.Prime → q ∣ a → q < p) ∧
        a * p ≤ X ∧
        ∃ f ∈ a.divisors, y < f * p ∧ f * p ≤ z := by
  classical
  simp [fordAdmissibleLargestPrimePairs, Nat.mem_primesLE,
    and_assoc]

theorem fordLargestPrimeShellPairs_subset_admissible
    {X y z : ℕ} :
    fordLargestPrimeShellPairs X y z ⊆
      fordAdmissibleLargestPrimePairs X y z := by
  classical
  intro ap hap
  rw [fordLargestPrimeShellPairs, Finset.mem_image] at hap
  obtain ⟨⟨n, m⟩, hnm, rfl⟩ := hap
  have hnData := Finset.mem_filter.mp (Finset.mem_sigma.mp hnm).1
  have hmData := Finset.mem_filter.mp (Finset.mem_sigma.mp hnm).2
  have hnIoc := Finset.mem_Ioc.mp hnData.1
  have hnPos : 0 < n := Nat.zero_lt_of_lt hnIoc.1
  have hmOne : 1 < m := hmData.2.2
  let p := Erdos469.largestPrimeFactor m
  let a := fordLowerPrimePart n p
  let b := fordUpperPrimePart n p
  have hpSpec : Erdos469.IsLargestPrimeFactor m p :=
    Erdos469.largestPrimeFactor_spec hmOne
  have hshell := squarefree_largestPrime_shell hnData.2 hmData.2.1 hmOne
  have hapDvd : a * p ∣ n := by
    use b
    exact hshell.2.2.2.2.1
  have haDvd : a ∣ n := (dvd_mul_right a p).trans hapDvd
  have haLeN : a ≤ n := Nat.le_of_dvd hnPos haDvd
  have hapLeN : a * p ≤ n := Nat.le_of_dvd hnPos hapDvd
  have hpLeM : p ≤ m := Nat.le_of_dvd (by omega) hpSpec.dvd
  rw [mem_fordAdmissibleLargestPrimePairs]
  refine ⟨hshell.2.2.1, haLeN.trans hnIoc.2,
    hpLeM.trans (Finset.mem_Ioc.mp hmData.1).2, hshell.1,
    hnData.2.squarefree_of_dvd haDvd, ?_,
    hapLeN.trans hnIoc.2, ?_⟩
  · intro q hqPrime hqa
    exact prime_lt_of_dvd_fordLowerPrimePart hqPrime hqa
  · refine ⟨m / p, hshell.2.2.2.2.2.2.1, ?_, ?_⟩
    · rw [← hshell.2.2.2.2.2.2.2]
      exact (Finset.mem_Ioc.mp hmData.1).1
    · rw [← hshell.2.2.2.2.2.2.2]
      exact (Finset.mem_Ioc.mp hmData.1).2

theorem fordAdmissibleLargestPrimePairs_fst_pos
    {X y z : ℕ} {ap : ℕ × ℕ}
    (hap : ap ∈ fordAdmissibleLargestPrimePairs X y z) :
    0 < ap.1 := by
  rcases ap with ⟨a, p⟩
  exact (mem_fordAdmissibleLargestPrimePairs.mp hap).1

theorem fordAdmissibleLargestPrimePairs_snd_two_le
    {X y z : ℕ} {ap : ℕ × ℕ}
    (hap : ap ∈ fordAdmissibleLargestPrimePairs X y z) :
    2 ≤ ap.2 := by
  rcases ap with ⟨a, p⟩
  exact (mem_fordAdmissibleLargestPrimePairs.mp hap).2.2.2.1.two_le

/-- The prime support of the smooth factor is a support in the cutoff
powerset which defines `squarefreeClusterMass`. -/
theorem primeFactors_mem_cutoff_powerset_of_admissible
    {X y z a p : ℕ}
    (hap : (a, p) ∈ fordAdmissibleLargestPrimePairs X y z) :
    a.primeFactors ∈ (primesUpTo z).powerset := by
  rw [Finset.mem_powerset]
  intro q hq
  have hdata := mem_fordAdmissibleLargestPrimePairs.mp hap
  have hqPrime := Nat.prime_of_mem_primeFactors hq
  have hqLt : q < p := hdata.2.2.2.2.2.1 q hqPrime
    (Nat.dvd_of_mem_primeFactors hq)
  rw [primesUpTo, Finset.mem_filter, Finset.mem_Icc]
  exact ⟨⟨hqPrime.two_le, hqLt.le.trans hdata.2.2.1⟩, hqPrime⟩

/-- On an admissible pair, the prime-support reciprocal cluster term is
literally `L(a)/a`. -/
theorem primeSubsetClusterTerm_primeFactors_of_admissible
    {X y z a p : ℕ}
    (hap : (a, p) ∈ fordAdmissibleLargestPrimePairs X y z) :
    primeSubsetClusterTerm a.primeFactors =
      clusterLength a / (a : ℝ) := by
  have haSq :=
    (mem_fordAdmissibleLargestPrimePairs.mp hap).2.2.2.2.1
  unfold primeSubsetClusterTerm
  have hprod : a.primeFactors.prod id = a := by
    simpa using Nat.prod_primeFactors_of_squarefree haSq
  rw [hprod]

/-- The selected divisor says exactly that the translated prime coordinate
`log(y/p)` lies in the logarithmic divisor cluster of `a`.  This is the
arithmetic input of Ford's short reciprocal-prime window estimate (28d). -/
theorem log_div_prime_mem_divisorCluster_of_admissible
    {X y a p : ℕ} (hy : 0 < y)
    (hap : (a, p) ∈ fordAdmissibleLargestPrimePairs X y (2 * y)) :
    Real.log ((y : ℝ) / (p : ℝ)) ∈ divisorCluster a := by
  have hdata := mem_fordAdmissibleLargestPrimePairs.mp hap
  obtain ⟨f, hf, hyfp, hfp2y⟩ := hdata.2.2.2.2.2.2.2
  have hfPos := Nat.pos_of_mem_divisors hf
  have hpPos := hdata.2.2.2.1.pos
  have hyR : (0 : ℝ) < y := by exact_mod_cast hy
  have hfR : (0 : ℝ) < f := by exact_mod_cast hfPos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hpPos
  have htwoR : (0 : ℝ) < (2 : ℝ) := by norm_num
  have hltR : (y : ℝ) < (f : ℝ) * (p : ℝ) := by
    exact_mod_cast hyfp
  have hleR : (f : ℝ) * (p : ℝ) ≤ (2 : ℝ) * (y : ℝ) := by
    exact_mod_cast hfp2y
  have hlogLt : Real.log (y : ℝ) <
      Real.log ((f : ℝ) * (p : ℝ)) :=
    Real.strictMonoOn_log (by simpa only [Set.mem_Ioi] using hyR)
      (by simpa only [Set.mem_Ioi] using mul_pos hfR hpR) hltR
  have hlogLe : Real.log ((f : ℝ) * (p : ℝ)) ≤
      Real.log ((2 : ℝ) * (y : ℝ)) :=
    Real.strictMonoOn_log.monotoneOn
      (by simpa only [Set.mem_Ioi] using mul_pos hfR hpR)
      (by simpa only [Set.mem_Ioi] using mul_pos htwoR hyR) hleR
  rw [Real.log_mul hfR.ne' hpR.ne'] at hlogLt hlogLe
  rw [Real.log_mul htwoR.ne' hyR.ne'] at hlogLe
  rw [mem_divisorCluster_iff]
  refine ⟨f, hf, ?_, ?_⟩
  · rw [Real.log_div hyR.ne' hpR.ne']
    linarith
  · rw [Real.log_div hyR.ne' hpR.ne']
    linarith

/-- Canonical form of the finite squarefree shell cover. -/
theorem squarefreeDivisorShell_subset_admissibleRoughShellUnion
    {X₀ X₁ y z : ℕ} (hy : 1 ≤ y) :
    squarefreeDivisorShell X₀ X₁ y z ⊆
      roughProductShellUnion X₀ X₁
        (fordAdmissibleLargestPrimePairs X₁ y z) := by
  intro n hn
  have hn' := squarefreeDivisorShell_subset_roughProductShellUnion hy hn
  rw [roughProductShellUnion, Finset.mem_biUnion] at hn' ⊢
  obtain ⟨ap, hap, hnap⟩ := hn'
  exact ⟨ap, fordLargestPrimeShellPairs_subset_admissible hap, hnap⟩

/-- The literal squarefree divisor shell is bounded by Ford's canonical
`(a,p)` Brun sum.  This is the finite counting statement immediately before
the reciprocal-prime/cluster summation in Lemma 3.2. -/
theorem card_squarefreeDivisorShell_le_admissible_brun
    {X₀ X₁ y z L : ℕ}
    (hX : X₀ ≤ X₁) (hy : 1 ≤ y) (hL : Even L)
    (htail : ∀ ap ∈ fordAdmissibleLargestPrimePairs X₁ y z,
      2 * Erdos387.brunSubsetTail
          (Erdos387.sievePrimeProduct 1 ap.2).primeFactors
          (fun q ↦ Erdos387.binomialSieveNu 1 q) L ≤
        Erdos387.finiteEulerProduct
          (Erdos387.sievePrimeProduct 1 ap.2).primeFactors
          (fun q ↦ Erdos387.binomialSieveNu 1 q)) :
    ((squarefreeDivisorShell X₀ X₁ y z).card : ℝ) ≤
      ∑ ap ∈ fordAdmissibleLargestPrimePairs X₁ y z,
        (((X₁ / (ap.1 * ap.2) - X₀ / (ap.1 * ap.2) : ℕ) : ℝ) *
            (3 / (2 * Real.log (ap.2 : ℝ))) +
          2 * (ap.2 ^ L + 1 : ℕ)) := by
  calc
    ((squarefreeDivisorShell X₀ X₁ y z).card : ℝ) ≤
        ((roughProductShellUnion X₀ X₁
          (fordAdmissibleLargestPrimePairs X₁ y z)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card
        (squarefreeDivisorShell_subset_admissibleRoughShellUnion hy)
    _ ≤ ∑ ap ∈ fordAdmissibleLargestPrimePairs X₁ y z,
        (((X₁ / (ap.1 * ap.2) - X₀ / (ap.1 * ap.2) : ℕ) : ℝ) *
            (3 / (2 * Real.log (ap.2 : ℝ))) +
          2 * (ap.2 ^ L + 1 : ℕ)) :=
      card_roughProductShellUnion_le_brun hX
        (fun ap hap ↦ fordAdmissibleLargestPrimePairs_fst_pos hap)
        (fun ap hap ↦ fordAdmissibleLargestPrimePairs_snd_two_le hap)
        hL htail

end

end Erdos446
