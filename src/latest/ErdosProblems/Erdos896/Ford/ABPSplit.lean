/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.Defs

/-!
# The local `a b p` split in Ford's Lemma 3.2

This file isolates the elementary squarefree decomposition used in the proof
of (3.2) of Kevin Ford's *Integers with a divisor in (y, 2y]*.  If a
squarefree integer is written as `m₁ * m₂`, choose the factor whose largest
prime factor is smaller and call that prime `p`.  Repartition all remaining
prime factors of the integer at `p`: their products are `a` and `b`.

Thus every prime factor of `a` is smaller than `p`, every prime factor of `b`
is larger than `p`, and the chosen `mᵢ` is `d * p` for a divisor `d` of `a`.
The final lemma records the exact logarithmic-divisor-union consequence of a
dyadic window for `mᵢ`.
-/

namespace Erdos896.Ford

open scoped BigOperators

/-- Product of the prime factors of `n` strictly below `p`. -/
def primesBelowPart (n p : ℕ) : ℕ :=
  ∏ q ∈ n.primeFactors.filter (fun q ↦ q < p), q

/-- Product of the prime factors of `n` strictly above `p`. -/
def primesAbovePart (n p : ℕ) : ℕ :=
  ∏ q ∈ n.primeFactors.filter (fun q ↦ p < q), q

/-- The largest prime factor, with the harmless value `1` at `0` and `1`.

This definition is local to the arithmetic split, so `ABPSplit` depends only
on `Ford.Defs` and not on later analytic modules. -/
noncomputable def splitLargestPrime (n : ℕ) : ℕ :=
  if h : n.primeFactors.Nonempty then n.primeFactors.max' h else 1

theorem splitLargestPrime_mem {n : ℕ} (hn : 1 < n) :
    splitLargestPrime n ∈ n.primeFactors := by
  rw [splitLargestPrime]
  simp only [Nat.nonempty_primeFactors.mpr hn, dite_true]
  exact Finset.max'_mem _ _

theorem splitLargestPrime_prime {n : ℕ} (hn : 1 < n) :
    Nat.Prime (splitLargestPrime n) :=
  Nat.prime_of_mem_primeFactors (splitLargestPrime_mem hn)

theorem prime_le_splitLargestPrime {n q : ℕ} (hn : 1 < n)
    (hq : q ∈ n.primeFactors) : q ≤ splitLargestPrime n := by
  rw [splitLargestPrime]
  simp only [Nat.nonempty_primeFactors.mpr hn, dite_true]
  exact Finset.le_max' _ q hq

@[simp]
theorem primeFactors_primesBelowPart (n p : ℕ) :
    (primesBelowPart n p).primeFactors =
      n.primeFactors.filter (fun q ↦ q < p) := by
  apply Nat.primeFactors_prod
  intro q hq
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1

@[simp]
theorem primeFactors_primesAbovePart (n p : ℕ) :
    (primesAbovePart n p).primeFactors =
      n.primeFactors.filter (fun q ↦ p < q) := by
  apply Nat.primeFactors_prod
  intro q hq
  exact Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1

theorem primesBelowPart_pos (n p : ℕ) : 0 < primesBelowPart n p := by
  apply Finset.prod_pos
  intro q hq
  exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).pos

theorem primesAbovePart_pos (n p : ℕ) : 0 < primesAbovePart n p := by
  apply Finset.prod_pos
  intro q hq
  exact (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hq).1).pos

theorem primesBelowPart_dvd (n p : ℕ) : primesBelowPart n p ∣ n := by
  refine (Finset.prod_dvd_prod_of_subset
    (n.primeFactors.filter fun q ↦ q < p) n.primeFactors id
    (Finset.filter_subset _ _)).trans ?_
  exact Nat.prod_primeFactors_dvd n

theorem primesAbovePart_dvd (n p : ℕ) : primesAbovePart n p ∣ n := by
  refine (Finset.prod_dvd_prod_of_subset
    (n.primeFactors.filter fun q ↦ p < q) n.primeFactors id
    (Finset.filter_subset _ _)).trans ?_
  exact Nat.prod_primeFactors_dvd n

theorem squarefree_primesBelowPart {n p : ℕ} (hn : Squarefree n) :
    Squarefree (primesBelowPart n p) :=
  hn.squarefree_of_dvd (primesBelowPart_dvd n p)

theorem squarefree_primesAbovePart {n p : ℕ} (hn : Squarefree n) :
    Squarefree (primesAbovePart n p) :=
  hn.squarefree_of_dvd (primesAbovePart_dvd n p)

/-- The witness produced by Ford's local decomposition.  The field
`selected_eq` says that `selected` is the factor whose largest prime was
chosen.  The three coprimality fields make the squarefree support split
explicit rather than leaving it implicit in the prime inequalities. -/
structure ABPSplit (n selected : ℕ) where
  a : ℕ
  b : ℕ
  p : ℕ
  d : ℕ
  prime_p : Nat.Prime p
  n_eq : n = a * b * p
  selected_eq : selected = d * p
  d_dvd_a : d ∣ a
  squarefree_a : Squarefree a
  squarefree_b : Squarefree b
  coprime_ab : Nat.Coprime a b
  coprime_ap : Nat.Coprime a p
  coprime_bp : Nat.Coprime b p
  primes_a_lt : ∀ q ∈ a.primeFactors, q < p
  primes_b_gt : ∀ q ∈ b.primeFactors, p < q
  p_lt_b : p < b

private theorem primeFactor_partition {n p : ℕ} (hp : p ∈ n.primeFactors) :
    n.primeFactors =
      insert p (n.primeFactors.filter (fun q ↦ q < p) ∪
        n.primeFactors.filter (fun q ↦ p < q)) := by
  ext q
  by_cases hqp : q = p
  · subst q
    simp [hp]
  · simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_filter]
    constructor
    · intro hq
      have : q < p ∨ p < q := lt_or_gt_of_ne hqp
      tauto
    · tauto

private theorem squarefree_eq_parts {n p : ℕ} (hn : Squarefree n)
    (hp : p ∈ n.primeFactors) :
    n = primesBelowPart n p * primesAbovePart n p * p := by
  let A := n.primeFactors.filter (fun q ↦ q < p)
  let B := n.primeFactors.filter (fun q ↦ p < q)
  have hpA : p ∉ n.primeFactors.filter (fun q ↦ q < p) := by simp
  have hpB : p ∉ n.primeFactors.filter (fun q ↦ p < q) := by simp
  have hAB : Disjoint
      (n.primeFactors.filter (fun q ↦ q < p))
      (n.primeFactors.filter (fun q ↦ p < q)) := by
    simp only [Finset.disjoint_filter]
    omega
  have hpart : n.primeFactors = insert p (A ∪ B) := by
    simpa [A, B] using primeFactor_partition hp
  calc
    n = ∏ q ∈ n.primeFactors, q := (Nat.prod_primeFactors_of_squarefree hn).symm
    _ = ∏ q ∈ insert p (A ∪ B), q :=
      congrArg (fun S : Finset ℕ ↦ ∏ q ∈ S, q) hpart
    _ = p * ∏ q ∈ A ∪ B, q := by
      rw [Finset.prod_insert]
      simp [A, B]
    _ = p * ((∏ q ∈ A, q) * ∏ q ∈ B, q) := by
      rw [Finset.prod_union]
      simpa [A, B] using hAB
    _ = primesBelowPart n p * primesAbovePart n p * p := by
      simp [A, B, primesBelowPart, primesAbovePart, mul_comm]

private theorem coprime_parts (n p : ℕ) :
    Nat.Coprime (primesBelowPart n p) (primesAbovePart n p) := by
  rw [← Nat.disjoint_primeFactors
    (primesBelowPart_pos n p).ne' (primesAbovePart_pos n p).ne']
  simp only [primeFactors_primesBelowPart, primeFactors_primesAbovePart,
    Finset.disjoint_filter]
  omega

private theorem coprime_below_prime {n p : ℕ} (hp : Nat.Prime p) :
    Nat.Coprime (primesBelowPart n p) p := by
  rw [← Nat.disjoint_primeFactors (primesBelowPart_pos n p).ne' hp.ne_zero,
    primeFactors_primesBelowPart, hp.primeFactors]
  simp

private theorem coprime_above_prime {n p : ℕ} (hp : Nat.Prime p) :
    Nat.Coprime (primesAbovePart n p) p := by
  rw [← Nat.disjoint_primeFactors (primesAbovePart_pos n p).ne' hp.ne_zero,
    primeFactors_primesAbovePart, hp.primeFactors]
  simp

private theorem chosenRemainder_dvd_below
    {n selected other p : ℕ}
    (hn : Squarefree n) (hprod : selected * other = n)
    (hselected : 1 < selected)
    (hp : p = splitLargestPrime selected) :
    (∏ q ∈ selected.primeFactors.erase p, q) ∣ primesBelowPart n p := by
  apply Finset.prod_dvd_prod_of_subset
  intro q hq
  have hqsel : q ∈ selected.primeFactors := (Finset.mem_erase.mp hq).2
  have hqne : q ≠ p := (Finset.mem_erase.mp hq).1
  have hselected0 : selected ≠ 0 := by omega
  have hother0 : other ≠ 0 := by
    intro h
    apply hn.ne_zero
    rw [← hprod, h, Nat.mul_zero]
  have hqglobal : q ∈ n.primeFactors := by
    rw [← hprod, Nat.primeFactors_mul hselected0 hother0]
    exact Finset.mem_union_left _ hqsel
  apply Finset.mem_filter.mpr
  refine ⟨hqglobal, ?_⟩
  have hqle : q ≤ p := by
    rw [hp]
    exact prime_le_splitLargestPrime hselected hqsel
  omega

private theorem abovePart_gt_of_primeFactor
    {n p q : ℕ} (hq : q ∈ n.primeFactors) (hpq : p < q) :
    p < primesAbovePart n p := by
  have hqmem : q ∈ n.primeFactors.filter (fun r ↦ p < r) :=
    Finset.mem_filter.mpr ⟨hq, hpq⟩
  have hqdvd : q ∣ primesAbovePart n p := by
    exact Finset.dvd_prod_of_mem id hqmem
  exact hpq.trans_le (Nat.le_of_dvd (primesAbovePart_pos n p) hqdvd)

/-- The ordered form of Ford's local split.  The selected factor is the one
with smaller largest prime factor. -/
theorem abpSplit_of_ordered_factorization
    {n selected other : ℕ}
    (hn : Squarefree n)
    (hprod : selected * other = n)
    (hselected : 1 < selected)
    (hother : 1 < other)
    (hmax : splitLargestPrime selected < splitLargestPrime other) :
    Nonempty (ABPSplit n selected) := by
  let p := splitLargestPrime selected
  let a := primesBelowPart n p
  let b := primesAbovePart n p
  let d := ∏ q ∈ selected.primeFactors.erase p, q
  have hpMemSelected : p ∈ selected.primeFactors := by
    simpa [p] using splitLargestPrime_mem hselected
  have hpPrime : Nat.Prime p := by
    simpa [p] using splitLargestPrime_prime hselected
  have hselected0 : selected ≠ 0 := by omega
  have hother0 : other ≠ 0 := by omega
  have hpMemGlobal : p ∈ n.primeFactors := by
    rw [← hprod, Nat.primeFactors_mul hselected0 hother0]
    exact Finset.mem_union_left _ hpMemSelected
  have hnParts : n = a * b * p := by
    simpa [a, b] using squarefree_eq_parts hn hpMemGlobal
  have hsqprod : Squarefree (selected * other) := by simpa [hprod] using hn
  have hselectedSq : Squarefree selected := (Nat.squarefree_mul_iff.mp hsqprod).2.1
  have hselectedEq : selected = d * p := by
    dsimp [d]
    symm
    calc
      (∏ q ∈ selected.primeFactors.erase p, q) * p =
          ∏ q ∈ selected.primeFactors, q := by
            simpa using Finset.prod_erase_mul selected.primeFactors id hpMemSelected
      _ = selected := Nat.prod_primeFactors_of_squarefree hselectedSq
  have hdDvd : d ∣ a := by
    simpa [a, d, p] using
      (chosenRemainder_dvd_below hn hprod hselected rfl)
  have hqMemOther : splitLargestPrime other ∈ other.primeFactors :=
    splitLargestPrime_mem hother
  have hqMemGlobal : splitLargestPrime other ∈ n.primeFactors := by
    rw [← hprod, Nat.primeFactors_mul hselected0 hother0]
    exact Finset.mem_union_right _ hqMemOther
  refine ⟨
    { a := a
      b := b
      p := p
      d := d
      prime_p := hpPrime
      n_eq := hnParts
      selected_eq := hselectedEq
      d_dvd_a := hdDvd
      squarefree_a := by simpa [a] using squarefree_primesBelowPart hn
      squarefree_b := by simpa [b] using squarefree_primesAbovePart hn
      coprime_ab := by simpa [a, b] using coprime_parts n p
      coprime_ap := by simpa [a] using coprime_below_prime (n := n) hpPrime
      coprime_bp := by simpa [b] using coprime_above_prime (n := n) hpPrime
      primes_a_lt := by
        intro q hq
        change q ∈ (primesBelowPart n p).primeFactors at hq
        rw [primeFactors_primesBelowPart] at hq
        exact (Finset.mem_filter.mp hq).2
      primes_b_gt := by
        intro q hq
        change q ∈ (primesAbovePart n p).primeFactors at hq
        rw [primeFactors_primesAbovePart] at hq
        exact (Finset.mem_filter.mp hq).2
      p_lt_b := by
        apply abovePart_gt_of_primeFactor hqMemGlobal
        simpa [p] using hmax }⟩

/-- Given a nontrivial squarefree factorization, exactly one side has the
smaller largest prime factor, and that side admits Ford's `a b p` split. -/
theorem abpSplit_of_squarefree_factorization
    {n m₁ m₂ : ℕ}
    (hn : Squarefree n)
    (hprod : m₁ * m₂ = n)
    (hm₁ : 1 < m₁)
    (hm₂ : 1 < m₂) :
    Nonempty (ABPSplit n m₁) ∨ Nonempty (ABPSplit n m₂) := by
  have hsqprod : Squarefree (m₁ * m₂) := by simpa [hprod] using hn
  have hcop : Nat.Coprime m₁ m₂ := Nat.coprime_of_squarefree_mul hsqprod
  have hne : splitLargestPrime m₁ ≠ splitLargestPrime m₂ := by
    intro heq
    have hmem₁ := splitLargestPrime_mem hm₁
    have hmem₂ := splitLargestPrime_mem hm₂
    exact (Finset.disjoint_left.mp hcop.disjoint_primeFactors hmem₁)
      (heq ▸ hmem₂)
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact Or.inl (abpSplit_of_ordered_factorization hn hprod hm₁ hm₂ hlt)
  · exact Or.inr (abpSplit_of_ordered_factorization hn
      (by simpa [mul_comm] using hprod) hm₂ hm₁ hgt)

/-- A dyadic window for the selected factor puts the corresponding logarithm
in Ford's logarithmic divisor union.  The natural inequalities avoid all
rounding issues; the conclusion is the exact real point
`log ((c*y)/p) ∈ ℒ(a; log 2)`. -/
theorem ABPSplit.log_mem_logDivisorUnion
    {n selected c y : ℕ} (w : ABPSplit n selected)
    (hc : 0 < c) (hy : 0 < y)
    (hlower : c * y < selected)
    (hupper : selected ≤ 2 * (c * y)) :
    Real.log (((c * y : ℕ) : ℝ) / (w.p : ℝ)) ∈
      logDivisorUnion w.a (Real.log 2) := by
  rw [mem_logDivisorUnion]
  have ha0 : w.a ≠ 0 := w.squarefree_a.ne_zero
  have hdMem : w.d ∈ w.a.divisors :=
    Nat.mem_divisors.mpr ⟨w.d_dvd_a, ha0⟩
  have hpR : (0 : ℝ) < w.p := by exact_mod_cast w.prime_p.pos
  have hcyR : (0 : ℝ) < (c * y : ℕ) := by exact_mod_cast Nat.mul_pos hc hy
  have hdR : (0 : ℝ) < w.d := by
    have hspos : 0 < selected := by omega
    have hdp : 0 < w.d * w.p := by simpa [← w.selected_eq] using hspos
    exact_mod_cast (pos_of_mul_pos_left hdp (Nat.zero_le w.p) : 0 < w.d)
  have hlowerR : ((c * y : ℕ) : ℝ) < (w.d : ℝ) * (w.p : ℝ) := by
    exact_mod_cast (by simpa [w.selected_eq] using hlower)
  have hupperR : (w.d : ℝ) * (w.p : ℝ) ≤ 2 * ((c * y : ℕ) : ℝ) := by
    exact_mod_cast (by simpa [w.selected_eq] using hupper)
  refine ⟨w.d, hdMem, ?_, ?_⟩
  · rw [Real.log_div (by positivity) (by positivity)]
    have hlog := Real.strictMonoOn_log.monotoneOn
      (by positivity : (0 : ℝ) < (w.d : ℝ) * w.p)
      (by positivity : (0 : ℝ) < 2 * ((c * y : ℕ) : ℝ)) hupperR
    rw [Real.log_mul (by positivity) (by positivity)] at hlog
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)] at hlog
    linarith
  · rw [Real.log_div (by positivity) (by positivity)]
    have hlog := Real.strictMonoOn_log hcyR (mul_pos hdR hpR) hlowerR
    rw [Real.log_mul (by positivity) (by positivity)] at hlog
    linarith

end Erdos896.Ford
