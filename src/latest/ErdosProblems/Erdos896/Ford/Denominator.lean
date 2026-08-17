/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos896.Ford.Measure
import ErdosProblems.Erdos896.Ford.PrimeEstimates

/-!
# Removing Ford's logarithmic denominator

This file proves the `h = 2` specialization of Lemma 3.3 in Kevin Ford's
short paper *Integers with a divisor in (y, 2y]*.  This is the only
specialization used in the proof of the multiplication-table estimate.

Ford writes `P(x)` for the (finite) family of squarefree integers all of
whose prime factors are at most `x`.  We index that family by subsets of
`Nat.primesLE x`; unique factorization makes this an exact, duplication-free
parametrization.  The result below is the source-faithful estimate

`sum L(a) / (a log(P⁺(a) + x/a)^2)
    = O((log x)^(-2) sum L(a)/a)`.
-/

namespace Erdos896.Ford

open Filter Asymptotics
open scoped BigOperators

/-- The largest prime factor, with Ford's convention `P⁺(1) = 1` (and the
same harmless convention at zero). -/
noncomputable def largestPrimeFactor (n : ℕ) : ℕ :=
  if h : n.primeFactors.Nonempty then n.primeFactors.max' h else 1

@[simp]
theorem largestPrimeFactor_one : largestPrimeFactor 1 = 1 := by
  simp [largestPrimeFactor]

theorem largestPrimeFactor_eq_max' {n : ℕ} (hn : 1 < n) :
    largestPrimeFactor n =
      n.primeFactors.max' (Nat.nonempty_primeFactors.mpr hn) := by
  simp [largestPrimeFactor, Nat.nonempty_primeFactors.mpr hn]

theorem largestPrimeFactor_mem {n : ℕ} (hn : 1 < n) :
    largestPrimeFactor n ∈ n.primeFactors := by
  rw [largestPrimeFactor_eq_max' hn]
  exact Finset.max'_mem _ _

theorem largestPrimeFactor_prime {n : ℕ} (hn : 1 < n) :
    Nat.Prime (largestPrimeFactor n) :=
  Nat.prime_of_mem_primeFactors (largestPrimeFactor_mem hn)

theorem prime_le_largestPrimeFactor {n q : ℕ} (hn : 1 < n)
    (hq : q ∈ n.primeFactors) : q ≤ largestPrimeFactor n := by
  rw [largestPrimeFactor_eq_max' hn]
  exact Finset.le_max' _ q hq

/-- Ford's squarefree prime-product family, indexed without duplication by
subsets of the primes at most `x`. -/
def fordPrimeSubsets (x : ℕ) : Finset (Finset ℕ) :=
  (Nat.primesLE x).powerset

/-- The integer represented by a prime subset. -/
def primeSubsetProd (s : Finset ℕ) : ℕ :=
  ∏ p ∈ s, p

/-- The unweighted finite sum on the right of Ford's Lemma 3.3, specialized
to the divisor-union measure `L(a; log 2)`. -/
noncomputable def fordWeightSum (x : ℕ) : ℝ :=
  ∑ s ∈ fordPrimeSubsets x,
    L (primeSubsetProd s) (Real.log 2) / (primeSubsetProd s : ℝ)

/-- The logarithmically weighted sum on the left of Ford's Lemma 3.3 for
`h = 2`. -/
noncomputable def fordDenominatorSum (x : ℕ) : ℝ :=
  ∑ s ∈ fordPrimeSubsets x,
    L (primeSubsetProd s) (Real.log 2) /
      ((primeSubsetProd s : ℝ) *
        Real.log ((largestPrimeFactor (primeSubsetProd s) : ℝ) +
          (x : ℝ) / primeSubsetProd s) ^ 2)

/-- A summand on the right side of the denominator-removal estimate. -/
noncomputable def fordWeight (s : Finset ℕ) : ℝ :=
  L (primeSubsetProd s) (Real.log 2) / (primeSubsetProd s : ℝ)

/-- A summand on the left side of the denominator-removal estimate. -/
noncomputable def fordDenominatorTerm (x : ℕ) (s : Finset ℕ) : ℝ :=
  L (primeSubsetProd s) (Real.log 2) /
    ((primeSubsetProd s : ℝ) *
      Real.log ((largestPrimeFactor (primeSubsetProd s) : ℝ) +
        (x : ℝ) / primeSubsetProd s) ^ 2)

/-- Ford's exceptional range `a > sqrt x`, `P⁺(a) ≤ x^(1/4)`, written
without real roots. -/
def denominatorBad (x : ℕ) (s : Finset ℕ) : Prop :=
  x < primeSubsetProd s ^ 2 ∧ largestPrimeFactor (primeSubsetProd s) ^ 4 ≤ x

noncomputable instance (x : ℕ) : DecidablePred (denominatorBad x) :=
  Classical.decPred _

theorem fordWeightSum_eq (x : ℕ) :
    fordWeightSum x = ∑ s ∈ fordPrimeSubsets x, fordWeight s := by
  rfl

theorem fordDenominatorSum_eq (x : ℕ) :
    fordDenominatorSum x =
      ∑ s ∈ fordPrimeSubsets x, fordDenominatorTerm x s := by
  rfl

private theorem primesLE_prime {x p : ℕ} (hp : p ∈ Nat.primesLE x) : p.Prime :=
  Nat.prime_of_mem_primesLE hp

private theorem prod_primeSubsets_injective (x : ℕ) :
    Set.InjOn primeSubsetProd (fordPrimeSubsets x) := by
  intro s hs t ht hst
  have hs' : s ⊆ Nat.primesLE x := Finset.mem_powerset.mp hs
  have ht' : t ⊆ Nat.primesLE x := Finset.mem_powerset.mp ht
  simp only [primeSubsetProd] at hst ⊢
  rw [← Nat.primeFactors_prod (fun p hp ↦ primesLE_prime (hs' hp)),
    ← Nat.primeFactors_prod (fun p hp ↦ primesLE_prime (ht' hp))]
  exact congrArg Nat.primeFactors hst

private theorem prod_primeSubset_pos {x : ℕ} {s : Finset ℕ}
    (hs : s ∈ fordPrimeSubsets x) : 0 < primeSubsetProd s := by
  unfold primeSubsetProd
  apply Finset.prod_pos
  intro p hp
  exact (primesLE_prime (Finset.mem_powerset.mp hs hp)).pos

private theorem prod_primeSubset_squarefree {x : ℕ} {s : Finset ℕ}
    (hs : s ∈ fordPrimeSubsets x) : Squarefree (primeSubsetProd s) := by
  unfold primeSubsetProd
  refine Finset.squarefree_prod_of_pairwise_isCoprime (fun p hp q hq hpq ↦ ?_)
    fun p hp ↦ (primesLE_prime (Finset.mem_powerset.mp hs hp)).squarefree
  simp only [← Nat.coprime_iff_isRelPrime]
  exact (Nat.coprime_primes
    (primesLE_prime (Finset.mem_powerset.mp hs hp))
    (primesLE_prime (Finset.mem_powerset.mp hs hq))).mpr hpq

private theorem primeFactors_primeSubsetProd {x : ℕ} {s : Finset ℕ}
    (hs : s ∈ fordPrimeSubsets x) :
    (primeSubsetProd s).primeFactors = s := by
  unfold primeSubsetProd
  exact Nat.primeFactors_prod fun p hp ↦
    primesLE_prime (Finset.mem_powerset.mp hs hp)

private theorem one_lt_primeSubsetProd {x : ℕ} {s : Finset ℕ}
    (hs : s ∈ fordPrimeSubsets x) (hsne : s.Nonempty) :
    1 < primeSubsetProd s := by
  rw [← Nat.nonempty_primeFactors, primeFactors_primeSubsetProd hs]
  exact hsne

private theorem largestPrimeFactor_primeSubsetProd {x : ℕ} {s : Finset ℕ}
    (hs : s ∈ fordPrimeSubsets x) (hsne : s.Nonempty) :
    largestPrimeFactor (primeSubsetProd s) = s.max' hsne := by
  rw [largestPrimeFactor_eq_max' (one_lt_primeSubsetProd hs hsne)]
  have hpf := primeFactors_primeSubsetProd hs
  simp [hpf]

private theorem fordWeight_nonneg (s : Finset ℕ) : 0 ≤ fordWeight s := by
  exact div_nonneg (L_nonneg _ _) (Nat.cast_nonneg _)

private theorem fordDenominatorTerm_nonneg (x : ℕ) (s : Finset ℕ) :
    0 ≤ fordDenominatorTerm x s := by
  unfold fordDenominatorTerm
  exact div_nonneg (L_nonneg _ _)
    (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _))

private theorem log_x_le_four_mul_log_fordArgument
    {x : ℕ} (hx : 2 ≤ x) {s : Finset ℕ} (hs : s ∈ fordPrimeSubsets x)
    (hgood : ¬denominatorBad x s) :
    Real.log x ≤ 4 * Real.log
      ((largestPrimeFactor (primeSubsetProd s) : ℝ) +
        (x : ℝ) / primeSubsetProd s) := by
  let a := primeSubsetProd s
  let p := largestPrimeFactor a
  have hxposN : 0 < x := by omega
  have hxpos : (0 : ℝ) < x := by exact_mod_cast hxposN
  have hlogx0 : 0 ≤ Real.log x :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ x by omega))
  have haposN : 0 < a := by simpa [a] using prod_primeSubset_pos hs
  have hapos : (0 : ℝ) < a := by exact_mod_cast haposN
  by_cases hs0 : s = ∅
  · subst s
    have harg : (x : ℝ) ≤ (1 : ℝ) + x := by linarith
    have hlog : Real.log x ≤ Real.log ((1 : ℝ) + x) :=
      Real.log_le_log hxpos harg
    simp only [primeSubsetProd, Finset.prod_empty, largestPrimeFactor_one,
      Nat.cast_one, div_one]
    nlinarith [Real.log_nonneg (show (1 : ℝ) ≤ 1 + x by linarith)]
  · have hsne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hs0
    have hpEq : p = s.max' hsne := by
      simpa [p, a] using largestPrimeFactor_primeSubsetProd hs hsne
    have hpMem : p ∈ s := by rw [hpEq]; exact Finset.max'_mem _ _
    have hpPrime : p.Prime := primesLE_prime (Finset.mem_powerset.mp hs hpMem)
    have hppos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
    by_cases ha2 : a ^ 2 ≤ x
    · have ha2R : (a : ℝ) ^ 2 ≤ (x : ℝ) := by exact_mod_cast ha2
      have hlogpow : 2 * Real.log (a : ℝ) ≤ Real.log x := by
        have ht := Real.log_le_log (sq_pos_of_pos hapos) ha2R
        simpa [Real.log_pow] using ht
      have hdivpos : (0 : ℝ) < (x : ℝ) / a := div_pos hxpos hapos
      have hdivle : (x : ℝ) / a ≤ (p : ℝ) + (x : ℝ) / a := by
        linarith
      have hlogdiv : Real.log ((x : ℝ) / a) ≤
          Real.log ((p : ℝ) + (x : ℝ) / a) :=
        Real.log_le_log hdivpos hdivle
      rw [Real.log_div hxpos.ne' hapos.ne'] at hlogdiv
      simpa [a, p] using (show Real.log x ≤
          4 * Real.log ((p : ℝ) + (x : ℝ) / a) by linarith)
    · have hp4 : x < p ^ 4 := by
        by_contra hp4not
        apply hgood
        simpa [denominatorBad, a, p] using
          (show x < a ^ 2 ∧ p ^ 4 ≤ x from
            ⟨Nat.lt_of_not_ge ha2, Nat.le_of_not_gt hp4not⟩)
      have hp4R : (x : ℝ) < (p : ℝ) ^ 4 := by exact_mod_cast hp4
      have hlogpow : Real.log x < 4 * Real.log (p : ℝ) := by
        have ht := Real.log_lt_log hxpos hp4R
        simpa [Real.log_pow] using ht
      have hple : (p : ℝ) ≤ (p : ℝ) + (x : ℝ) / a :=
        le_add_of_nonneg_right (div_nonneg hxpos.le hapos.le)
      have hlogp : Real.log (p : ℝ) ≤
          Real.log ((p : ℝ) + (x : ℝ) / a) :=
        Real.log_le_log hppos hple
      simpa [a, p] using (show Real.log x ≤
          4 * Real.log ((p : ℝ) + (x : ℝ) / a) by linarith)

private theorem fordDenominatorTerm_le_of_not_bad
    {x : ℕ} (hx : 2 ≤ x) {s : Finset ℕ} (hs : s ∈ fordPrimeSubsets x)
    (hgood : ¬denominatorBad x s) :
    fordDenominatorTerm x s ≤
      16 / Real.log x ^ 2 * fordWeight s := by
  let ell := Real.log
    ((largestPrimeFactor (primeSubsetProd s) : ℝ) +
      (x : ℝ) / primeSubsetProd s)
  have hlogx : 0 < Real.log x :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hlower : Real.log x ≤ 4 * ell := by
    simpa [ell] using log_x_le_four_mul_log_fordArgument hx hs hgood
  have hell : 0 < ell := by linarith
  have hsquares : Real.log x ^ 2 ≤ 16 * ell ^ 2 := by nlinarith
  have hinv : (1 : ℝ) / ell ^ 2 ≤ 16 / Real.log x ^ 2 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hell) (sq_pos_of_pos hlogx)]
    nlinarith
  have hw := fordWeight_nonneg s
  have hmul := mul_le_mul_of_nonneg_right hinv hw
  change L (primeSubsetProd s) (Real.log 2) /
      ((primeSubsetProd s : ℝ) * ell ^ 2) ≤
    16 / Real.log x ^ 2 *
      (L (primeSubsetProd s) (Real.log 2) / (primeSubsetProd s : ℝ))
  calc
    L (primeSubsetProd s) (Real.log 2) /
          ((primeSubsetProd s : ℝ) * ell ^ 2) =
        (1 / ell ^ 2) *
          (L (primeSubsetProd s) (Real.log 2) / (primeSubsetProd s : ℝ)) := by
      have ha0 : (primeSubsetProd s : ℝ) ≠ 0 := by
        exact_mod_cast (prod_primeSubset_pos hs).ne'
      field_simp [ha0, hell.ne']
    _ ≤ _ := hmul

private theorem primeSubsetProd_union {s t : Finset ℕ} (h : Disjoint s t) :
    primeSubsetProd (s ∪ t) = primeSubsetProd s * primeSubsetProd t := by
  simp [primeSubsetProd, Finset.prod_union h]

private theorem L_primeSubset_union_le
    {s t : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (ht : ∀ p ∈ t, p.Prime)
    (hst : Disjoint s t) :
    L (primeSubsetProd (s ∪ t)) (Real.log 2) ≤
      (2 : ℝ) ^ s.card * L (primeSubsetProd t) (Real.log 2) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | @cons p s hps ih =>
      have hp : p.Prime := hs p (by simp)
      have hsPrime : ∀ q ∈ s, q.Prime := fun q hq ↦ hs q (by simp [hq])
      have hpt : p ∉ t := by
        intro hpt
        exact Finset.disjoint_left.mp hst (by simp) hpt
      have hst' : Disjoint s t := by
        exact Finset.disjoint_left.mpr fun q hqs hqt ↦
          Finset.disjoint_left.mp hst (by simp [hqs]) hqt
      have hrest0 : primeSubsetProd (s ∪ t) ≠ 0 := by
        apply Nat.ne_of_gt
        unfold primeSubsetProd
        apply Finset.prod_pos
        intro q hq
        rcases Finset.mem_union.mp hq with hqs | hqt
        · exact (hsPrime q hqs).pos
        · exact (ht q hqt).pos
      calc
        L (primeSubsetProd (Finset.cons p s hps ∪ t)) (Real.log 2) =
            L (p * primeSubsetProd (s ∪ t)) (Real.log 2) := by
          congr 1
          simp [primeSubsetProd, hps, hpt, Finset.insert_union]
        _ ≤ 2 * L (primeSubsetProd (s ∪ t)) (Real.log 2) :=
          L_prime_mul_le_two hp hrest0 _
        _ ≤ 2 * ((2 : ℝ) ^ s.card * L (primeSubsetProd t) (Real.log 2)) := by
          gcongr
          exact ih hsPrime hst'
        _ = (2 : ℝ) ^ (Finset.cons p s hps).card *
            L (primeSubsetProd t) (Real.log 2) := by
          simp [Finset.cons_eq_insert, hps, pow_succ]
          ring

private def subsetContaining (P Q : Finset ℕ) : Finset (Finset ℕ) :=
  P.powerset.filter fun s ↦ Q ⊆ s

private theorem subsetContaining_eq_image {P Q : Finset ℕ} (hQP : Q ⊆ P) :
    subsetContaining P Q =
      (P \ Q).powerset.image fun t ↦ Q ∪ t := by
  ext s
  simp only [subsetContaining, Finset.mem_filter, Finset.mem_powerset,
    Finset.mem_image]
  constructor
  · rintro ⟨hsP, hQs⟩
    refine ⟨s \ Q, ?_, ?_⟩
    · intro q hq
      exact Finset.mem_sdiff.mpr
        ⟨hsP (Finset.mem_sdiff.mp hq).1, (Finset.mem_sdiff.mp hq).2⟩
    · ext q
      simp only [Finset.mem_union, Finset.mem_sdiff]
      constructor
      · rintro (hqQ | ⟨hqs, -⟩)
        · exact hQs hqQ
        · exact hqs
      · intro hqs
        exact if hqQ : q ∈ Q then Or.inl hqQ else Or.inr ⟨hqs, hqQ⟩
  · rintro ⟨t, ht, rfl⟩
    have ht' : t ⊆ P \ Q := ht
    exact ⟨Finset.union_subset hQP
      (ht'.trans (Finset.sdiff_subset.trans (by rfl))), Finset.subset_union_left⟩

private theorem union_injective_on_sdiff_powerset (P Q : Finset ℕ) :
    Set.InjOn (fun t : Finset ℕ ↦ Q ∪ t) (P \ Q).powerset := by
  intro s hs t ht hst
  have hs' : s ⊆ P \ Q := Finset.mem_powerset.mp hs
  have ht' : t ⊆ P \ Q := Finset.mem_powerset.mp ht
  ext q
  have hqQs : q ∈ Q → q ∉ s := fun hqQ hqs ↦
    (Finset.mem_sdiff.mp (hs' hqs)).2 hqQ
  have hqQt : q ∈ Q → q ∉ t := fun hqQ hqt ↦
    (Finset.mem_sdiff.mp (ht' hqt)).2 hqQ
  by_cases hqQ : q ∈ Q
  · simp [hqQs hqQ, hqQt hqQ]
  · have := Finset.ext_iff.mp hst q
    simpa [hqQ] using this

private theorem primeSubsetProd_triple_eq_lcm {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) :
    primeSubsetProd {p, q, r} = Nat.lcm p (Nat.lcm q r) := by
  let Q : Finset ℕ := {p, q, r}
  have hQprime : ∀ z ∈ Q, z.Prime := by
    intro z hz
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl | rfl
    · exact hp
    · exact hq
    · exact hr
  have hQpf : (primeSubsetProd Q).primeFactors = Q := by
    unfold primeSubsetProd
    exact Nat.primeFactors_prod hQprime
  have hlcm0 : Nat.lcm p (Nat.lcm q r) ≠ 0 := by
    exact (Nat.lcm_pos hp.pos (Nat.lcm_pos hq.pos hr.pos)).ne'
  apply Nat.dvd_antisymm
  · change primeSubsetProd Q ∣ Nat.lcm p (Nat.lcm q r)
    rw [primeSubsetProd, ← hQpf]
    apply (Nat.prod_primeFactors_dvd_iff hlcm0).2
    rw [hQpf]
    intro z hz
    simp only [Q, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with hzp | hzq | hzr
    · subst z
      exact hp.mem_primeFactors (Nat.dvd_lcm_left _ _) hlcm0
    · subst z
      exact hq.mem_primeFactors
        ((Nat.dvd_lcm_left q r).trans (Nat.dvd_lcm_right p (Nat.lcm q r))) hlcm0
    · subst z
      exact hr.mem_primeFactors
        ((Nat.dvd_lcm_right q r).trans (Nat.dvd_lcm_right p (Nat.lcm q r))) hlcm0
  · apply Nat.lcm_dvd
    · exact Finset.dvd_prod_of_mem id (by simp)
    · apply Nat.lcm_dvd
      · exact Finset.dvd_prod_of_mem id (by simp)
      · exact Finset.dvd_prod_of_mem id (by simp)

private theorem subsetContaining_weight_le
    {P Q : Finset ℕ} (hQP : Q ⊆ P)
    (hPprime : ∀ p ∈ P, p.Prime) (hQcard : Q.card ≤ 3) :
    (∑ s ∈ subsetContaining P Q, fordWeight s) ≤
      8 / (primeSubsetProd Q : ℝ) *
        ∑ t ∈ P.powerset, fordWeight t := by
  have hQprime : ∀ p ∈ Q, p.Prime := fun p hp ↦ hPprime p (hQP hp)
  have hQposN : 0 < primeSubsetProd Q := by
    unfold primeSubsetProd
    exact Finset.prod_pos fun p hp ↦ (hQprime p hp).pos
  have hQpos : (0 : ℝ) < primeSubsetProd Q := by exact_mod_cast hQposN
  rw [subsetContaining_eq_image hQP,
    Finset.sum_image (union_injective_on_sdiff_powerset P Q)]
  calc
    (∑ t ∈ (P \ Q).powerset, fordWeight (Q ∪ t)) ≤
        ∑ t ∈ (P \ Q).powerset,
          (8 / (primeSubsetProd Q : ℝ)) * fordWeight t := by
      apply Finset.sum_le_sum
      intro t ht
      have htSub : t ⊆ P \ Q := Finset.mem_powerset.mp ht
      have htP : t ⊆ P := htSub.trans Finset.sdiff_subset
      have htPrime : ∀ p ∈ t, p.Prime := fun p hp ↦ hPprime p (htP hp)
      have hdisj : Disjoint Q t := Finset.disjoint_left.mpr fun p hpQ hpt ↦
        (Finset.mem_sdiff.mp (htSub hpt)).2 hpQ
      have htposN : 0 < primeSubsetProd t := by
        unfold primeSubsetProd
        exact Finset.prod_pos fun p hp ↦ (htPrime p hp).pos
      have htpos : (0 : ℝ) < primeSubsetProd t := by exact_mod_cast htposN
      have hpow : (2 : ℝ) ^ Q.card ≤ 8 := by
        have hcases : Q.card = 0 ∨ Q.card = 1 ∨ Q.card = 2 ∨ Q.card = 3 := by omega
        rcases hcases with h | h | h | h <;> norm_num [h]
      have hL : L (primeSubsetProd (Q ∪ t)) (Real.log 2) ≤
          8 * L (primeSubsetProd t) (Real.log 2) :=
        (L_primeSubset_union_le hQprime htPrime hdisj).trans
          (mul_le_mul_of_nonneg_right hpow (L_nonneg _ _))
      rw [primeSubsetProd_union hdisj] at hL
      unfold fordWeight
      rw [primeSubsetProd_union hdisj]
      push_cast
      have hden : (0 : ℝ) <
          (primeSubsetProd Q : ℝ) * primeSubsetProd t := mul_pos hQpos htpos
      apply (div_le_iff₀ hden).2
      field_simp [hQpos.ne', htpos.ne']
      nlinarith
    _ = (8 / (primeSubsetProd Q : ℝ)) *
        ∑ t ∈ (P \ Q).powerset, fordWeight t := by
      rw [Finset.mul_sum]
    _ ≤ (8 / (primeSubsetProd Q : ℝ)) *
        ∑ t ∈ P.powerset, fordWeight t := by
      apply mul_le_mul_of_nonneg_left
      · apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro t ht
          exact Finset.mem_powerset.mpr
            ((Finset.mem_powerset.mp ht).trans Finset.sdiff_subset)
        · exact fun t _ _ ↦ fordWeight_nonneg t
      · exact div_nonneg (by norm_num) hQpos.le

private theorem log_primeSubsetProd_eq_sum {P s : Finset ℕ}
    (hsP : s ⊆ P) (hPprime : ∀ p ∈ P, p.Prime) :
    Real.log (primeSubsetProd s) = ∑ p ∈ s, Real.log p := by
  have hne : ∀ p ∈ s, (p : ℝ) ≠ 0 := fun p hp ↦ by
    exact_mod_cast (hPprime p (hsP hp)).ne_zero
  simpa [primeSubsetProd] using
    (Real.log_prod (s := s) (f := fun p : ℕ ↦ (p : ℝ)) hne)

private theorem weighted_log_cube_eq_triple (P : Finset ℕ)
    (hPprime : ∀ p ∈ P, p.Prime) :
    (∑ s ∈ P.powerset,
        fordWeight s * Real.log (primeSubsetProd s) ^ 3) =
      ∑ p ∈ P, ∑ q ∈ P, ∑ r ∈ P,
        (Real.log p * Real.log q * Real.log r) *
          ∑ s ∈ subsetContaining P {p, q, r}, fordWeight s := by
  calc
    (∑ s ∈ P.powerset,
        fordWeight s * Real.log (primeSubsetProd s) ^ 3) =
        ∑ s ∈ P.powerset,
          fordWeight s * (∑ p ∈ s, Real.log p) ^ 3 := by
      apply Finset.sum_congr rfl
      intro s hs
      rw [log_primeSubsetProd_eq_sum (Finset.mem_powerset.mp hs) hPprime]
    _ = ∑ p ∈ P, ∑ q ∈ P, ∑ r ∈ P,
        (Real.log p * Real.log q * Real.log r) *
          ∑ s ∈ subsetContaining P {p, q, r}, fordWeight s := by
      unfold subsetContaining
      simp only [Finset.sum_filter]
      simp [pow_three, Finset.mul_sum, Finset.sum_mul]
      let F : ℕ → ℕ → ℕ → Finset ℕ → ℝ := fun p q r s ↦
        if {p, q, r} ⊆ s then
          Real.log p * Real.log q * Real.log r * fordWeight s else 0
      change (∑ s ∈ P.powerset, ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s,
          fordWeight s * (Real.log r * (Real.log q * Real.log p))) =
        ∑ p ∈ P, ∑ q ∈ P, ∑ r ∈ P, ∑ s ∈ P.powerset, F p q r s
      symm
      calc
        (∑ p ∈ P, ∑ q ∈ P, ∑ r ∈ P,
            ∑ s ∈ P.powerset, F p q r s) =
            ∑ p ∈ P, ∑ q ∈ P, ∑ s ∈ P.powerset,
              ∑ r ∈ P, F p q r s := by
          apply Finset.sum_congr rfl
          intro p hp
          apply Finset.sum_congr rfl
          intro q hq
          exact Finset.sum_comm
        _ = ∑ p ∈ P, ∑ s ∈ P.powerset, ∑ q ∈ P,
              ∑ r ∈ P, F p q r s := by
          apply Finset.sum_congr rfl
          intro p hp
          exact Finset.sum_comm
        _ = ∑ s ∈ P.powerset, ∑ p ∈ P, ∑ q ∈ P,
              ∑ r ∈ P, F p q r s := Finset.sum_comm
        _ = ∑ s ∈ P.powerset, ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s,
              fordWeight s * (Real.log r * (Real.log q * Real.log p)) := by
          apply Finset.sum_congr rfl
          intro s hs
          have hsP : s ⊆ P := Finset.mem_powerset.mp hs
          simp only [F, Finset.insert_subset_iff, Finset.singleton_subset_iff]
          calc
            (∑ p ∈ P, ∑ q ∈ P, ∑ r ∈ P,
                if p ∈ s ∧ q ∈ s ∧ r ∈ s then
                  Real.log p * Real.log q * Real.log r * fordWeight s else 0) =
                ∑ p ∈ s, ∑ q ∈ P, ∑ r ∈ P,
                  if p ∈ s ∧ q ∈ s ∧ r ∈ s then
                    Real.log p * Real.log q * Real.log r * fordWeight s else 0 := by
              symm
              apply Finset.sum_subset hsP
              intro p hpP hps
              simp [hps]
            _ = ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ P,
                  if p ∈ s ∧ q ∈ s ∧ r ∈ s then
                    Real.log p * Real.log q * Real.log r * fordWeight s else 0 := by
              apply Finset.sum_congr rfl
              intro p hps
              symm
              apply Finset.sum_subset hsP
              intro q hqP hqs
              simp [hps, hqs]
            _ = ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s,
                  if p ∈ s ∧ q ∈ s ∧ r ∈ s then
                    Real.log p * Real.log q * Real.log r * fordWeight s else 0 := by
              apply Finset.sum_congr rfl
              intro p hps
              apply Finset.sum_congr rfl
              intro q hqs
              symm
              apply Finset.sum_subset hsP
              intro r hrP hrs
              simp [hps, hqs, hrs]
            _ = ∑ p ∈ s, ∑ q ∈ s, ∑ r ∈ s,
                  fordWeight s * (Real.log r * (Real.log q * Real.log p)) := by
              apply Finset.sum_congr rfl
              intro p hps
              apply Finset.sum_congr rfl
              intro q hqs
              apply Finset.sum_congr rfl
              intro r hrs
              simp [hps, hqs, hrs]
              ring

private theorem L_prod_nonneg (s : Finset ℕ) :
    0 ≤ L (primeSubsetProd s) (Real.log 2) := L_nonneg _ _

private theorem fordWeightSum_nonneg (x : ℕ) : 0 ≤ fordWeightSum x := by
  unfold fordWeightSum
  exact Finset.sum_nonneg fun s _ ↦
    div_nonneg (L_prod_nonneg s) (Nat.cast_nonneg _)

/-- The third logarithmic moment of Ford's weights is controlled by the
triple-lcm convolution.  This is the `h = 2` instance of the combinatorial
step in Ford's proof of Lemma 3.3. -/
private theorem ford_weighted_log_cube_le (x : ℕ) :
    (∑ s ∈ fordPrimeSubsets x,
        fordWeight s * Real.log (primeSubsetProd s) ^ 3) ≤
      8 * primeTripleLcmSum x * fordWeightSum x := by
  let P := Nat.primesLE x
  have hPprime : ∀ p ∈ P, p.Prime := fun p hp ↦ primesLE_prime hp
  rw [show fordPrimeSubsets x = P.powerset by rfl,
    weighted_log_cube_eq_triple P hPprime]
  calc
    (∑ p ∈ P, ∑ q ∈ P, ∑ r ∈ P,
        (Real.log p * Real.log q * Real.log r) *
          ∑ s ∈ subsetContaining P {p, q, r}, fordWeight s) ≤
      ∑ p ∈ P, ∑ q ∈ P, ∑ r ∈ P,
        8 * (Real.log p * Real.log q * Real.log r /
          (Nat.lcm p (Nat.lcm q r) : ℝ)) * fordWeightSum x := by
      apply Finset.sum_le_sum
      intro p hp
      apply Finset.sum_le_sum
      intro q hq
      apply Finset.sum_le_sum
      intro r hr
      have hpPrime := hPprime p hp
      have hqPrime := hPprime q hq
      have hrPrime := hPprime r hr
      have hQP : ({p, q, r} : Finset ℕ) ⊆ P := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl | rfl
        · exact hp
        · exact hq
        · exact hr
      have hQcard : ({p, q, r} : Finset ℕ).card ≤ 3 := by
        calc
          ({p, q, r} : Finset ℕ).card ≤ ({q, r} : Finset ℕ).card + 1 :=
            Finset.card_insert_le _ _
          _ ≤ ({r} : Finset ℕ).card + 1 + 1 :=
            Nat.add_le_add_right (Finset.card_insert_le _ _) 1
          _ = 3 := by simp
      have hfiber := subsetContaining_weight_le hQP hPprime hQcard
      have hlogs : 0 ≤ Real.log p * Real.log q * Real.log r := by
        positivity
      calc
        (Real.log p * Real.log q * Real.log r) *
            ∑ s ∈ subsetContaining P {p, q, r}, fordWeight s ≤
          (Real.log p * Real.log q * Real.log r) *
            (8 / (primeSubsetProd {p, q, r} : ℝ) *
              ∑ t ∈ P.powerset, fordWeight t) :=
          mul_le_mul_of_nonneg_left hfiber hlogs
        _ = 8 * (Real.log p * Real.log q * Real.log r /
              (Nat.lcm p (Nat.lcm q r) : ℝ)) * fordWeightSum x := by
          rw [primeSubsetProd_triple_eq_lcm hpPrime hqPrime hrPrime]
          change _ = 8 * _ * (∑ t ∈ P.powerset, fordWeight t)
          ring
    _ = 8 * primeTripleLcmSum x * fordWeightSum x := by
      unfold primeTripleLcmSum
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      rw [Finset.mul_sum, Finset.sum_mul]

private theorem denominatorBad_nonempty {x : ℕ} {s : Finset ℕ}
    (hx : 2 ≤ x) (hbad : denominatorBad x s) : s.Nonempty := by
  rw [Finset.nonempty_iff_ne_empty]
  intro hs
  subst s
  simp [denominatorBad, primeSubsetProd] at hbad
  omega

private theorem bad_remainder_mem {x : ℕ} {s : Finset ℕ}
    (hx : 2 ≤ x) (hs : s ∈ fordPrimeSubsets x) (hbad : denominatorBad x s) :
    let p := largestPrimeFactor (primeSubsetProd s)
    s.erase p ∈ fordPrimeSubsets p := by
  intro p
  have hsne : s.Nonempty := denominatorBad_nonempty hx hbad
  have hpEq : p = s.max' hsne := largestPrimeFactor_primeSubsetProd hs hsne
  have hpMem : p ∈ s := by rw [hpEq]; exact Finset.max'_mem _ _
  apply Finset.mem_powerset.mpr
  intro q hq
  have hqs : q ∈ s := Finset.mem_of_mem_erase hq
  have hqPrime := primesLE_prime (Finset.mem_powerset.mp hs hqs)
  have hqp : q ≤ p := by
    rw [hpEq]
    exact Finset.le_max' s q hqs
  exact Nat.mem_primesLE.mpr ⟨hqp, hqPrime⟩

private theorem bad_largest_mem {x : ℕ} {s : Finset ℕ}
    (hx : 2 ≤ x) (hs : s ∈ fordPrimeSubsets x)
    (hbad : denominatorBad x s) :
    largestPrimeFactor (primeSubsetProd s) ∈ Nat.primesLE x := by
  have hsne := denominatorBad_nonempty hx hbad
  rw [largestPrimeFactor_primeSubsetProd hs hsne]
  exact Finset.mem_powerset.mp hs (Finset.max'_mem _ _)

private theorem bad_term_le {x : ℕ} (hx : 2 ≤ x) {s : Finset ℕ}
    (hs : s ∈ fordPrimeSubsets x) (hbad : denominatorBad x s) :
    let p := largestPrimeFactor (primeSubsetProd s)
    let t := s.erase p
    fordDenominatorTerm x s ≤
      128 / Real.log x ^ 3 *
        (fordWeight t * Real.log (primeSubsetProd t) ^ 3 /
          ((p : ℝ) * Real.log p ^ 2)) := by
  intro p t
  have hsne := denominatorBad_nonempty hx hbad
  have hpEq : p = s.max' hsne := largestPrimeFactor_primeSubsetProd hs hsne
  have hpMem : p ∈ s := by rw [hpEq]; exact Finset.max'_mem _ _
  have hpPrime : p.Prime := primesLE_prime (Finset.mem_powerset.mp hs hpMem)
  have hpt : p ∉ t := by simp [t]
  have htUnion : insert p t = s := by simp [t, hpMem]
  have htMem : t ∈ fordPrimeSubsets p := bad_remainder_mem hx hs hbad
  have htMemX : t ∈ fordPrimeSubsets x := by
    apply Finset.mem_powerset.mpr
    exact (Finset.mem_powerset.mp htMem).trans fun q hq ↦
      Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hq).trans
        (Nat.le_of_mem_primesLE (bad_largest_mem hx hs hbad)),
        Nat.prime_of_mem_primesLE hq⟩
  have htposN : 0 < primeSubsetProd t := prod_primeSubset_pos htMem
  have htpos : (0 : ℝ) < primeSubsetProd t := by exact_mod_cast htposN
  have hppos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
  have hprod : primeSubsetProd s = p * primeSubsetProd t := by
    rw [← htUnion]
    simp [primeSubsetProd, hpt]
  have hapos : (0 : ℝ) < primeSubsetProd s := by
    exact_mod_cast prod_primeSubset_pos hs
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hlogx : 0 < Real.log x :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hlogp : 0 < Real.log p :=
    Real.log_pos (by exact_mod_cast hpPrime.one_lt)
  have hlogArg : Real.log p ≤ Real.log
      ((p : ℝ) + (x : ℝ) / primeSubsetProd s) := by
    apply Real.log_le_log hppos
    exact le_add_of_nonneg_right (div_nonneg hxpos.le hapos.le)
  have hL : L (primeSubsetProd s) (Real.log 2) ≤
      2 * L (primeSubsetProd t) (Real.log 2) := by
    rw [hprod]
    exact L_prime_mul_le_two hpPrime htposN.ne' _
  have hloga : Real.log x < 2 * Real.log (primeSubsetProd s) := by
    have hsq : (x : ℝ) < (primeSubsetProd s : ℝ) ^ 2 := by
      exact_mod_cast hbad.1
    have := Real.log_lt_log hxpos hsq
    simpa [Real.log_pow] using this
  have hlogp4 : 4 * Real.log p ≤ Real.log x := by
    have hp4 : (p : ℝ) ^ 4 ≤ (x : ℝ) := by
      exact_mod_cast hbad.2
    have hp4pos : (0 : ℝ) < (p : ℝ) ^ 4 := pow_pos hppos _
    have := Real.log_le_log hp4pos hp4
    norm_num [Real.log_pow] at this ⊢
    exact this
  have hlogaEq : Real.log (primeSubsetProd s) =
      Real.log p + Real.log (primeSubsetProd t) := by
    rw [hprod]
    push_cast
    exact Real.log_mul (ne_of_gt hppos) (ne_of_gt htpos)
  have hlogt : Real.log x < 4 * Real.log (primeSubsetProd t) := by
    rw [hlogaEq] at hloga
    linarith
  have hlogtpos : 0 < Real.log (primeSubsetProd t) := by linarith
  have hcube : Real.log x ^ 3 ≤
      64 * Real.log (primeSubsetProd t) ^ 3 := by
    nlinarith [sq_nonneg (Real.log x),
      sq_nonneg (Real.log (primeSubsetProd t)),
      mul_self_le_mul_self (hlogx.le) hlogt.le]
  let base := L (primeSubsetProd t) (Real.log 2) /
    (((p : ℝ) * primeSubsetProd t) * Real.log p ^ 2)
  have hbase : 0 ≤ base := by
    dsimp [base]
    exact div_nonneg (L_nonneg _ _)
      (mul_nonneg (mul_nonneg hppos.le htpos.le) (sq_nonneg _))
  have hfirst : fordDenominatorTerm x s ≤ 2 * base := by
    unfold fordDenominatorTerm
    rw [show largestPrimeFactor (primeSubsetProd s) = p by rfl, hprod]
    push_cast
    let ell := Real.log
      ((p : ℝ) + (x : ℝ) / ((p : ℝ) * primeSubsetProd t))
    have hlell : Real.log p ≤ ell := by simpa [ell, hprod] using hlogArg
    have hell : 0 < ell := lt_of_lt_of_le hlogp hlell
    have hden : (0 : ℝ) <
        ((p : ℝ) * primeSubsetProd t) * Real.log p ^ 2 := by positivity
    have hdenle : ((p : ℝ) * primeSubsetProd t) * Real.log p ^ 2 ≤
        ((p : ℝ) * primeSubsetProd t) * ell ^ 2 := by
      have : Real.log p ^ 2 ≤ ell ^ 2 := by
        nlinarith [sq_nonneg (ell - Real.log p)]
      gcongr
    calc
      L (p * primeSubsetProd t) (Real.log 2) /
          (((p : ℝ) * primeSubsetProd t) * ell ^ 2) ≤
        L (p * primeSubsetProd t) (Real.log 2) /
          (((p : ℝ) * primeSubsetProd t) * Real.log p ^ 2) :=
        div_le_div_of_nonneg_left (L_nonneg _ _) hden hdenle
      _ ≤ (2 * L (primeSubsetProd t) (Real.log 2)) /
          (((p : ℝ) * primeSubsetProd t) * Real.log p ^ 2) := by
        apply div_le_div_of_nonneg_right (by simpa [hprod] using hL)
        positivity
      _ = 2 * base := by dsimp [base]; ring
  have hcoeff : (2 : ℝ) ≤
      128 * Real.log (primeSubsetProd t) ^ 3 / Real.log x ^ 3 := by
    apply (le_div_iff₀ (pow_pos hlogx 3)).2
    nlinarith
  calc
    fordDenominatorTerm x s ≤ 2 * base := hfirst
    _ ≤ (128 * Real.log (primeSubsetProd t) ^ 3 / Real.log x ^ 3) * base :=
      mul_le_mul_of_nonneg_right hcoeff hbase
    _ = 128 / Real.log x ^ 3 *
        (fordWeight t * Real.log (primeSubsetProd t) ^ 3 /
          ((p : ℝ) * Real.log p ^ 2)) := by
      dsimp [base, fordWeight]
      field_simp [hppos.ne', htpos.ne', hlogp.ne', hlogx.ne']

private noncomputable def badSubsets (x : ℕ) : Finset (Finset ℕ) :=
  (fordPrimeSubsets x).filter (denominatorBad x)

private noncomputable def badEncoding (s : Finset ℕ) : ℕ × Finset ℕ :=
  let p := largestPrimeFactor (primeSubsetProd s)
  (p, s.erase p)

private def boundedPrimePairs (x : ℕ) : Finset (ℕ × Finset ℕ) :=
  ((Nat.primesLE x).product (fordPrimeSubsets x)).filter fun z ↦
    z.2 ⊆ Nat.primesLE z.1

private noncomputable def badMajorant (x : ℕ) (z : ℕ × Finset ℕ) : ℝ :=
  128 / Real.log x ^ 3 *
    (fordWeight z.2 * Real.log (primeSubsetProd z.2) ^ 3 /
      ((z.1 : ℝ) * Real.log z.1 ^ 2))

private theorem badEncoding_injective (x : ℕ) (hx : 2 ≤ x) :
    Set.InjOn badEncoding (badSubsets x) := by
  intro s hs t ht hst
  have hs' := Finset.mem_filter.mp hs
  have ht' := Finset.mem_filter.mp ht
  have hsne := denominatorBad_nonempty hx hs'.2
  have htne := denominatorBad_nonempty hx ht'.2
  have hps : largestPrimeFactor (primeSubsetProd s) ∈ s := by
    rw [largestPrimeFactor_primeSubsetProd hs'.1 hsne]
    exact Finset.max'_mem _ _
  have hpt : largestPrimeFactor (primeSubsetProd t) ∈ t := by
    rw [largestPrimeFactor_primeSubsetProd ht'.1 htne]
    exact Finset.max'_mem _ _
  have hins := congrArg (fun z : ℕ × Finset ℕ ↦ insert z.1 z.2) hst
  simpa [badEncoding, Finset.insert_erase hps, Finset.insert_erase hpt] using hins

private theorem badEncoding_mem_boundedPrimePairs {x : ℕ} (hx : 2 ≤ x)
    {s : Finset ℕ} (hs : s ∈ badSubsets x) :
    badEncoding s ∈ boundedPrimePairs x := by
  have hs' := Finset.mem_filter.mp hs
  let p := largestPrimeFactor (primeSubsetProd s)
  have hp := bad_largest_mem hx hs'.1 hs'.2
  have htP : s.erase p ∈ fordPrimeSubsets x := by
    apply Finset.mem_powerset.mpr
    exact (Finset.mem_powerset.mp (bad_remainder_mem hx hs'.1 hs'.2)).trans
      fun q hq ↦ Nat.mem_primesLE.mpr ⟨
        (Nat.le_of_mem_primesLE hq).trans (Nat.le_of_mem_primesLE hp),
        Nat.prime_of_mem_primesLE hq⟩
  have htp : s.erase p ⊆ Nat.primesLE p :=
    Finset.mem_powerset.mp (bad_remainder_mem hx hs'.1 hs'.2)
  exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hp, htP⟩, htp⟩

private theorem badMajorant_nonneg {x : ℕ} (hx : 2 ≤ x)
    {z : ℕ × Finset ℕ} (hz : z ∈ boundedPrimePairs x) :
    0 ≤ badMajorant x z := by
  have hz' := Finset.mem_filter.mp hz
  have ht := (Finset.mem_product.mp hz'.1).2
  have htpos : (0 : ℝ) < primeSubsetProd z.2 := by
    exact_mod_cast prod_primeSubset_pos ht
  have hlogt : 0 ≤ Real.log (primeSubsetProd z.2) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ primeSubsetProd z.2 from
      prod_primeSubset_pos ht))
  have hlogx : 0 < Real.log x :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  unfold badMajorant
  exact mul_nonneg (div_nonneg (by norm_num) (pow_nonneg hlogx.le 3))
    (div_nonneg (mul_nonneg (fordWeight_nonneg _) (pow_nonneg hlogt 3))
      (mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)))

private theorem bad_sum_le_bounded_pair_sum {x : ℕ} (hx : 2 ≤ x) :
    (∑ s ∈ badSubsets x, fordDenominatorTerm x s) ≤
      ∑ z ∈ boundedPrimePairs x, badMajorant x z := by
  calc
    (∑ s ∈ badSubsets x, fordDenominatorTerm x s) ≤
        ∑ s ∈ badSubsets x, badMajorant x (badEncoding s) := by
      apply Finset.sum_le_sum
      intro s hs
      have hs' := Finset.mem_filter.mp hs
      simpa [badEncoding, badMajorant] using bad_term_le hx hs'.1 hs'.2
    _ = ∑ z ∈ (badSubsets x).image badEncoding, badMajorant x z := by
      rw [Finset.sum_image (badEncoding_injective x hx)]
    _ ≤ ∑ z ∈ boundedPrimePairs x, badMajorant x z := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro z hz
        rcases Finset.mem_image.mp hz with ⟨s, hs, rfl⟩
        exact badEncoding_mem_boundedPrimePairs hx hs
      · intro z hzB hzI
        exact badMajorant_nonneg hx hzB

private theorem bounded_pair_sum_eq (x : ℕ) :
    (∑ z ∈ boundedPrimePairs x, badMajorant x z) =
      ∑ p ∈ Nat.primesLE x, ∑ t ∈ fordPrimeSubsets p,
        badMajorant x (p, t) := by
  unfold boundedPrimePairs
  rw [Finset.sum_filter]
  calc
    (∑ z ∈ (Nat.primesLE x).product (fordPrimeSubsets x),
        if z.2 ⊆ Nat.primesLE z.1 then badMajorant x z else 0) =
      ∑ p ∈ Nat.primesLE x, ∑ t ∈ fordPrimeSubsets x,
        if t ⊆ Nat.primesLE p then badMajorant x (p, t) else 0 := by
      exact Finset.sum_product _ _ _
    _ = ∑ p ∈ Nat.primesLE x, ∑ t ∈ fordPrimeSubsets p,
        badMajorant x (p, t) := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.sum_filter]
      apply Finset.sum_congr
      · ext t
        simp only [Finset.mem_filter, Finset.mem_powerset, fordPrimeSubsets]
        constructor
        · exact fun h ↦ h.2
        · intro htp
          refine ⟨?_, htp⟩
          exact htp.trans fun q hq ↦ Nat.mem_primesLE.mpr ⟨
            (Nat.le_of_mem_primesLE hq).trans (Nat.le_of_mem_primesLE hp),
            Nat.prime_of_mem_primesLE hq⟩
      · intro t ht
        rfl

private theorem fordWeightSum_mono {u x : ℕ} (hux : u ≤ x) :
    fordWeightSum u ≤ fordWeightSum x := by
  rw [fordWeightSum_eq, fordWeightSum_eq]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro s hs
    apply Finset.mem_powerset.mpr
    exact (Finset.mem_powerset.mp hs).trans fun p hp ↦
      Nat.mem_primesLE.mpr ⟨(Nat.le_of_mem_primesLE hp).trans hux,
        Nat.prime_of_mem_primesLE hp⟩
  · intro s hsx hsu
    exact fordWeight_nonneg s

private theorem bounded_pair_sum_le {x : ℕ} (hx : 2 ≤ x)
    {C₃ : ℝ} (hC₃ : 0 ≤ C₃)
    (htriple : ∀ u : ℕ, 2 ≤ u →
      primeTripleLcmSum u ≤ C₃ * Real.log u ^ 3) :
    (∑ z ∈ boundedPrimePairs x, badMajorant x z) ≤
      1024 * C₃ / Real.log x ^ 3 * primeLogWeightSum x * fordWeightSum x := by
  rw [bounded_pair_sum_eq]
  have hlogx : 0 < Real.log x :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  calc
    (∑ p ∈ Nat.primesLE x, ∑ t ∈ fordPrimeSubsets p,
        badMajorant x (p, t)) ≤
      ∑ p ∈ Nat.primesLE x,
        (1024 * C₃ / Real.log x ^ 3) *
          (Real.log p / p) * fordWeightSum x := by
      apply Finset.sum_le_sum
      intro p hp
      have hpPrime := Nat.prime_of_mem_primesLE hp
      have hp2 : 2 ≤ p := hpPrime.two_le
      have hppos : (0 : ℝ) < p := by exact_mod_cast hpPrime.pos
      have hlogp : 0 < Real.log p :=
        Real.log_pos (by exact_mod_cast hpPrime.one_lt)
      let A : ℝ := 128 / Real.log x ^ 3 /
        ((p : ℝ) * Real.log p ^ 2)
      have hA : 0 ≤ A := by dsimp [A]; positivity
      have hmoment := ford_weighted_log_cube_le p
      have hWmono : fordWeightSum p ≤ fordWeightSum x :=
        fordWeightSum_mono (Nat.le_of_mem_primesLE hp)
      calc
        (∑ t ∈ fordPrimeSubsets p, badMajorant x (p, t)) =
            A * ∑ t ∈ fordPrimeSubsets p,
              fordWeight t * Real.log (primeSubsetProd t) ^ 3 := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro t ht
          dsimp [A, badMajorant]
          ring
        _ ≤ A * (8 * primeTripleLcmSum p * fordWeightSum p) :=
          mul_le_mul_of_nonneg_left hmoment hA
        _ ≤ A * (8 * (C₃ * Real.log p ^ 3) * fordWeightSum x) := by
          apply mul_le_mul_of_nonneg_left _ hA
          have htriple' := htriple p hp2
          have htriple0 : 0 ≤ primeTripleLcmSum p := by
            unfold primeTripleLcmSum
            positivity
          have hCterm : 0 ≤ C₃ * Real.log p ^ 3 :=
            mul_nonneg hC₃ (pow_nonneg hlogp.le 3)
          calc
            8 * primeTripleLcmSum p * fordWeightSum p ≤
                8 * (C₃ * Real.log p ^ 3) * fordWeightSum p := by
              exact mul_le_mul_of_nonneg_right
                (mul_le_mul_of_nonneg_left htriple' (by norm_num))
                (fordWeightSum_nonneg p)
            _ ≤ 8 * (C₃ * Real.log p ^ 3) * fordWeightSum x := by
              apply mul_le_mul_of_nonneg_left hWmono
              positivity
        _ = (1024 * C₃ / Real.log x ^ 3) *
              (Real.log p / p) * fordWeightSum x := by
          dsimp [A]
          field_simp [hppos.ne', hlogp.ne', hlogx.ne']
          ring
    _ = 1024 * C₃ / Real.log x ^ 3 *
        primeLogWeightSum x * fordWeightSum x := by
      unfold primeLogWeightSum
      rw [Finset.mul_sum, Finset.sum_mul]

private theorem bad_sum_le_const {x : ℕ} (hx : 2 ≤ x)
    {C₁ C₃ : ℝ} (_hC₁ : 0 ≤ C₁) (hC₃ : 0 ≤ C₃)
    (hweight : ∀ u : ℕ, 2 ≤ u →
      primeLogWeightSum u ≤ C₁ * Real.log u)
    (htriple : ∀ u : ℕ, 2 ≤ u →
      primeTripleLcmSum u ≤ C₃ * Real.log u ^ 3) :
    (∑ s ∈ badSubsets x, fordDenominatorTerm x s) ≤
      (1024 * C₃ * C₁) / Real.log x ^ 2 * fordWeightSum x := by
  have hlogx : 0 < Real.log x :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hpair := bounded_pair_sum_le hx hC₃ htriple
  have hbadpair := (bad_sum_le_bounded_pair_sum hx).trans hpair
  let K : ℝ := 1024 * C₃ / Real.log x ^ 3
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hW := hweight x hx
  calc
    (∑ s ∈ badSubsets x, fordDenominatorTerm x s) ≤
        K * primeLogWeightSum x * fordWeightSum x := by
      simpa [K] using hbadpair
    _ ≤ K * (C₁ * Real.log x) * fordWeightSum x := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hW hK) (fordWeightSum_nonneg x)
    _ = (1024 * C₃ * C₁) / Real.log x ^ 2 * fordWeightSum x := by
      dsimp [K]
      field_simp [hlogx.ne']

private theorem good_sum_le {x : ℕ} (hx : 2 ≤ x) :
    (∑ s ∈ (fordPrimeSubsets x).filter (fun s ↦ ¬denominatorBad x s),
        fordDenominatorTerm x s) ≤
      16 / Real.log x ^ 2 * fordWeightSum x := by
  have hlogx : 0 < Real.log x :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  calc
    (∑ s ∈ (fordPrimeSubsets x).filter (fun s ↦ ¬denominatorBad x s),
        fordDenominatorTerm x s) ≤
      ∑ s ∈ (fordPrimeSubsets x).filter (fun s ↦ ¬denominatorBad x s),
        16 / Real.log x ^ 2 * fordWeight s := by
      apply Finset.sum_le_sum
      intro s hs
      have hs' := Finset.mem_filter.mp hs
      exact fordDenominatorTerm_le_of_not_bad hx hs'.1 hs'.2
    _ ≤ ∑ s ∈ fordPrimeSubsets x,
        16 / Real.log x ^ 2 * fordWeight s := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro s hs hsn
        exact mul_nonneg (div_nonneg (by norm_num) (sq_nonneg _))
          (fordWeight_nonneg s)
    _ = 16 / Real.log x ^ 2 * fordWeightSum x := by
      rw [fordWeightSum_eq, Finset.mul_sum]

/-- Uniform, assumption-free `h = 2` specialization of Ford's Lemma 3.3.
The constant is absolute and the estimate holds for every integer `x ≥ 2`. -/
theorem exists_fordDenominatorSum_le_const_div_log_sq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℕ, 2 ≤ x →
      fordDenominatorSum x ≤
        C / Real.log x ^ 2 * fordWeightSum x := by
  obtain ⟨C₁, hC₁, hweight⟩ := exists_primeLogWeightSum_le_const_mul_log
  obtain ⟨C₃, hC₃, htriple⟩ :=
    exists_primeTripleLcmSum_le_const_mul_log_cube
  refine ⟨16 + 1024 * C₃ * C₁, by positivity, fun x hx ↦ ?_⟩
  have hbad := bad_sum_le_const hx hC₁ hC₃ hweight htriple
  have hgood := good_sum_le hx
  rw [fordDenominatorSum_eq]
  calc
    (∑ s ∈ fordPrimeSubsets x, fordDenominatorTerm x s) =
        (∑ s ∈ badSubsets x, fordDenominatorTerm x s) +
          ∑ s ∈ (fordPrimeSubsets x).filter
            (fun s ↦ ¬denominatorBad x s), fordDenominatorTerm x s := by
      rw [badSubsets]
      exact (Finset.sum_filter_add_sum_filter_not
        (fordPrimeSubsets x) (denominatorBad x) (fordDenominatorTerm x)).symm
    _ ≤ (1024 * C₃ * C₁) / Real.log x ^ 2 * fordWeightSum x +
        16 / Real.log x ^ 2 * fordWeightSum x := add_le_add hbad hgood
    _ = (16 + 1024 * C₃ * C₁) / Real.log x ^ 2 * fordWeightSum x := by
      ring

/-- Big-O form of Ford's denominator-removal lemma (`h = 2`). -/
theorem fordDenominatorSum_isBigO_inv_log_sq_mul_weight :
    fordDenominatorSum =O[atTop]
      (fun x : ℕ ↦ (1 / Real.log x ^ 2) * fordWeightSum x) := by
  obtain ⟨C, hC, h⟩ := exists_fordDenominatorSum_le_const_div_log_sq
  apply IsBigO.of_bound C
  filter_upwards [eventually_atTop.2 ⟨2, fun _ hx ↦ hx⟩] with x hx
  have hlogx : 0 < Real.log x :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (by
      rw [fordDenominatorSum_eq]
      exact Finset.sum_nonneg fun s hs ↦ fordDenominatorTerm_nonneg x s),
    abs_of_nonneg (mul_nonneg (div_nonneg zero_le_one (sq_nonneg _))
      (fordWeightSum_nonneg x))]
  have hxbound := h x hx
  calc
    fordDenominatorSum x ≤ C / Real.log x ^ 2 * fordWeightSum x := hxbound
    _ = C * (1 / Real.log x ^ 2 * fordWeightSum x) := by ring

end Erdos896.Ford
