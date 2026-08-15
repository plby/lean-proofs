/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RefinedErrorCounting

/-!
# The final elementary exhaustion in the BNPZ divisor argument

This file refines the almost-prime error class into the two alternatives of
Propositions 6.5 and 6.6.  The thresholds are kept integral.  The two explicit
scale inequalities below are the exact finite substitutes for the exponent
comparisons at the end of Section 6 of the source.
-/

namespace Erdos387

open scoped BigOperators

/-- Bound a finite product by one distinguished factor and a uniform bound
for every other factor. -/
theorem fin_prod_le_distinguished_mul_pow {k : ℕ} (a : Fin k → ℕ)
    (i₀ : Fin k) (T : ℕ) (h : ∀ j, j ≠ i₀ → a j ≤ T) :
    (∏ j, a j) ≤ a i₀ * T ^ (k - 1) := by
  rw [← Finset.mul_prod_erase (Finset.univ : Finset (Fin k)) a
    (Finset.mem_univ i₀)]
  gcongr
  calc
    ∏ j ∈ (Finset.univ : Finset (Fin k)).erase i₀, a j ≤
        ∏ _j ∈ (Finset.univ : Finset (Fin k)).erase i₀, T := by
      apply Finset.prod_le_prod
      · intro j hj
        omega
      · intro j hj
        exact h j (Finset.ne_of_mem_erase hj)
    _ = T ^ (k - 1) := by simp

namespace CoverBPZ

/-- The tuple-free event estimated in Proposition 6.5: two distinct large
prime divisors are within the prescribed multiplicative gap. -/
def HasComparablePrimeError {B K : ℕ} (S : BPZSection6Input B K)
    (n secondMin gap medium : ℕ) : Prop :=
  ∃ r q : ℕ,
    r.Prime ∧ q.Prime ∧ secondMin < r ∧ r < q ∧ q ≤ medium ∧
      q < gap * r ∧ r ∣ n.choose S.k ∧ q ∣ n.choose S.k

/-- The certificate estimated in Proposition 6.6: after extracting uniformly
small factors, one prime is separated from every other prime factor by the
prescribed multiplicative gap, and a second prime exceeds `secondMin`. -/
def HasSeparatedAlmostPrimeError {B K : ℕ} (S : BPZSection6Input B K)
    (n y medium secondMin gap : ℕ) : Prop :=
  ∃ hn : S.k < n,
    ∃ hprog : (Nk_formula S.k : ℤ) ∣ (n : ℤ) - S.α,
      ∃ d : ℕ, ∃ E : CoverDivisorTuple (S.toCoverFactorization hn hprog),
        ∃ f q : Fin S.k → ℕ, ∃ i₀ j₀ : Fin S.k,
          n < B * d ∧ d ≤ n ∧ E.value = d ∧
          (∀ i, E.factor i = f i * q i) ∧
          (∀ i, f i ≤ y ^ 3) ∧
          (∀ i, q i = 1 ∨ (q i).Prime ∧ y < q i) ∧
          (∀ i, E.factor i ≤ medium) ∧
          (∀ i, q i ≤ q i₀) ∧
          i₀ ≠ j₀ ∧ secondMin < q j₀ ∧
          ∀ j, j ≠ i₀ → gap * q j ≤ q i₀

noncomputable def RefinedComparablePrimeErrors {B K : ℕ}
    (S : BPZSection6Input B K) (X z secondMin gap medium : ℕ) :
    Finset ℕ := by
  classical
  exact (RefinedSiftedCandidates S X z).filter fun n =>
    HasComparablePrimeError S n secondMin gap medium

noncomputable def RefinedSeparatedAlmostPrimeErrors {B K : ℕ}
    (S : BPZSection6Input B K)
    (X z y medium secondMin gap : ℕ) : Finset ℕ := by
  classical
  exact (RefinedSiftedCandidates S X z).filter fun n =>
    HasSeparatedAlmostPrimeError S n y medium secondMin gap

/-- Every refined almost-prime error belongs either to the comparable-prime
event or to the separated-largest-prime event.  The first scale inequality
forces a second prime above `secondMin`; the second forces the largest prime
to be at least `gap * secondMin`. -/
theorem refinedAlmostPrimeErrors_subset_comparable_union_separated
    {B K X z y medium secondMin gap : ℕ}
    (S : BPZSection6Input B K)
    (hsecond : 1 ≤ secondMin)
    (hscaleSecond :
      B * y ^ (3 * S.k) * medium * secondMin ^ (S.k - 1) ≤ X / 2)
    (hscaleGap :
      B * y ^ (3 * S.k) * (gap * secondMin) ^ S.k ≤ X / 2) :
    RefinedAlmostPrimeErrors S X z y medium ⊆
      RefinedComparablePrimeErrors S X z secondMin gap medium ∪
        RefinedSeparatedAlmostPrimeErrors S X z y medium secondMin gap := by
  classical
  intro n hnAlmost
  rw [RefinedAlmostPrimeErrors, Finset.mem_filter] at hnAlmost
  obtain ⟨hnS, hnErr⟩ := hnAlmost
  obtain ⟨hn, hprog, d, E, hnd, hdn, hvalue, hmedium,
      hdecomp⟩ := hnErr
  choose f q hfactor hfSmall hqShape using hdecomp
  have hk3 := S.hk3
  have hkpos : 0 < S.k := by omega
  have hchoosePos : 0 < n.choose S.k := Nat.choose_pos hn.le
  have hfactorPos : ∀ i : Fin S.k, 0 < E.factor i := by
    intro i
    exact Nat.pos_of_dvd_of_pos
      ((E.divides i).trans
        (coverQuotient_dvd_choose (S.toCoverFactorization hn hprog) i.isLt))
      hchoosePos
  have hfPos : ∀ i : Fin S.k, 0 < f i := by
    intro i
    have := hfactorPos i
    rw [hfactor i] at this
    exact pos_of_mul_pos_left this (Nat.zero_le _)
  have hqPos : ∀ i : Fin S.k, 0 < q i := by
    intro i
    have := hfactorPos i
    rw [hfactor i] at this
    exact pos_of_mul_pos_right this (Nat.zero_le _)
  have hqLeFactor : ∀ i : Fin S.k, q i ≤ E.factor i := by
    intro i
    calc
      q i = 1 * q i := by simp
      _ ≤ f i * q i :=
        Nat.mul_le_mul_right (q i) (Nat.succ_le_iff.mpr (hfPos i))
      _ = E.factor i := (hfactor i).symm
  have hqMedium : ∀ i : Fin S.k, q i ≤ medium := fun i =>
    (hqLeFactor i).trans (hmedium i)
  have hqDvdChoose : ∀ i : Fin S.k, q i ∣ n.choose S.k := by
    intro i
    have hqFactor : q i ∣ E.factor i := by
      rw [hfactor i]
      exact dvd_mul_left _ _
    exact hqFactor.trans ((E.divides i).trans
      (coverQuotient_dvd_choose (S.toCoverFactorization hn hprog) i.isLt))
  have hpair : ∀ i j : Fin S.k, i ≠ j →
      Nat.Coprime (E.factor i) (E.factor j) := by
    intro i j hij
    exact Nat.Coprime.of_dvd_right (E.divides j)
      (Nat.Coprime.of_dvd_left (E.divides i)
        (S.coverQuotients_pairwise_coprime hn hprog i i.isLt j j.isLt
          (fun h => hij (Fin.ext h))))
  have hpairQ : ∀ i j : Fin S.k, i ≠ j → Nat.Coprime (q i) (q j) := by
    intro i j hij
    apply Nat.Coprime.of_dvd_right
      (show q j ∣ E.factor j by rw [hfactor j]; exact dvd_mul_left _ _)
    apply Nat.Coprime.of_dvd_left
      (show q i ∣ E.factor i by rw [hfactor i]; exact dvd_mul_left _ _)
    exact hpair i j hij
  have hfProd : (∏ i, f i) ≤ y ^ (3 * S.k) := by
    calc
      (∏ i, f i) ≤ ∏ _i : Fin S.k, y ^ 3 := by
        apply Finset.prod_le_prod
        · intro i hi
          omega
        · intro i hi
          exact hfSmall i
      _ = (y ^ 3) ^ S.k := by simp
      _ = y ^ (3 * S.k) := (pow_mul y 3 S.k).symm
  have hvalueSplit : E.value = (∏ i, f i) * ∏ i, q i := by
    rw [CoverDivisorTuple.value]
    calc
      (∏ i, E.factor i) = ∏ i, f i * q i := by
        apply Finset.prod_congr rfl
        intro i hi
        exact hfactor i
      _ = (∏ i, f i) * ∏ i, q i := Finset.prod_mul_distrib
  have huniv : (Finset.univ : Finset (Fin S.k)).Nonempty :=
    ⟨⟨0, hkpos⟩, Finset.mem_univ _⟩
  obtain ⟨i₀, _hi₀, hi₀max⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin S.k)) q huniv
  have hqMax : ∀ i : Fin S.k, q i ≤ q i₀ := fun i =>
    hi₀max i (Finset.mem_univ i)
  have hqMaxGap : gap * secondMin ≤ q i₀ := by
    by_contra hnot
    have hmaxLt : q i₀ < gap * secondMin := Nat.lt_of_not_ge hnot
    have hqBound : ∀ i : Fin S.k, q i ≤ gap * secondMin := fun i =>
      (hqMax i).trans hmaxLt.le
    have hqProd : (∏ i, q i) ≤ (gap * secondMin) ^ S.k := by
      calc
        (∏ i, q i) ≤ ∏ _i : Fin S.k, gap * secondMin := by
          apply Finset.prod_le_prod
          · intro i hi
            omega
          · intro i hi
            exact hqBound i
        _ = (gap * secondMin) ^ S.k := by simp
    have hdBound : d ≤ y ^ (3 * S.k) * (gap * secondMin) ^ S.k := by
      calc
        d = E.value := hvalue.symm
        _ = (∏ i, f i) * ∏ i, q i := hvalueSplit
        _ ≤ y ^ (3 * S.k) * (gap * secondMin) ^ S.k :=
          Nat.mul_le_mul hfProd hqProd
    have hBd : B * d ≤ X / 2 := by
      exact (Nat.mul_le_mul_left B hdBound).trans (by
        simpa [mul_assoc] using hscaleGap)
    have hnData := hnS
    rw [RefinedSiftedCandidates, Finset.mem_filter,
      mem_RefinedBaseCandidates] at hnData
    obtain ⟨⟨hnWindow, _hn, _hprog⟩, _hrough⟩ := hnData
    have hXn := (Finset.mem_Ioc.mp hnWindow).1
    omega
  have hsecondPrime : ∃ j : Fin S.k, j ≠ i₀ ∧ secondMin < q j := by
    by_contra hnot
    push Not at hnot
    have hqProd : (∏ i, q i) ≤ q i₀ * secondMin ^ (S.k - 1) :=
      fin_prod_le_distinguished_mul_pow q i₀ secondMin hnot
    have hdBound :
        d ≤ y ^ (3 * S.k) * medium * secondMin ^ (S.k - 1) := by
      calc
        d = E.value := hvalue.symm
        _ = (∏ i, f i) * ∏ i, q i := hvalueSplit
        _ ≤ y ^ (3 * S.k) * (q i₀ * secondMin ^ (S.k - 1)) :=
          Nat.mul_le_mul hfProd hqProd
        _ ≤ y ^ (3 * S.k) * (medium * secondMin ^ (S.k - 1)) := by
          gcongr
          exact hqMedium i₀
        _ = y ^ (3 * S.k) * medium * secondMin ^ (S.k - 1) := by
          ac_rfl
    have hBd : B * d ≤ X / 2 := by
      exact (Nat.mul_le_mul_left B hdBound).trans (by
        simpa [mul_assoc] using hscaleSecond)
    have hnData := hnS
    rw [RefinedSiftedCandidates, Finset.mem_filter,
      mem_RefinedBaseCandidates] at hnData
    obtain ⟨⟨hnWindow, _hn, _hprog⟩, _hrough⟩ := hnData
    have hXn := (Finset.mem_Ioc.mp hnWindow).1
    omega
  obtain ⟨j₀, hj₀ne, hj₀large⟩ := hsecondPrime
  by_cases hsep : ∀ j, j ≠ i₀ → gap * q j ≤ q i₀
  · apply Finset.mem_union.mpr
    right
    rw [RefinedSeparatedAlmostPrimeErrors, Finset.mem_filter]
    exact ⟨hnS, hn, hprog, d, E, f, q, i₀, j₀, hnd, hdn, hvalue,
      hfactor, hfSmall, hqShape, hmedium, hqMax, hj₀ne.symm, hj₀large,
      hsep⟩
  · apply Finset.mem_union.mpr
    left
    rw [RefinedComparablePrimeErrors, Finset.mem_filter]
    push Not at hsep
    obtain ⟨j, hjne, hjclose⟩ := hsep
    have hjlarge : secondMin < q j := by
      by_contra hjnot
      have : gap * q j ≤ gap * secondMin :=
        Nat.mul_le_mul_left gap (Nat.le_of_not_gt hjnot)
      omega
    have hjPrime : (q j).Prime := by
      rcases hqShape j with hqone | hqprime
      · omega
      · exact hqprime.1
    have hiPrime : (q i₀).Prime := by
      rcases hqShape i₀ with hqone | hqprime
      · have := hqMax j
        omega
      · exact hqprime.1
    have hqne : q j ≠ q i₀ := by
      intro heq
      have hone := (hpairQ j i₀ hjne).eq_one_of_dvd
        (show q j ∣ q i₀ by simp [heq])
      exact hjPrime.ne_one hone
    have hjlt : q j < q i₀ := lt_of_le_of_ne (hqMax j) hqne
    exact ⟨hnS, q j, q i₀, hjPrime, hiPrime, hjlarge, hjlt,
      hqMedium i₀, hjclose, hqDvdChoose j, hqDvdChoose i₀⟩

theorem refinedAlmostPrimeErrors_card_le_comparable_add_separated
    {B K X z y medium secondMin gap : ℕ}
    (S : BPZSection6Input B K)
    (hsecond : 1 ≤ secondMin)
    (hscaleSecond :
      B * y ^ (3 * S.k) * medium * secondMin ^ (S.k - 1) ≤ X / 2)
    (hscaleGap :
      B * y ^ (3 * S.k) * (gap * secondMin) ^ S.k ≤ X / 2) :
    (RefinedAlmostPrimeErrors S X z y medium).card ≤
      (RefinedComparablePrimeErrors S X z secondMin gap medium).card +
        (RefinedSeparatedAlmostPrimeErrors S X z y medium secondMin gap).card := by
  exact (Finset.card_le_card
    (refinedAlmostPrimeErrors_subset_comparable_union_separated S hsecond
      hscaleSecond hscaleGap)).trans (Finset.card_union_le _ _)

/-- The exact five-error handoff corresponding to Propositions 6.2--6.6. -/
theorem exists_refined_counterexample_of_five_error_sum_lt
    {B K X z y medium large secondMin gap : ℕ}
    (S : BPZSection6Input B K) (hB : 0 < B) (hy : 2 ≤ y)
    (hsecond : 1 ≤ secondMin)
    (hscaleSecond :
      B * y ^ (3 * S.k) * medium * secondMin ^ (S.k - 1) ≤ X / 2)
    (hscaleGap :
      B * y ^ (3 * S.k) * (gap * secondMin) ^ S.k ≤ X / 2)
    (herrors :
      (RefinedLargeErrors S X z large).card +
          (RefinedMediumErrors S X z medium large).card +
          (RefinedConvenientErrors S X z y medium).card +
          (RefinedComparablePrimeErrors S X z secondMin gap medium).card +
          (RefinedSeparatedAlmostPrimeErrors S X z y medium secondMin gap).card <
        (RefinedSiftedCandidates S X z).card) :
    ∃ n : ℕ,
      n ∈ Finset.Ioc (X / 2) X ∧ S.k < n ∧
      (refinementModulus S : ℤ) ∣ (n : ℤ) - refinementResidue S ∧
      IsZRough z (n.choose S.k) ∧
      ∀ d : ℕ, (d : ℝ) ∈ Set.Ioc ((n : ℝ) / B) n →
        ¬d ∣ n.choose S.k := by
  apply exists_refined_counterexample_of_error_sum_lt
    (medium := medium) (large := large) S hB hy
  have hlast :=
    refinedAlmostPrimeErrors_card_le_comparable_add_separated
      (z := z) S hsecond hscaleSecond hscaleGap
  omega

end CoverBPZ

end Erdos387
