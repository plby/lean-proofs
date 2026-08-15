/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.ErrorClasses
import ErdosProblems.Erdos387.QualitativeSieve

/-!
# Exact bad-set handoff for the unconditional absorber progression

This is the fixed-parameter analogue of `Section6Counting.lean`.  It turns the
remaining analytic problem into a strict comparison of two literal finite
cardinalities and exposes the unique residual-divisor tuple attached to every
bad parameter.
-/

namespace Erdos387

/-- Sifted absorber parameters whose binomial coefficient still has a divisor
in the forbidden fixed-`B` interval. -/
noncomputable def BadSiftedAbsorberParameterCandidates {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (T z : ℕ) : Finset ℕ := by
  classical
  exact (SiftedAbsorberParameterCandidates C T z).filter fun t =>
    HasFixedBNearDivisor m (C.nNat t) k

/-- A strict bad-set cardinality bound produces the exact counterexample on
the absorber progression. -/
theorem exists_absorberCounterexample_of_bad_card_lt {m k T z : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (hm : 0 < m)
    (hcard : (BadSiftedAbsorberParameterCandidates C T z).card <
      (SiftedAbsorberParameterCandidates C T z).card) :
    ∃ t : ℕ,
      t ∈ Finset.Ioc (T / 2) T ∧
      Nat.Coprime (sievePrimeProduct k z) ((C.nNat t).choose k) ∧
      ∀ d : ℕ, (d : ℝ) ∈ Set.Ioc ((C.nNat t : ℝ) / m) (C.nNat t) →
        ¬d ∣ (C.nNat t).choose k := by
  classical
  have hnsubset :
      ¬SiftedAbsorberParameterCandidates C T z ⊆
        BadSiftedAbsorberParameterCandidates C T z := by
    intro hsub
    have hle := Finset.card_le_card hsub
    omega
  obtain ⟨t, htS, htBad⟩ := Finset.not_subset.mp hnsubset
  have htData := htS
  rw [SiftedAbsorberParameterCandidates, Finset.mem_filter] at htData
  refine ⟨t, htData.1, htData.2, ?_⟩
  intro d hdI hdvd
  apply htBad
  rw [BadSiftedAbsorberParameterCandidates, Finset.mem_filter]
  refine ⟨htS, d, ?_, ?_, hdvd⟩
  · exact (mem_Ioc_natCast_div_iff hm).mp hdI |>.1
  · exact (mem_Ioc_natCast_div_iff hm).mp hdI |>.2

/-- A bad divisor on an absorber progression has a unique residual-divisor
tuple representation; its components divide the consecutive numerator
terms, are pairwise coprime, and at least two are nonunits. -/
theorem absorberNearDivisor_has_residualTuple
    {m k t : ℕ} (C : CoverBPZ.AbsorberCoverValid m k)
    (hm : 0 < m) (hk : 0 < k)
    (hnear : HasFixedBNearDivisor m (C.nNat t) k) :
    let D := C.toCoverFactorization t
    ∃ d : ℕ, ∃ E : CoverDivisorTuple D,
      C.nNat t < m * d ∧ d ≤ C.nNat t ∧ E.value = d ∧
      (∀ i : Fin k, E.factor i ∣ C.nNat t - i) ∧
      (∀ i j : Fin k, i ≠ j → Nat.Coprime (E.factor i) (E.factor j)) ∧
      ∃ i j : Fin k, i ≠ j ∧ E.factor i ≠ 1 ∧ E.factor j ≠ 1 := by
  dsimp
  let D := C.toCoverFactorization t
  obtain ⟨d, hnd, hdn, hdvd⟩ := hnear
  obtain ⟨E, hvalue⟩ := CoverDivisorTuple.exists_value_eq (D := D) hdvd
  have hcomponentDvd : ∀ i : Fin k, E.factor i ∣ C.nNat t - i := by
    intro i
    exact (E.divides i).trans (coverQuotient_dvd_term D i.isLt)
  have hcomponentPairwise :
      ∀ i j : Fin k, i ≠ j → Nat.Coprime (E.factor i) (E.factor j) := by
    intro i j hij
    exact Nat.Coprime.of_dvd_right (E.divides j)
      (Nat.Coprime.of_dvd_left (E.divides i)
        (C.coverQuotients_pairwise_coprime t i i.isLt j j.isLt
          (fun hval => hij (Fin.ext hval))))
  have hcomponentLe : ∀ i : Fin k, E.factor i ≤ C.nNat t / m := by
    intro i
    have hresPos : 0 < C.residual t (Fin.rev i) :=
      C.residual_pos t (Fin.rev i)
    calc
      E.factor i ≤ (C.nNat t - (i : ℕ)) / D.g i :=
        Nat.le_of_dvd (by
          rw [show (C.nNat t - (i : ℕ)) / D.g i =
              C.residual t (Fin.rev i) by
            simpa [D] using C.coverQuotient_eq_residual t i]
          exact hresPos) (E.divides i)
      _ = C.residual t (Fin.rev i) := by
        simpa [D] using C.coverQuotient_eq_residual t i
      _ ≤ C.nNat t / m := C.residual_le_div hm t (Fin.rev i)
  let i₀ : Fin k := ⟨0, hk⟩
  have hN : 1 ≤ C.nNat t / m := by
    exact (C.residual_pos t (Fin.rev i₀)).trans_le
      (C.residual_le_div hm t (Fin.rev i₀))
  have hprodGt : C.nNat t / m < ∏ i, E.factor i := by
    change C.nNat t / m < E.value
    rw [hvalue]
    apply (Nat.div_lt_iff_lt_mul hm).mpr
    simpa [mul_comm] using hnd
  have htwo :=
    exists_two_ne_one_of_prod_gt_bound E.factor hN hcomponentLe hprodGt
  exact ⟨d, E, hnd, hdn, hvalue, hcomponentDvd,
    hcomponentPairwise, htwo⟩

/-- Absorber bad tuple with a component above `large`. -/
def IsAbsorberLargeError {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (t large : ℕ) : Prop :=
  ∃ d : ℕ, ∃ E : CoverDivisorTuple (C.toCoverFactorization t),
    C.nNat t < m * d ∧ d ≤ C.nNat t ∧ E.value = d ∧
      E.HasLargeComponent large

/-- Absorber bad tuple with a component in `(medium,large]`. -/
def IsAbsorberMediumError {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (t medium large : ℕ) : Prop :=
  ∃ d : ℕ, ∃ E : CoverDivisorTuple (C.toCoverFactorization t),
    C.nNat t < m * d ∧ d ≤ C.nNat t ∧ E.value = d ∧
      E.HasMediumComponent medium large

/-- Absorber bad tuple with a convenient component factorization. -/
def IsAbsorberConvenientError {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (t y medium : ℕ) : Prop :=
  ∃ d : ℕ, ∃ E : CoverDivisorTuple (C.toCoverFactorization t),
    C.nNat t < m * d ∧ d ≤ C.nNat t ∧ E.value = d ∧
      E.HasConvenientComponent y ∧
      ∀ i : Fin k, E.factor i ≤ medium

/-- Remaining absorber error class: every component is medium and is a
small factor times at most one prime above `y`. -/
def IsAbsorberAlmostPrimeError {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k) (t y medium : ℕ) : Prop :=
  ∃ d : ℕ, ∃ E : CoverDivisorTuple (C.toCoverFactorization t),
    C.nNat t < m * d ∧ d ≤ C.nNat t ∧ E.value = d ∧
      (∀ i : Fin k, E.factor i ≤ medium) ∧ E.IsAlmostPrimeTuple y

noncomputable def AbsorberLargeErrors {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (T z large : ℕ) : Finset ℕ := by
  classical
  exact (SiftedAbsorberParameterCandidates C T z).filter fun t =>
    IsAbsorberLargeError C t large

noncomputable def AbsorberMediumErrors {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (T z medium large : ℕ) : Finset ℕ := by
  classical
  exact (SiftedAbsorberParameterCandidates C T z).filter fun t =>
    IsAbsorberMediumError C t medium large

noncomputable def AbsorberConvenientErrors {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (T z y medium : ℕ) : Finset ℕ := by
  classical
  exact (SiftedAbsorberParameterCandidates C T z).filter fun t =>
    IsAbsorberConvenientError C t y medium

noncomputable def AbsorberAlmostPrimeErrors {m k : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (T z y medium : ℕ) : Finset ℕ := by
  classical
  exact (SiftedAbsorberParameterCandidates C T z).filter fun t =>
    IsAbsorberAlmostPrimeError C t y medium

/-- The literal bad absorber set is covered by the four successive divisor
tuple classes. -/
theorem badSiftedAbsorber_subset_errorClasses
    {m k T z y medium large : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (hm : 0 < m) (hk : 0 < k) (hy : 2 ≤ y) :
    BadSiftedAbsorberParameterCandidates C T z ⊆
      (((AbsorberLargeErrors C T z large ∪
        AbsorberMediumErrors C T z medium large) ∪
        AbsorberConvenientErrors C T z y medium) ∪
        AbsorberAlmostPrimeErrors C T z y medium) := by
  classical
  intro t htBad
  rw [BadSiftedAbsorberParameterCandidates, Finset.mem_filter] at htBad
  obtain ⟨htS, hnear⟩ := htBad
  obtain ⟨d, E, hnd, hdn, hvalue, _hcomponentDvd,
      _hcomponentPairwise, _htwo⟩ :=
    absorberNearDivisor_has_residualTuple C hm hk hnear
  have hpos : ∀ i : Fin k, 0 < E.factor i := by
    intro i
    have hfactorDvd : E.factor i ∣ (C.nNat t).choose k :=
      (E.divides i).trans
        (coverQuotient_dvd_choose (C.toCoverFactorization t) i.isLt)
    exact Nat.pos_of_dvd_of_pos hfactorDvd
      (Nat.choose_pos (C.k_lt_nNat t).le)
  rcases E.errorClass_exhaustion (y := y) (medium := medium) (large := large)
      hy hpos with hlarge | hmedium | hconv | halmost
  · apply Finset.mem_union.mpr
    left; apply Finset.mem_union.mpr
    left; apply Finset.mem_union.mpr
    left
    rw [AbsorberLargeErrors, Finset.mem_filter]
    exact ⟨htS, d, E, hnd, hdn, hvalue, hlarge⟩
  · apply Finset.mem_union.mpr
    left; apply Finset.mem_union.mpr
    left; apply Finset.mem_union.mpr
    right
    rw [AbsorberMediumErrors, Finset.mem_filter]
    exact ⟨htS, d, E, hnd, hdn, hvalue, hmedium⟩
  · apply Finset.mem_union.mpr
    left; apply Finset.mem_union.mpr
    right
    rw [AbsorberConvenientErrors, Finset.mem_filter]
    exact ⟨htS, d, E, hnd, hdn, hvalue, hconv.2, hconv.1⟩
  · apply Finset.mem_union.mpr
    right
    rw [AbsorberAlmostPrimeErrors, Finset.mem_filter]
    exact ⟨htS, d, E, hnd, hdn, hvalue, halmost.1, halmost.2⟩

/-- Cardinality form of the absorber error-class cover. -/
theorem badSiftedAbsorber_card_le_error_sum
    {m k T z y medium large : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (hm : 0 < m) (hk : 0 < k) (hy : 2 ≤ y) :
    (BadSiftedAbsorberParameterCandidates C T z).card ≤
      (AbsorberLargeErrors C T z large).card +
      (AbsorberMediumErrors C T z medium large).card +
      (AbsorberConvenientErrors C T z y medium).card +
      (AbsorberAlmostPrimeErrors C T z y medium).card := by
  let EL := AbsorberLargeErrors C T z large
  let EM := AbsorberMediumErrors C T z medium large
  let EC := AbsorberConvenientErrors C T z y medium
  let EA := AbsorberAlmostPrimeErrors C T z y medium
  calc
    (BadSiftedAbsorberParameterCandidates C T z).card ≤
        (EL ∪ EM ∪ EC ∪ EA).card :=
      Finset.card_le_card (badSiftedAbsorber_subset_errorClasses C hm hk hy)
    _ ≤ (EL ∪ EM ∪ EC).card + EA.card := Finset.card_union_le _ _
    _ ≤ ((EL ∪ EM).card + EC.card) + EA.card := by
      gcongr
      exact Finset.card_union_le _ _
    _ ≤ ((EL.card + EM.card) + EC.card) + EA.card := by
      gcongr
      exact Finset.card_union_le _ _
    _ = EL.card + EM.card + EC.card + EA.card := by omega

/-- Exact analytic handoff for the unconditional fixed-parameter route. -/
theorem exists_absorberCounterexample_of_error_sum_lt
    {m k T z y medium large : ℕ}
    (C : CoverBPZ.AbsorberCoverValid m k)
    (hm : 0 < m) (hk : 0 < k) (hy : 2 ≤ y)
    (herrors :
        (AbsorberLargeErrors C T z large).card +
        (AbsorberMediumErrors C T z medium large).card +
        (AbsorberConvenientErrors C T z y medium).card +
        (AbsorberAlmostPrimeErrors C T z y medium).card <
          (SiftedAbsorberParameterCandidates C T z).card) :
    ∃ t : ℕ,
      t ∈ Finset.Ioc (T / 2) T ∧
      Nat.Coprime (sievePrimeProduct k z) ((C.nNat t).choose k) ∧
      ∀ d : ℕ, (d : ℝ) ∈ Set.Ioc ((C.nNat t : ℝ) / m) (C.nNat t) →
        ¬d ∣ (C.nNat t).choose k := by
  apply exists_absorberCounterexample_of_bad_card_lt C hm
  exact lt_of_le_of_lt
    (badSiftedAbsorber_card_le_error_sum C hm hk hy) herrors

end Erdos387
