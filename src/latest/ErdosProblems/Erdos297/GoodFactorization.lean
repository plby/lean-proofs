/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos285.PrimePowers

/-!
# Erdős Problem 297: good denominators and denominator clearing

This file packages the finite arithmetic objects in the Liu--Sawhney lower
bound.  Their notion of smoothness bounds every *exact prime-power part* of a
denominator, rather than only its prime divisors.  We use the implementation
from `Erdos285.PrimePowers` for that distinction.

For integer cutoffs `M ≤ N` and `S`, `goodDenominators N M S` is the set

`{n ∈ [M,N] : P*(n) ≤ S, max_p v_p(n) ≤ floor(5 log log N),
                    Ω(n) ≤ floor(10 log log N)}`.

The common denominator `smoothLcm S` is `lcm(1,...,S)`.  The main results
below prove that every good denominator divides it, every reciprocal sum over
good denominators has reduced denominator dividing it, and clearing
denominators gives the expected integer identity.  The last section records
the exact prime-power factorization and double-counting identities used in
the minor-arc argument.
-/

namespace Erdos297.GoodFactorization

open Finset Real
open scoped ArithmeticFunction.Omega BigOperators

noncomputable section

open Erdos285.PrimePowers

attribute [local instance] Classical.propDecidable

/-- Liu--Sawhney's bound `floor (5 log log N)` for the largest exponent in a
prime factorization. -/
def exponentBound (N : ℕ) : ℕ :=
  ⌊5 * Real.log (Real.log (N : ℝ))⌋₊

/-- Liu--Sawhney's bound `floor (10 log log N)` for the total number of prime
factors, counted with multiplicity. -/
def factorBound (N : ℕ) : ℕ :=
  ⌊10 * Real.log (Real.log (N : ℝ))⌋₊

/-- The largest exponent appearing in the prime factorization of `n`, with
value zero at `n = 0,1`. -/
def maxPrimeExponent (n : ℕ) : ℕ :=
  n.factorization.support.sup fun p ↦ n.factorization p

/-- The finite good set in the simplified Liu--Sawhney proposition. -/
def goodDenominators (N M S : ℕ) : Finset ℕ :=
  (Icc M N).filter fun n ↦
    PrimePowerSmooth S n ∧
      maxPrimeExponent n ≤ exponentBound N ∧
      Ω n ≤ factorBound N

/-- All prime powers at most the smoothness cutoff. -/
abbrev smoothPrimePowers (S : ℕ) : Finset ℕ := primePowersUpTo S

/-- The common denominator `Q(S) = lcm(1,2,...,S)`. -/
abbrev smoothLcm (S : ℕ) : ℕ := initialLcm S

/-- The subfamily of `A` consisting of multiples of `d`; this is the source's
notation `A_d`. -/
def divisiblePart (A : Finset ℕ) (d : ℕ) : Finset ℕ :=
  A.filter fun n ↦ d ∣ n

/-- The exact `q`-part of `A`: denominators whose full prime-power part at
the prime below `q` is exactly `q`.  This is the local decomposition already
used throughout the unit-fraction library. -/
abbrev exactLocalPart (A : Finset ℕ) (q : ℕ) : Finset ℕ :=
  UnitFractions.local_part A q

@[simp] lemma mem_goodDenominators {N M S n : ℕ} :
    n ∈ goodDenominators N M S ↔
      M ≤ n ∧ n ≤ N ∧ PrimePowerSmooth S n ∧
        maxPrimeExponent n ≤ exponentBound N ∧
        Ω n ≤ factorBound N := by
  simp [goodDenominators, and_assoc]

@[simp] lemma mem_divisiblePart {A : Finset ℕ} {d n : ℕ} :
    n ∈ divisiblePart A d ↔ n ∈ A ∧ d ∣ n := by
  simp [divisiblePart]

@[simp] lemma mem_exactLocalPart {A : Finset ℕ} {q n : ℕ} :
    n ∈ exactLocalPart A q ↔
      n ∈ A ∧ q ∣ n ∧ Nat.Coprime q (n / q) :=
  UnitFractions.mem_local_part n

lemma exactLocalPart_subset_divisiblePart (A : Finset ℕ) (q : ℕ) :
    exactLocalPart A q ⊆ divisiblePart A q := by
  intro n hn
  exact mem_divisiblePart.mpr ⟨(mem_exactLocalPart.mp hn).1,
    (mem_exactLocalPart.mp hn).2.1⟩

lemma card_exactLocalPart_le_divisiblePart (A : Finset ℕ) (q : ℕ) :
    (exactLocalPart A q).card ≤ (divisiblePart A q).card :=
  Finset.card_le_card (exactLocalPart_subset_divisiblePart A q)

lemma goodDenominators_subset_Icc (N M S : ℕ) :
    goodDenominators N M S ⊆ Icc M N :=
  filter_subset _ _

lemma goodDenominator_pos {N M S n : ℕ} (hM : 1 ≤ M)
    (hn : n ∈ goodDenominators N M S) : 0 < n := by
  exact (hM.trans (mem_goodDenominators.mp hn).1).trans_lt' Nat.zero_lt_one

lemma goodDenominator_smooth {N M S n : ℕ}
    (hn : n ∈ goodDenominators N M S) : PrimePowerSmooth S n :=
  (mem_goodDenominators.mp hn).2.2.1

lemma goodDenominator_factorBound {N M S n : ℕ}
    (hn : n ∈ goodDenominators N M S) :
    Ω n ≤ factorBound N :=
  (mem_goodDenominators.mp hn).2.2.2.2

lemma goodDenominator_exponentBound {N M S n : ℕ}
    (hn : n ∈ goodDenominators N M S) :
    maxPrimeExponent n ≤ exponentBound N :=
  (mem_goodDenominators.mp hn).2.2.2.1

/-! ## Exact prime-power factorization -/

/-- The exact prime-power parts of a nonzero integer have LCM equal to the
integer itself. -/
lemma lcm_primePowerParts {n : ℕ} (hn : n ≠ 0) :
    (primePowerParts n).lcm id = n := by
  rw [primePowerParts_eq_ppowers_in_singleton]
  calc
    UnitFractions.lcmA (UnitFractions.ppowers_in_set {n}) =
        UnitFractions.lcmA ({n} : Finset ℕ) :=
      UnitFractions.lcm_Q (by simpa using hn.symm)
    _ = n := by simp [UnitFractions.lcmA]

/-- Every exact prime-power part of a smooth integer occurs among the prime
powers up to the smoothness cutoff. -/
lemma primePowerParts_subset_smoothPrimePowers {S n : ℕ}
    (hn : PrimePowerSmooth S n) :
    primePowerParts n ⊆ smoothPrimePowers S := by
  intro q hq
  exact mem_primePowersUpTo.mpr
    ⟨((mem_primePowerParts (by rintro rfl; simp [primePowerParts] at hq)).mp hq).1,
      hn q hq⟩

/-- The number of exact prime-power parts is at most `Ω(n)`.  This is the
finite multiplicity budget used when factors are assigned to denominators. -/
lemma card_primePowerParts_le_Omega {n : ℕ} (hn : n ≠ 0) :
    (primePowerParts n).card ≤ Ω n := by
  rw [UnitFractions.Omega_eq_card_prime_pow_divisors hn]
  exact Finset.card_le_card fun q hq ↦ by
    rw [primePowerParts, mem_filter] at hq
    exact mem_filter.mpr ⟨hq.1, hq.2.1⟩

/-- Each individual prime exponent is bounded by the total multiplicity
`Ω(n)`. -/
lemma factorization_le_Omega (n p : ℕ) :
    n.factorization p ≤ Ω n := by
  by_cases hp : p ∈ n.factorization.support
  · rw [ArithmeticFunction.cardFactors_eq_sum_factorization]
    exact Finset.single_le_sum (fun q hq ↦ Nat.zero_le (n.factorization q)) hp
  · rw [Finsupp.notMem_support_iff.mp hp]
    exact Nat.zero_le _

lemma maxPrimeExponent_le_Omega (n : ℕ) :
    maxPrimeExponent n ≤ Ω n := by
  rw [maxPrimeExponent, Finset.sup_le_iff]
  intro p hp
  exact factorization_le_Omega n p

/-- A good denominator has at most `factorBound N` exact prime-power parts. -/
lemma card_primePowerParts_good_le {N M S n : ℕ} (hM : 1 ≤ M)
    (hn : n ∈ goodDenominators N M S) :
    (primePowerParts n).card ≤ factorBound N := by
  exact (card_primePowerParts_le_Omega (goodDenominator_pos hM hn).ne').trans
    (goodDenominator_factorBound hn)

/-- Exact prime-power parts are precisely the nonempty local components of a
singleton denominator. -/
lemma mem_primePowerParts_iff {n q : ℕ} :
    q ∈ primePowerParts n ↔
      IsPrimePow q ∧ (exactLocalPart {n} q).Nonempty := by
  rw [primePowerParts_eq_ppowers_in_singleton,
    UnitFractions.mem_ppowers_in_set]

/-- The prime powers occurring exactly in some member of `A` are the union
of the exact prime-power factorizations of its members. -/
lemma ppowersInSet_eq_biUnion_primePowerParts (A : Finset ℕ) :
    UnitFractions.ppowers_in_set A = A.biUnion primePowerParts := by
  rfl

/-! ## The common LCM and exact denominator clearing -/

/-- A nonzero prime-power-smooth integer divides `Q(S)`. -/
lemma dvd_smoothLcm_of_smooth {S n : ℕ} (hn0 : n ≠ 0)
    (hn : PrimePowerSmooth S n) : n ∣ smoothLcm S := by
  have hparts : (primePowerParts n).lcm id ∣ smoothLcm S := by
    apply Finset.lcm_dvd
    intro q hq
    exact Finset.dvd_lcm (s := Icc 1 S) (f := id)
      (Finset.mem_Icc.mpr
        ⟨((mem_primePowerParts hn0).mp hq).1.one_lt.le, hn q hq⟩)
  rwa [lcm_primePowerParts hn0] at hparts

lemma goodDenominator_dvd_smoothLcm {N M S n : ℕ} (hM : 1 ≤ M)
    (hn : n ∈ goodDenominators N M S) : n ∣ smoothLcm S :=
  dvd_smoothLcm_of_smooth (goodDenominator_pos hM hn).ne'
    (goodDenominator_smooth hn)

/-- The two source descriptions of `Q(S)` agree: it is both the LCM of all
prime powers at most `S` and `lcm(1,...,S)`. -/
lemma smoothPrimePowers_eq_ppowersInInterval (S : ℕ) :
    smoothPrimePowers S = UnitFractions.ppowers_in_set (Icc 1 S) := by
  ext q
  rw [mem_primePowersUpTo, UnitFractions.mem_ppowers_in_set]
  constructor
  · rintro ⟨hqpp, hqS⟩
    refine ⟨hqpp, ⟨q, (UnitFractions.mem_local_part q).mpr ?_⟩⟩
    exact ⟨Finset.mem_Icc.mpr ⟨hqpp.one_lt.le, hqS⟩, dvd_rfl,
      by rw [Nat.div_self hqpp.pos]; exact Nat.coprime_one_right q⟩
  · rintro ⟨hqpp, ⟨n, hn⟩⟩
    rcases (UnitFractions.mem_local_part n).mp hn with ⟨hnIcc, hqn, -⟩
    exact ⟨hqpp, (Nat.le_of_dvd (Finset.mem_Icc.mp hnIcc).1 hqn).trans
      (Finset.mem_Icc.mp hnIcc).2⟩

lemma lcm_smoothPrimePowers (S : ℕ) :
    (smoothPrimePowers S).lcm id = smoothLcm S := by
  rw [smoothPrimePowers_eq_ppowersInInterval]
  change UnitFractions.lcmA (UnitFractions.ppowers_in_set (Icc 1 S)) =
    UnitFractions.lcmA (Icc 1 S)
  exact UnitFractions.lcm_Q (by simp)

/-- The LCM of any family of good denominators divides the common smooth LCM. -/
lemma lcm_dvd_smoothLcm {N M S : ℕ} {A : Finset ℕ} (hM : 1 ≤ M)
    (hA : A ⊆ goodDenominators N M S) : A.lcm id ∣ smoothLcm S := by
  apply Finset.lcm_dvd
  intro n hn
  exact goodDenominator_dvd_smoothLcm hM (hA hn)

/-- The reduced denominator of a reciprocal sum over good denominators
divides `Q(S)`. -/
lemma recSum_den_dvd_smoothLcm {N M S : ℕ} {A : Finset ℕ}
    (hM : 1 ≤ M) (hA : A ⊆ goodDenominators N M S) :
    (UnitFractions.rec_sum A).den ∣ smoothLcm S :=
  (recSum_den_dvd_lcm A).trans (lcm_dvd_smoothLcm hM hA)

/-- Clearing one reciprocal denominator inside `Q(S)`. -/
lemma smoothLcm_mul_one_div {S n : ℕ} (hn0 : n ≠ 0)
    (hn : n ∣ smoothLcm S) :
    (smoothLcm S : ℚ) * ((1 : ℚ) / n) = (smoothLcm S / n : ℕ) := by
  field_simp [hn0]
  exact_mod_cast (by simpa [Nat.mul_comm] using (Nat.div_mul_cancel hn).symm)

/-- Exact denominator-clearing identity for an arbitrary smooth finite set. -/
lemma smoothLcm_mul_recSum {S : ℕ} {A : Finset ℕ} (hA0 : 0 ∉ A)
    (hA : ∀ n ∈ A, n ∣ smoothLcm S) :
    (smoothLcm S : ℚ) * UnitFractions.rec_sum A =
      ∑ n ∈ A, ((smoothLcm S / n : ℕ) : ℚ) := by
  rw [UnitFractions.rec_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  exact smoothLcm_mul_one_div (fun hn0 ↦ hA0 (hn0 ▸ hn)) (hA n hn)

/-- Exact denominator clearing specialized to a subfamily of the good set. -/
lemma smoothLcm_mul_recSum_good {N M S : ℕ} {A : Finset ℕ}
    (hM : 1 ≤ M) (hA : A ⊆ goodDenominators N M S) :
    (smoothLcm S : ℚ) * UnitFractions.rec_sum A =
      ∑ n ∈ A, ((smoothLcm S / n : ℕ) : ℚ) := by
  apply smoothLcm_mul_recSum
  · intro h0
    have := goodDenominator_pos hM (hA h0)
    omega
  · intro n hn
    exact goodDenominator_dvd_smoothLcm hM (hA hn)

/-! ## Prime-power divisor incidence and double counting -/

/-- The prime-power divisors of `n`, including all intermediate powers.  For
nonzero `n` its cardinality is exactly `Ω(n)`. -/
def primePowerDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter IsPrimePow

@[simp] lemma mem_primePowerDivisors {n q : ℕ} (hn : n ≠ 0) :
    q ∈ primePowerDivisors n ↔ IsPrimePow q ∧ q ∣ n := by
  simp [primePowerDivisors, Nat.mem_divisors, hn, and_comm]

lemma card_primePowerDivisors {n : ℕ} (hn : n ≠ 0) :
    (primePowerDivisors n).card = Ω n := by
  exact (UnitFractions.Omega_eq_card_prime_pow_divisors hn).symm

/-- Smoothness of exact prime-power parts bounds every prime-power divisor. -/
lemma primePowerDivisor_le_of_smooth {S n q : ℕ} (hn0 : n ≠ 0)
    (hn : PrimePowerSmooth S n) (hqpp : IsPrimePow q) (hqn : q ∣ n) : q ≤ S := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff q).mp hqpp
  have hfac : k ≤ n.factorization p :=
    (hp.pow_dvd_iff_le_factorization hn0).mp hqn
  have hfac0 : n.factorization p ≠ 0 := by omega
  have hexact : p ^ n.factorization p ∈ primePowerParts n := by
    rw [primePowerParts_eq_ppowers_in_singleton,
      UnitFractions.mem_ppowers_in_set' hp hfac0]
    exact ⟨n, by simp⟩
  exact (Nat.pow_le_pow_right hp.pos hfac).trans (hn _ hexact)

lemma primePowerDivisors_subset_smoothPrimePowers {S n : ℕ} (hn0 : n ≠ 0)
    (hn : PrimePowerSmooth S n) :
    primePowerDivisors n ⊆ smoothPrimePowers S := by
  intro q hq
  rw [mem_primePowerDivisors hn0] at hq
  exact mem_primePowersUpTo.mpr
    ⟨hq.1, primePowerDivisor_le_of_smooth hn0 hn hq.1 hq.2⟩

/-- Incidence double counting: summing the sizes of `A_q` over all prime
powers up to `S` counts each nonzero smooth `n ∈ A` exactly `Ω(n)` times. -/
lemma sum_card_divisiblePart_eq_sum_Omega {S : ℕ} {A : Finset ℕ}
    (hA0 : 0 ∉ A) (hAsmooth : ∀ n ∈ A, PrimePowerSmooth S n) :
    ∑ q ∈ smoothPrimePowers S, (divisiblePart A q).card =
      ∑ n ∈ A, Ω n := by
  calc
    ∑ q ∈ smoothPrimePowers S, (divisiblePart A q).card =
        ∑ q ∈ smoothPrimePowers S, ∑ n ∈ A, if q ∣ n then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro q hq
      simp [divisiblePart]
    _ = ∑ n ∈ A, ∑ q ∈ smoothPrimePowers S, if q ∣ n then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ n ∈ A, Ω n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn0 : n ≠ 0 := fun hn0 ↦ hA0 (hn0 ▸ hn)
      calc
        (∑ q ∈ smoothPrimePowers S, if q ∣ n then (1 : ℕ) else 0) =
            (primePowerDivisors n).card := by
          rw [Finset.sum_boole]
          apply congrArg Finset.card
          ext q
          rw [mem_filter, mem_primePowerDivisors hn0, mem_primePowersUpTo]
          constructor
          · rintro ⟨⟨hqpp, _⟩, hqn⟩
            exact ⟨hqpp, hqn⟩
          · rintro ⟨hqpp, hqn⟩
            exact ⟨⟨hqpp, primePowerDivisor_le_of_smooth hn0
              (hAsmooth n hn) hqpp hqn⟩, hqn⟩
        _ = Ω n := card_primePowerDivisors hn0

/-- The total number of prime-power incidences in a subfamily of the good set
is at most the source's multiplicity budget. -/
lemma sum_card_divisiblePart_good_le {N M S : ℕ} {A : Finset ℕ}
    (hM : 1 ≤ M) (hA : A ⊆ goodDenominators N M S) :
    ∑ q ∈ smoothPrimePowers S, (divisiblePart A q).card ≤
      A.card * factorBound N := by
  rw [sum_card_divisiblePart_eq_sum_Omega
    (fun h0 ↦ (goodDenominator_pos hM (hA h0)).ne' rfl)
    (fun n hn ↦ goodDenominator_smooth (hA hn))]
  exact Finset.sum_le_card_nsmul A (fun n ↦ Ω n)
    (factorBound N) fun n hn ↦ goodDenominator_factorBound (hA hn)

/-! ## LCM decomposition for omitted prime powers -/

/-- Omitting prime powers from the LCM costs at most their product.  This is
the exact divisibility statement behind the minor-arc frequency count. -/
lemma smoothLcm_dvd_complement_prod_mul_lcm {S : ℕ} {D : Finset ℕ}
    (_hD : D ⊆ smoothPrimePowers S) :
    smoothLcm S ∣ (smoothPrimePowers S \ D).prod id * D.lcm id := by
  rw [← lcm_smoothPrimePowers]
  apply Finset.lcm_dvd
  intro q hq
  by_cases hqD : q ∈ D
  · exact dvd_mul_of_dvd_right (Finset.dvd_lcm hqD) _
  · exact dvd_mul_of_dvd_left
      (dvd_prod_of_mem id (Finset.mem_sdiff.mpr ⟨hq, hqD⟩)) _

end

end Erdos297.GoodFactorization

#print axioms Erdos297.GoodFactorization.smoothLcm_mul_recSum_good
#print axioms Erdos297.GoodFactorization.sum_card_divisiblePart_eq_sum_Omega
