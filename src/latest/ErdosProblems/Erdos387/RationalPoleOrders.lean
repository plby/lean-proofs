/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalTracePolynomials
import Mathlib.Algebra.Polynomial.RingDivision

/-!
# Pole orders of the cleared rational trace

At a supported simple pole, the low denominator has order
`1 + p + ... + p^(m-1)` and the low numerator has order
`1 + p + ... + p^(m-2)`.  After the high Frobenius expansion, the two orders
differ by exactly `p^(2*m-1)`.  This is the local spacing used to prove that
the rational Stepanov auxiliary polynomial is nonzero.
-/

namespace Erdos387

open Polynomial
open scoped BigOperators

namespace RationalStepanov

/-- The finite geometric sum used in all local-order formulas. -/
def frobeniusOrderSum (p m : ℕ) : ℕ :=
  ∑ t ∈ Finset.range m, p ^ t

theorem frobeniusOrderSum_succ (p m : ℕ) :
    frobeniusOrderSum p (m + 1) =
      frobeniusOrderSum p m + p ^ m := by
  simp [frobeniusOrderSum, Finset.sum_range_succ]

/-- The mapped denominator is the coefficientwise image of the base-field
simple-pole denominator. -/
theorem mappedSimplePoleDenominatorPolynomial_eq_map
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) :
    mappedSimplePoleDenominatorPolynomial (E := E) coeff =
      (InverseRational.simplePoleDenominatorPolynomial coeff).map
        (algebraMap (ZMod p) E) := by
  rw [mappedSimplePoleDenominatorPolynomial,
    InverseRational.simplePoleDenominatorPolynomial]
  change (∏ r ∈ InverseRational.poleSupport coeff,
      (X - C (algebraMap (ZMod p) E r))) =
    (mapRingHom (algebraMap (ZMod p) E))
      (∏ r ∈ InverseRational.poleSupport coeff, (X - C r))
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro r hr
  simp

/-- The same coefficientwise-map identity for the common numerator. -/
theorem mappedSimplePoleNumeratorPolynomial_eq_map
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) :
    mappedSimplePoleNumeratorPolynomial (E := E) coeff =
      (InverseRational.simplePoleNumeratorPolynomial coeff).map
        (algebraMap (ZMod p) E) := by
  rw [mappedSimplePoleNumeratorPolynomial,
    InverseRational.simplePoleNumeratorPolynomial]
  change (∑ r ∈ InverseRational.poleSupport coeff,
      C (algebraMap (ZMod p) E (coeff r)) *
        ∏ s ∈ (InverseRational.poleSupport coeff).erase r,
          (X - C (algebraMap (ZMod p) E s))) =
    (mapRingHom (algebraMap (ZMod p) E))
      (∑ r ∈ InverseRational.poleSupport coeff,
        C (coeff r) *
          ∏ s ∈ (InverseRational.poleSupport coeff).erase r, (X - C s))
  simp only [coe_mapRingHom, map_sum, map_mul, map_C, map_prod, map_sub, map_X]

/-- Every iterate of Frobenius fixes an element embedded from `ZMod p`. -/
theorem iterateFrobenius_algebraMap_zmod
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [CharP E p] [Algebra (ZMod p) E]
    (t : ℕ) (x : ZMod p) :
    iterateFrobenius E p t (algebraMap (ZMod p) E x) =
      algebraMap (ZMod p) E x := by
  rw [iterateFrobenius_def, ← map_pow, ZMod.pow_card_pow]

/-- Frobenius expansion of a polynomial mapped from `ZMod p` is its literal
`p^t`-th power. -/
theorem expand_map_zmod_eq_pow
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [CharP E p] [Algebra (ZMod p) E]
    (t : ℕ) (f : (ZMod p)[X]) :
    expand E (p ^ t) (f.map (algebraMap (ZMod p) E)) =
      (f.map (algebraMap (ZMod p) E)) ^ (p ^ t) := by
  have hzmod : expand (ZMod p) (p ^ t) f = f ^ (p ^ t) := by
    induction t generalizing f with
    | zero => simp
    | succ t ih =>
        rw [pow_succ, expand_mul, ih, ZMod.expand_card]
        simpa only [← pow_mul, Nat.mul_comm]
  rw [← map_expand, hzmod, Polynomial.map_pow]

/-- A useful exact valuation rule: when two nonzero polynomials have
different orders at a point, their sum has the smaller order. -/
theorem rootMultiplicity_add_eq_left_of_lt
    {K : Type*} [Field K] {P Q : K[X]} {r : K}
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hlt : P.rootMultiplicity r < Q.rootMultiplicity r) :
    (P + Q).rootMultiplicity r = P.rootMultiplicity r := by
  let TP := taylor r P
  let TQ := taylor r Q
  have hTP : TP ≠ 0 := by
    intro h
    apply hP
    apply taylor_injective r
    simpa only [TP, map_zero] using h
  have hTQ : TQ ≠ 0 := by
    intro h
    apply hQ
    apply taylor_injective r
    simpa only [TQ, map_zero] using h
  have horders :
      TP.natTrailingDegree < TQ.natTrailingDegree := by
    simpa only [TP, TQ, taylor_apply, ← rootMultiplicity_eq_natTrailingDegree]
      using hlt
  have hcoeffP : TP.coeff TP.natTrailingDegree ≠ 0 :=
    coeff_natTrailingDegree_ne_zero.mpr hTP
  have hcoeffQ : TQ.coeff TP.natTrailingDegree = 0 :=
    coeff_eq_zero_of_lt_natTrailingDegree horders
  have hcoeffAdd :
      (TP + TQ).coeff TP.natTrailingDegree ≠ 0 := by
    simpa [coeff_add, hcoeffQ] using hcoeffP
  have hsum : TP + TQ ≠ 0 := by
    intro h
    rw [h, coeff_zero] at hcoeffAdd
    exact hcoeffAdd rfl
  have hlower : ∀ j < TP.natTrailingDegree,
      (TP + TQ).coeff j = 0 := by
    intro j hj
    rw [coeff_add, coeff_eq_zero_of_lt_natTrailingDegree hj,
      coeff_eq_zero_of_lt_natTrailingDegree (hj.trans horders), zero_add]
  have heq : (TP + TQ).natTrailingDegree = TP.natTrailingDegree := by
    apply le_antisymm
    · exact natTrailingDegree_le_of_ne_zero hcoeffAdd
    · exact le_natTrailingDegree hsum hlower
  rw [rootMultiplicity_eq_natTrailingDegree,
    rootMultiplicity_eq_natTrailingDegree, add_comp]
  simpa only [TP, TQ, taylor_apply] using heq

theorem rootMultiplicity_add_eq_right_of_lt
    {K : Type*} [Field K] {P Q : K[X]} {r : K}
    (hP : P ≠ 0) (hQ : Q ≠ 0)
    (hlt : Q.rootMultiplicity r < P.rootMultiplicity r) :
    (P + Q).rootMultiplicity r = Q.rootMultiplicity r := by
  rw [add_comm]
  exact rootMultiplicity_add_eq_left_of_lt hQ hP hlt

/-- Adding one Frobenius transform to the low denominator. -/
theorem lowRationalDenominator_succ
    {E : Type*} [CommRing E] (p m : ℕ) (B : E[X]) :
    lowRationalDenominator p (m + 1) B =
      lowRationalDenominator p m B * expand E (p ^ m) B := by
  simp [lowRationalDenominator, Finset.prod_range_succ]

/-- Adding one Frobenius transform to the cleared low numerator. -/
theorem lowRationalNumerator_succ
    {E : Type*} [CommRing E] (p m : ℕ) (A B : E[X]) :
    lowRationalNumerator p (m + 1) A B =
      lowRationalNumerator p m A B * expand E (p ^ m) B +
        expand E (p ^ m) A * lowRationalDenominator p m B := by
  rw [lowRationalNumerator, Finset.sum_range_succ,
    lowRationalNumerator, lowRationalDenominator]
  congr 1
  · rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro t ht
    have htlt : t < m := Finset.mem_range.mp ht
    rw [mul_assoc]
    apply congrArg ((expand E (p ^ t) A) * ·)
    rw [Finset.range_add_one, Finset.erase_insert_of_ne (by omega),
      Finset.prod_insert]
    · ring
    · intro hm
      exact Finset.notMem_range_self (Finset.mem_of_mem_erase hm)
  · rw [Finset.range_add_one,
      Finset.erase_insert (s := Finset.range m) (a := m)
        Finset.notMem_range_self]

/-- The mapped numerator is nonzero at every embedded supported pole. -/
theorem eval_mappedSimplePoleNumeratorPolynomial_ne_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff) :
    (mappedSimplePoleNumeratorPolynomial (E := E) coeff).eval
        (algebraMap (ZMod p) E r) ≠ 0 := by
  rw [mappedSimplePoleNumeratorPolynomial_eq_map, eval_map_apply]
  intro h
  apply InverseRational.eval_simplePoleNumeratorPolynomial_ne_zero coeff hr
  exact (algebraMap (ZMod p) E).injective (by simpa using h)

/-- At a supported pole, the base numerator has order zero. -/
theorem rootMultiplicity_mappedSimplePoleNumeratorPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff) :
    (mappedSimplePoleNumeratorPolynomial (E := E) coeff).rootMultiplicity
        (algebraMap (ZMod p) E r) = 0 := by
  apply rootMultiplicity_eq_zero
  simpa only [IsRoot] using
    eval_mappedSimplePoleNumeratorPolynomial_ne_zero (E := E) coeff hr

/-- At a supported pole, the base denominator has order one. -/
theorem rootMultiplicity_mappedSimplePoleDenominatorPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff) :
    (mappedSimplePoleDenominatorPolynomial (E := E) coeff).rootMultiplicity
        (algebraMap (ZMod p) E r) = 1 := by
  rw [mappedSimplePoleDenominatorPolynomial_eq_map,
    ← eq_rootMultiplicity_map (algebraMap (ZMod p) E).injective r,
    InverseRational.simplePoleDenominatorPolynomial_eq_mul_erase coeff hr]
  have hcomp :
      (∏ s ∈ (InverseRational.poleSupport coeff).erase r,
        (X - C s : (ZMod p)[X])) ≠ 0 := by
    intro h
    have heval := congrArg (eval r) h
    exact (InverseRational.eval_simplePoleComplement_ne_zero coeff hr)
      (by simpa using heval)
  rw [rootMultiplicity_mul (mul_ne_zero (X_sub_C_ne_zero r) hcomp),
    rootMultiplicity_X_sub_C_self,
    rootMultiplicity_eq_zero (by
      simpa only [IsRoot] using
        InverseRational.eval_simplePoleComplement_ne_zero coeff hr)]

/-- Simultaneous exact orders and nonvanishing for both low cleared
polynomials. -/
theorem lowRationalPoleOrders
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [CharP E p] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff)
    (m : ℕ) (hm : 0 < m) :
    let A := mappedSimplePoleNumeratorPolynomial (E := E) coeff
    let B := mappedSimplePoleDenominatorPolynomial (E := E) coeff
    lowRationalDenominator p m B ≠ 0 ∧
      (lowRationalDenominator p m B).rootMultiplicity
        (algebraMap (ZMod p) E r) = frobeniusOrderSum p m ∧
      lowRationalNumerator p m A B ≠ 0 ∧
      (lowRationalNumerator p m A B).rootMultiplicity
        (algebraMap (ZMod p) E r) = frobeniusOrderSum p (m - 1) := by
  dsimp only
  let A := mappedSimplePoleNumeratorPolynomial (E := E) coeff
  let B := mappedSimplePoleDenominatorPolynomial (E := E) coeff
  have hA : A ≠ 0 := by
    intro h
    have he := congrArg (eval (algebraMap (ZMod p) E r)) h
    exact (eval_mappedSimplePoleNumeratorPolynomial_ne_zero
      (E := E) coeff hr) (by simpa [A] using he)
  have hB : B ≠ 0 := by
    intro h
    have hmultiplicity :=
      rootMultiplicity_mappedSimplePoleDenominatorPolynomial
        (E := E) coeff hr
    change B.rootMultiplicity (algebraMap (ZMod p) E r) = 1 at hmultiplicity
    rw [h, rootMultiplicity_zero] at hmultiplicity
    omega
  have hAr : A.rootMultiplicity (algebraMap (ZMod p) E r) = 0 :=
    rootMultiplicity_mappedSimplePoleNumeratorPolynomial (E := E) coeff hr
  have hBr : B.rootMultiplicity (algebraMap (ZMod p) E r) = 1 :=
    rootMultiplicity_mappedSimplePoleDenominatorPolynomial (E := E) coeff hr
  induction m using Nat.twoStepInduction with
  | zero => omega
  | one =>
      simpa [lowRationalDenominator, lowRationalNumerator,
        frobeniusOrderSum, A, B, hA, hB, hAr, hBr]
  | more m ih0 ih1 =>
      have hm1 : 0 < m + 1 := by omega
      obtain ⟨hLD, hLDord, hLN, hLNord⟩ := ih1 hm1
      have hEA : expand E (p ^ (m + 1)) A ≠ 0 := by
        change expand E (p ^ (m + 1))
          (mappedSimplePoleNumeratorPolynomial (E := E) coeff) ≠ 0
        rw [mappedSimplePoleNumeratorPolynomial_eq_map,
          expand_map_zmod_eq_pow]
        exact pow_ne_zero _ (by
          simpa [A, mappedSimplePoleNumeratorPolynomial_eq_map] using hA)
      have hEB : expand E (p ^ (m + 1)) B ≠ 0 := by
        change expand E (p ^ (m + 1))
          (mappedSimplePoleDenominatorPolynomial (E := E) coeff) ≠ 0
        rw [mappedSimplePoleDenominatorPolynomial_eq_map,
          expand_map_zmod_eq_pow]
        exact pow_ne_zero _ (by
          simpa [B, mappedSimplePoleDenominatorPolynomial_eq_map] using hB)
      have hEAord :
          (expand E (p ^ (m + 1)) A).rootMultiplicity
              (algebraMap (ZMod p) E r) = 0 := by
        rw [rootMultiplicity_expand_pow, ← iterateFrobenius_def,
          iterateFrobenius_algebraMap_zmod, hAr, mul_zero]
      have hEBord :
          (expand E (p ^ (m + 1)) B).rootMultiplicity
              (algebraMap (ZMod p) E r) = p ^ (m + 1) := by
        rw [rootMultiplicity_expand_pow, ← iterateFrobenius_def,
          iterateFrobenius_algebraMap_zmod, hBr, mul_one]
      let P := lowRationalNumerator p (m + 1) A B *
        expand E (p ^ (m + 1)) B
      let Q := expand E (p ^ (m + 1)) A *
        lowRationalDenominator p (m + 1) B
      have hP : P ≠ 0 := mul_ne_zero hLN hEB
      have hQ : Q ≠ 0 := mul_ne_zero hEA hLD
      have hPord : P.rootMultiplicity (algebraMap (ZMod p) E r) =
          frobeniusOrderSum p m + p ^ (m + 1) := by
        dsimp only [P]
        rw [rootMultiplicity_mul hP, hLNord, hEBord]
        simp only [show m + 1 - 1 = m by omega]
      have hQord : Q.rootMultiplicity (algebraMap (ZMod p) E r) =
          frobeniusOrderSum p (m + 1) := by
        dsimp only [Q]
        rw [rootMultiplicity_mul hQ, hEAord, hLDord, zero_add]
      have hlt : Q.rootMultiplicity (algebraMap (ZMod p) E r) <
          P.rootMultiplicity (algebraMap (ZMod p) E r) := by
        rw [hQord, hPord, frobeniusOrderSum_succ]
        have hp : 1 < p := (Fact.out : p.Prime).one_lt
        have hpow : p ^ m < p ^ (m + 1) :=
          Nat.pow_lt_pow_right hp (by omega)
        omega
      have hsum : P + Q ≠ 0 := by
        intro hzero
        have hord := rootMultiplicity_add_eq_right_of_lt hP hQ hlt
        rw [hzero, rootMultiplicity_zero, hQord] at hord
        have hpos : 0 < frobeniusOrderSum p (m + 1) := by
          rw [frobeniusOrderSum_succ]
          exact Nat.add_pos_right _ (Nat.pow_pos (Fact.out : p.Prime).pos)
        omega
      change lowRationalDenominator p (m + 2) B ≠ 0 ∧ _
      rw [show m + 2 = (m + 1) + 1 by omega,
        lowRationalDenominator_succ, lowRationalNumerator_succ]
      refine ⟨mul_ne_zero hLD hEB, ?_, hsum, ?_⟩
      · rw [rootMultiplicity_mul (mul_ne_zero hLD hEB), hLDord,
          hEBord, frobeniusOrderSum_succ p (m + 1),
          frobeniusOrderSum_succ p m]
      · change (P + Q).rootMultiplicity (algebraMap (ZMod p) E r) = _
        rw [rootMultiplicity_add_eq_right_of_lt hP hQ hlt, hQord]
        congr 2

/-- Exact pole order of the high numerator. -/
theorem rootMultiplicity_highRationalNumerator
    {p m : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [CharP E p] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff) (hm : 0 < m) :
    (highRationalNumerator p m
      (mappedSimplePoleNumeratorPolynomial (E := E) coeff)
      (mappedSimplePoleDenominatorPolynomial (E := E) coeff)).rootMultiplicity
        (algebraMap (ZMod p) E r) =
      p ^ m * frobeniusOrderSum p (m - 1) := by
  rw [highRationalNumerator, rootMultiplicity_expand_pow,
    ← iterateFrobenius_def, iterateFrobenius_algebraMap_zmod]
  exact congrArg (p ^ m * ·) (lowRationalPoleOrders coeff hr m hm).2.2.2

/-- Exact pole order of the high denominator. -/
theorem rootMultiplicity_highRationalDenominator
    {p m : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [CharP E p] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff) (hm : 0 < m) :
    (highRationalDenominator p m
      (mappedSimplePoleDenominatorPolynomial (E := E) coeff)).rootMultiplicity
        (algebraMap (ZMod p) E r) =
      p ^ m * frobeniusOrderSum p m := by
  rw [highRationalDenominator, rootMultiplicity_expand_pow,
    ← iterateFrobenius_def, iterateFrobenius_algebraMap_zmod]
  exact congrArg (p ^ m * ·) (lowRationalPoleOrders coeff hr m hm).2.1

/-- The high denominator order exceeds the high numerator order by the
precise mixed-radix spacing `p^(2*m-1)`. -/
theorem highRationalPoleOrder_gap
    {p m : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [CharP E p] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ InverseRational.poleSupport coeff) (hm : 0 < m) :
    let HN := highRationalNumerator p m
      (mappedSimplePoleNumeratorPolynomial (E := E) coeff)
      (mappedSimplePoleDenominatorPolynomial (E := E) coeff)
    let HD := highRationalDenominator p m
      (mappedSimplePoleDenominatorPolynomial (E := E) coeff)
    HN.rootMultiplicity (algebraMap (ZMod p) E r) + p ^ (2 * m - 1) =
      HD.rootMultiplicity (algebraMap (ZMod p) E r) := by
  dsimp only
  rw [rootMultiplicity_highRationalNumerator coeff hr hm,
    rootMultiplicity_highRationalDenominator coeff hr hm]
  have hsum := frobeniusOrderSum_succ p (m - 1)
  rw [show m - 1 + 1 = m by omega] at hsum
  rw [hsum, Nat.mul_add]
  congr 1
  rw [← pow_add]
  congr 1
  omega

end RationalStepanov

end Erdos387
