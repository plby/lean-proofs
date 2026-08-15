/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalRootRadius
import Mathlib.Algebra.Polynomial.Expand

/-!
# Cleared trace polynomials for a rational phase

For a fraction `A / B`, the first half of a Frobenius orbit sum is written
over the product of the Frobenius-expanded denominators.  The second half is
the corresponding Frobenius expansion of the first.  These definitions are
the denominator-cleared input for a rational Stepanov construction.
-/

namespace Erdos387

open Polynomial
open scoped BigOperators

namespace RationalStepanov

/-- The simple-pole denominator after embedding all pole parameters in an
extension field. -/
noncomputable def mappedSimplePoleDenominatorPolynomial
    {p : ℕ} [NeZero p] {E : Type*} [Field E]
    [Algebra (ZMod p) E] (coeff : ZMod p → ZMod p) : E[X] :=
  ∏ r ∈ InverseRational.poleSupport coeff,
    (X - C (algebraMap (ZMod p) E r))

/-- The corresponding embedded common numerator. -/
noncomputable def mappedSimplePoleNumeratorPolynomial
    {p : ℕ} [NeZero p] {E : Type*} [Field E]
    [Algebra (ZMod p) E] (coeff : ZMod p → ZMod p) : E[X] :=
  ∑ r ∈ InverseRational.poleSupport coeff,
    C (algebraMap (ZMod p) E (coeff r)) *
      ∏ s ∈ (InverseRational.poleSupport coeff).erase r,
        (X - C (algebraMap (ZMod p) E s))

/-- Common denominator of the first `m` Frobenius transforms of `A / B`. -/
noncomputable def lowRationalDenominator
    {E : Type*} [CommRing E] (p m : ℕ) (B : E[X]) : E[X] :=
  ∏ t ∈ Finset.range m, expand E (p ^ t) B

/-- Numerator of the first `m` Frobenius transforms of `A / B` over their
common denominator. -/
noncomputable def lowRationalNumerator
    {E : Type*} [CommRing E] (p m : ℕ) (A B : E[X]) : E[X] :=
  ∑ t ∈ Finset.range m,
    expand E (p ^ t) A *
      ∏ u ∈ (Finset.range m).erase t, expand E (p ^ u) B

/-- The second half numerator in an even Frobenius orbit. -/
noncomputable def highRationalNumerator
    {E : Type*} [CommRing E] (p m : ℕ) (A B : E[X]) : E[X] :=
  expand E (p ^ m) (lowRationalNumerator p m A B)

/-- The second half denominator in an even Frobenius orbit. -/
noncomputable def highRationalDenominator
    {E : Type*} [CommRing E] (p m : ℕ) (B : E[X]) : E[X] :=
  expand E (p ^ m) (lowRationalDenominator p m B)

/-- Numerator of the full length-`2m` rational trace. -/
noncomputable def fullRationalNumerator
    {E : Type*} [CommRing E] (p m : ℕ) (A B : E[X]) : E[X] :=
  lowRationalNumerator p m A B * highRationalDenominator p m B +
    highRationalNumerator p m A B * lowRationalDenominator p m B

/-- Denominator of the full length-`2m` rational trace. -/
noncomputable def fullRationalDenominator
    {E : Type*} [CommRing E] (p m : ℕ) (B : E[X]) : E[X] :=
  lowRationalDenominator p m B * highRationalDenominator p m B

theorem eval_lowRationalDenominator
    {E : Type*} [CommRing E] (p m : ℕ) (B : E[X]) (x : E) :
    (lowRationalDenominator p m B).eval x =
      ∏ t ∈ Finset.range m, B.eval (x ^ (p ^ t)) := by
  rw [lowRationalDenominator, eval_prod]
  apply Finset.prod_congr rfl
  intro t ht
  exact expand_eval (p ^ t) B x

theorem eval_lowRationalNumerator
    {E : Type*} [CommRing E] (p m : ℕ) (A B : E[X]) (x : E) :
    (lowRationalNumerator p m A B).eval x =
      ∑ t ∈ Finset.range m,
        A.eval (x ^ (p ^ t)) *
          ∏ u ∈ (Finset.range m).erase t,
            B.eval (x ^ (p ^ u)) := by
  rw [lowRationalNumerator, eval_finsetSum]
  apply Finset.sum_congr rfl
  intro t ht
  rw [eval_mul, expand_eval, eval_prod]
  apply congrArg (A.eval (x ^ (p ^ t)) * ·)
  apply Finset.prod_congr rfl
  intro u hu
  exact expand_eval (p ^ u) B x

/-- The elementary common-denominator identity used by every rational trace
evaluation. -/
theorem sum_mul_prod_erase_mul_inv_prod
    {E : Type*} [Field E] {I : Type*} [DecidableEq I]
    (s : Finset I) (a b : I → E)
    (hb : ∀ i ∈ s, b i ≠ 0) :
    (∑ i ∈ s, a i * ∏ j ∈ s.erase i, b j) *
        (∏ j ∈ s, b j)⁻¹ =
      ∑ i ∈ s, a i * (b i)⁻¹ := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  have hfactor :
      b i * (∏ j ∈ s.erase i, b j) = ∏ j ∈ s, b j := by
    exact Finset.mul_prod_erase s b hi
  have hrest : (∏ j ∈ s.erase i, b j) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact hb j (Finset.mem_of_mem_erase hj)
  rw [← hfactor]
  field_simp [hb i hi, hrest]

/-- The mapped common fraction evaluates to the mapped simple-pole phase at
every extension-field point away from the embedded poles. -/
theorem mappedSimplePolePhase_eq_numerator_mul_inv_denominator
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {x : E}
    (hx : ∀ r ∈ InverseRational.poleSupport coeff,
      x ≠ algebraMap (ZMod p) E r) :
    RationalWeil.mappedSimplePolePhase coeff x =
      (mappedSimplePoleNumeratorPolynomial coeff).eval x *
        ((mappedSimplePoleDenominatorPolynomial coeff).eval x)⁻¹ := by
  rw [RationalWeil.mappedSimplePolePhase,
    mappedSimplePoleNumeratorPolynomial, eval_finsetSum,
    mappedSimplePoleDenominatorPolynomial, eval_prod]
  simp only [eval_mul, eval_C, eval_prod, eval_sub, eval_X]
  exact (sum_mul_prod_erase_mul_inv_prod
    (InverseRational.poleSupport coeff)
    (fun r ↦ algebraMap (ZMod p) E (coeff r))
    (fun r ↦ x - algebraMap (ZMod p) E r) (by
      intro r hr
      exact sub_ne_zero.mpr (hx r hr))).symm

theorem eval_mappedSimplePoleDenominatorPolynomial_ne_zero
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) {x : E}
    (hx : ∀ r ∈ InverseRational.poleSupport coeff,
      x ≠ algebraMap (ZMod p) E r) :
    (mappedSimplePoleDenominatorPolynomial coeff).eval x ≠ 0 := by
  rw [mappedSimplePoleDenominatorPolynomial, eval_prod,
    Finset.prod_ne_zero_iff]
  intro r hr
  simpa only [eval_sub, eval_X, eval_C, sub_ne_zero] using hx r hr

/-- Frobenius powers act only on the extension-field point in the mapped
simple-pole phase. -/
theorem mappedSimplePolePhase_pow_char_pow
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [CharP E p] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) (x : E) (t : ℕ) :
    RationalWeil.mappedSimplePolePhase coeff x ^ (p ^ t) =
      RationalWeil.mappedSimplePolePhase coeff (x ^ (p ^ t)) := by
  rw [RationalWeil.mappedSimplePolePhase,
    RationalWeil.mappedSimplePolePhase]
  calc
    (∑ r ∈ InverseRational.poleSupport coeff,
        algebraMap (ZMod p) E (coeff r) *
          (x - algebraMap (ZMod p) E r)⁻¹) ^ (p ^ t) =
        ∑ r ∈ InverseRational.poleSupport coeff,
          (algebraMap (ZMod p) E (coeff r) *
            (x - algebraMap (ZMod p) E r)⁻¹) ^ (p ^ t) := by
      simpa using sum_pow_char_pow p t
        (InverseRational.poleSupport coeff)
        (fun r ↦ algebraMap (ZMod p) E (coeff r) *
          (x - algebraMap (ZMod p) E r)⁻¹)
    _ = ∑ r ∈ InverseRational.poleSupport coeff,
        algebraMap (ZMod p) E (coeff r) *
          (x ^ (p ^ t) - algebraMap (ZMod p) E r)⁻¹ := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [mul_pow, inv_pow, sub_pow_expChar_pow,
        ← map_pow, ← map_pow, ZMod.pow_card_pow, ZMod.pow_card_pow]

/-- A non-pole remains a non-pole throughout its Frobenius orbit. -/
theorem frobenius_pow_ne_mappedPole
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [CharP E p] [PerfectRing E p]
    [Algebra (ZMod p) E]
    {x : E} (coeff : ZMod p → ZMod p)
    (hx : ∀ r ∈ InverseRational.poleSupport coeff,
      x ≠ algebraMap (ZMod p) E r) (t : ℕ) :
    ∀ r ∈ InverseRational.poleSupport coeff,
      x ^ (p ^ t) ≠ algebraMap (ZMod p) E r := by
  intro r hr hpow
  apply hx r hr
  apply (iterateFrobeniusEquiv E p t).injective
  rw [iterateFrobeniusEquiv_def, iterateFrobeniusEquiv_def,
    hpow, ← map_pow, ZMod.pow_card_pow]

/-- Away from all orbit poles, the cleared low numerator divided by the
cleared denominator evaluates to the first half rational orbit sum. -/
theorem eval_lowRationalNumerator_mul_inv_denominator
    {E : Type*} [Field E] (p m : ℕ) (A B : E[X]) (x : E)
    (hB : ∀ t < m, B.eval (x ^ (p ^ t)) ≠ 0) :
    (lowRationalNumerator p m A B).eval x *
        ((lowRationalDenominator p m B).eval x)⁻¹ =
      ∑ t ∈ Finset.range m,
        A.eval (x ^ (p ^ t)) * (B.eval (x ^ (p ^ t)))⁻¹ := by
  rw [eval_lowRationalNumerator, eval_lowRationalDenominator]
  exact sum_mul_prod_erase_mul_inv_prod (Finset.range m)
    (fun t ↦ A.eval (x ^ (p ^ t)))
    (fun t ↦ B.eval (x ^ (p ^ t))) (by
      intro t ht
      exact hB t (Finset.mem_range.mp ht))

theorem eval_highRationalNumerator
    {E : Type*} [CommRing E] (p m : ℕ) (A B : E[X]) (x : E) :
    (highRationalNumerator p m A B).eval x =
      (lowRationalNumerator p m A B).eval (x ^ (p ^ m)) := by
  exact expand_eval (p ^ m) (lowRationalNumerator p m A B) x

theorem eval_highRationalDenominator
    {E : Type*} [CommRing E] (p m : ℕ) (B : E[X]) (x : E) :
    (highRationalDenominator p m B).eval x =
      (lowRationalDenominator p m B).eval (x ^ (p ^ m)) := by
  exact expand_eval (p ^ m) (lowRationalDenominator p m B) x

theorem eval_fullRationalNumerator
    {E : Type*} [CommRing E] (p m : ℕ) (A B : E[X]) (x : E) :
    (fullRationalNumerator p m A B).eval x =
      (lowRationalNumerator p m A B).eval x *
          (lowRationalDenominator p m B).eval (x ^ (p ^ m)) +
        (lowRationalNumerator p m A B).eval (x ^ (p ^ m)) *
          (lowRationalDenominator p m B).eval x := by
  rw [fullRationalNumerator, eval_add, eval_mul, eval_mul,
    eval_highRationalNumerator, eval_highRationalDenominator]

theorem eval_fullRationalDenominator
    {E : Type*} [CommRing E] (p m : ℕ) (B : E[X]) (x : E) :
    (fullRationalDenominator p m B).eval x =
      (lowRationalDenominator p m B).eval x *
        (lowRationalDenominator p m B).eval (x ^ (p ^ m)) := by
  rw [fullRationalDenominator, eval_mul, eval_highRationalDenominator]

/-- Away from every pole in the length-`2m` orbit, the full cleared
fraction evaluates to the complete rational Frobenius-orbit sum. -/
theorem eval_fullRationalNumerator_mul_inv_denominator
    {E : Type*} [Field E] (p m : ℕ) (A B : E[X]) (x : E)
    (hB : ∀ t < 2 * m, B.eval (x ^ (p ^ t)) ≠ 0) :
    (fullRationalNumerator p m A B).eval x *
        ((fullRationalDenominator p m B).eval x)⁻¹ =
      ∑ t ∈ Finset.range (2 * m),
        A.eval (x ^ (p ^ t)) * (B.eval (x ^ (p ^ t)))⁻¹ := by
  have hlowOrbit : ∀ t < m, B.eval (x ^ (p ^ t)) ≠ 0 := by
    intro t ht
    exact hB t (by omega)
  have hhighOrbit : ∀ t < m,
      B.eval ((x ^ (p ^ m)) ^ (p ^ t)) ≠ 0 := by
    intro t ht
    rw [← pow_mul, ← pow_add]
    exact hB (m + t) (by omega)
  have hlowDen : (lowRationalDenominator p m B).eval x ≠ 0 := by
    rw [eval_lowRationalDenominator]
    apply Finset.prod_ne_zero_iff.mpr
    intro t ht
    exact hlowOrbit t (Finset.mem_range.mp ht)
  have hhighDen :
      (lowRationalDenominator p m B).eval (x ^ (p ^ m)) ≠ 0 := by
    rw [eval_lowRationalDenominator]
    apply Finset.prod_ne_zero_iff.mpr
    intro t ht
    exact hhighOrbit t (Finset.mem_range.mp ht)
  rw [eval_fullRationalNumerator, eval_fullRationalDenominator]
  have hadd :
      ((lowRationalNumerator p m A B).eval x *
            (lowRationalDenominator p m B).eval (x ^ (p ^ m)) +
          (lowRationalNumerator p m A B).eval (x ^ (p ^ m)) *
            (lowRationalDenominator p m B).eval x) *
          ((lowRationalDenominator p m B).eval x *
            (lowRationalDenominator p m B).eval (x ^ (p ^ m)))⁻¹ =
        (lowRationalNumerator p m A B).eval x *
            ((lowRationalDenominator p m B).eval x)⁻¹ +
          (lowRationalNumerator p m A B).eval (x ^ (p ^ m)) *
            ((lowRationalDenominator p m B).eval (x ^ (p ^ m)))⁻¹ := by
    field_simp [hlowDen, hhighDen]
  rw [hadd,
    eval_lowRationalNumerator_mul_inv_denominator p m A B x hlowOrbit,
    eval_lowRationalNumerator_mul_inv_denominator
      p m A B (x ^ (p ^ m)) hhighOrbit]
  rw [show 2 * m = m + m by omega, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro t ht
  rw [← pow_mul, ← pow_add]

/-- For the mapped simple-pole fraction in a finite extension of degree
`2m`, the full cleared rational trace evaluates to the embedded algebraic
trace of the original phase. -/
theorem eval_fullRationalTrace_eq_algebraMap_trace
    {p m : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Finite E] [Algebra (ZMod p) E]
    [CharP E p] [FiniteDimensional (ZMod p) E]
    (hfin : Module.finrank (ZMod p) E = 2 * m)
    (coeff : ZMod p → ZMod p) (x : E)
    (hx : ∀ r ∈ InverseRational.poleSupport coeff,
      x ≠ algebraMap (ZMod p) E r) :
    (fullRationalNumerator p m
        (mappedSimplePoleNumeratorPolynomial coeff)
        (mappedSimplePoleDenominatorPolynomial coeff)).eval x *
      ((fullRationalDenominator p m
        (mappedSimplePoleDenominatorPolynomial coeff)).eval x)⁻¹ =
      algebraMap (ZMod p) E
        (Algebra.trace (ZMod p) E
          (RationalWeil.mappedSimplePolePhase coeff x)) := by
  let A : E[X] := mappedSimplePoleNumeratorPolynomial coeff
  let B : E[X] := mappedSimplePoleDenominatorPolynomial coeff
  have hOrbit (t : ℕ) :
      ∀ r ∈ InverseRational.poleSupport coeff,
        x ^ (p ^ t) ≠ algebraMap (ZMod p) E r :=
    frobenius_pow_ne_mappedPole coeff hx t
  have hB : ∀ t < 2 * m, B.eval (x ^ (p ^ t)) ≠ 0 := by
    intro t ht
    exact eval_mappedSimplePoleDenominatorPolynomial_ne_zero
      coeff (hOrbit t)
  calc
    (fullRationalNumerator p m A B).eval x *
        ((fullRationalDenominator p m B).eval x)⁻¹ =
        ∑ t ∈ Finset.range (2 * m),
          A.eval (x ^ (p ^ t)) * (B.eval (x ^ (p ^ t)))⁻¹ :=
      eval_fullRationalNumerator_mul_inv_denominator p m A B x hB
    _ = ∑ t ∈ Finset.range (2 * m),
        RationalWeil.mappedSimplePolePhase coeff (x ^ (p ^ t)) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact (mappedSimplePolePhase_eq_numerator_mul_inv_denominator
        coeff (hOrbit t)).symm
    _ = ∑ t ∈ Finset.range (2 * m),
        RationalWeil.mappedSimplePolePhase coeff x ^ (p ^ t) := by
      apply Finset.sum_congr rfl
      intro t ht
      exact (mappedSimplePolePhase_pow_char_pow coeff x t).symm
    _ = algebraMap (ZMod p) E
        (Algebra.trace (ZMod p) E
          (RationalWeil.mappedSimplePolePhase coeff x)) := by
      rw [FiniteField.algebraMap_trace_eq_sum_pow, hfin, Nat.card_zmod]

/-! ## Degree bounds -/

theorem natDegree_mappedSimplePoleDenominatorPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) :
    (mappedSimplePoleDenominatorPolynomial (E := E) coeff).natDegree =
      (InverseRational.poleSupport coeff).card := by
  exact natDegree_finsetProd_X_sub_C_eq_card
    (InverseRational.poleSupport coeff)
    (fun r : ZMod p ↦ algebraMap (ZMod p) E r)

theorem natDegree_mappedSimplePoleNumeratorPolynomial_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) :
    (mappedSimplePoleNumeratorPolynomial (E := E) coeff).natDegree ≤
      (InverseRational.poleSupport coeff).card - 1 := by
  rw [mappedSimplePoleNumeratorPolynomial]
  apply natDegree_sum_le_of_forall_le
  intro r hr
  calc
    (C (algebraMap (ZMod p) E (coeff r)) *
        ∏ s ∈ (InverseRational.poleSupport coeff).erase r,
          (X - C (algebraMap (ZMod p) E s))).natDegree ≤
        (∏ s ∈ (InverseRational.poleSupport coeff).erase r,
          (X - C (algebraMap (ZMod p) E s))).natDegree :=
      natDegree_C_mul_le _ _
    _ = ((InverseRational.poleSupport coeff).erase r).card :=
      natDegree_finsetProd_X_sub_C_eq_card
        ((InverseRational.poleSupport coeff).erase r)
        (fun s : ZMod p ↦ algebraMap (ZMod p) E s)
    _ = (InverseRational.poleSupport coeff).card - 1 :=
      Finset.card_erase_of_mem hr

theorem natDegree_lowRationalDenominator_le
    {E : Type*} [CommRing E] {p m d : ℕ} {B : E[X]}
    (hB : B.natDegree ≤ d) :
    (lowRationalDenominator p m B).natDegree ≤
      d * ∑ t ∈ Finset.range m, p ^ t := by
  calc
    (lowRationalDenominator p m B).natDegree ≤
        ∑ t ∈ Finset.range m,
          (expand E (p ^ t) B).natDegree := by
      exact natDegree_prod_le _ _
    _ ≤ ∑ t ∈ Finset.range m, d * p ^ t := by
      apply Finset.sum_le_sum
      intro t ht
      rw [natDegree_expand]
      exact Nat.mul_le_mul_right _ hB
    _ = d * ∑ t ∈ Finset.range m, p ^ t := by
      rw [Finset.mul_sum]

theorem natDegree_lowRationalNumerator_le
    {E : Type*} [CommRing E] {p m d : ℕ} {A B : E[X]}
    (hA : A.natDegree ≤ d) (hB : B.natDegree ≤ d) :
    (lowRationalNumerator p m A B).natDegree ≤
      d * ∑ t ∈ Finset.range m, p ^ t := by
  rw [lowRationalNumerator]
  apply natDegree_sum_le_of_forall_le
  intro t ht
  have htMem : t ∈ Finset.range m := ht
  have hprod :
      (∏ u ∈ (Finset.range m).erase t,
        expand E (p ^ u) B).natDegree ≤
        ∑ u ∈ (Finset.range m).erase t, d * p ^ u := by
    calc
      (∏ u ∈ (Finset.range m).erase t,
          expand E (p ^ u) B).natDegree ≤
          ∑ u ∈ (Finset.range m).erase t,
            (expand E (p ^ u) B).natDegree :=
        natDegree_prod_le _ _
      _ ≤ ∑ u ∈ (Finset.range m).erase t, d * p ^ u := by
        apply Finset.sum_le_sum
        intro u hu
        rw [natDegree_expand]
        exact Nat.mul_le_mul_right _ hB
  have hterm :
      (expand E (p ^ t) A *
        ∏ u ∈ (Finset.range m).erase t,
          expand E (p ^ u) B).natDegree ≤
        d * p ^ t +
          ∑ u ∈ (Finset.range m).erase t, d * p ^ u := by
    exact natDegree_mul_le.trans
      (Nat.add_le_add (by
        rw [natDegree_expand]
        exact Nat.mul_le_mul_right _ hA) hprod)
  calc
    (expand E (p ^ t) A *
        ∏ u ∈ (Finset.range m).erase t,
          expand E (p ^ u) B).natDegree ≤
        d * p ^ t +
          ∑ u ∈ (Finset.range m).erase t, d * p ^ u := hterm
    _ = ∑ u ∈ Finset.range m, d * p ^ u := by
      exact Finset.add_sum_erase (Finset.range m)
        (fun u : ℕ ↦ d * p ^ u) htMem
    _ = d * ∑ u ∈ Finset.range m, p ^ u := by
      rw [Finset.mul_sum]

theorem natDegree_highRationalNumerator_le
    {E : Type*} [CommRing E] {p m d : ℕ} {A B : E[X]}
    (hA : A.natDegree ≤ d) (hB : B.natDegree ≤ d) :
    (highRationalNumerator p m A B).natDegree ≤
      (d * ∑ t ∈ Finset.range m, p ^ t) * p ^ m := by
  rw [highRationalNumerator, natDegree_expand]
  exact Nat.mul_le_mul_right _
    (natDegree_lowRationalNumerator_le hA hB)

theorem natDegree_highRationalDenominator_le
    {E : Type*} [CommRing E] {p m d : ℕ} {B : E[X]}
    (hB : B.natDegree ≤ d) :
    (highRationalDenominator p m B).natDegree ≤
      (d * ∑ t ∈ Finset.range m, p ^ t) * p ^ m := by
  rw [highRationalDenominator, natDegree_expand]
  exact Nat.mul_le_mul_right _
    (natDegree_lowRationalDenominator_le hB)

theorem natDegree_fullRationalNumerator_le
    {E : Type*} [CommRing E] {p m d : ℕ} {A B : E[X]}
    (hA : A.natDegree ≤ d) (hB : B.natDegree ≤ d) :
    (fullRationalNumerator p m A B).natDegree ≤
      (d * ∑ t ∈ Finset.range m, p ^ t) * (p ^ m + 1) := by
  let D := d * ∑ t ∈ Finset.range m, p ^ t
  have hLN : (lowRationalNumerator p m A B).natDegree ≤ D :=
    natDegree_lowRationalNumerator_le hA hB
  have hLD : (lowRationalDenominator p m B).natDegree ≤ D :=
    natDegree_lowRationalDenominator_le hB
  have hHN : (highRationalNumerator p m A B).natDegree ≤ D * p ^ m :=
    natDegree_highRationalNumerator_le hA hB
  have hHD : (highRationalDenominator p m B).natDegree ≤ D * p ^ m :=
    natDegree_highRationalDenominator_le hB
  unfold fullRationalNumerator
  refine (natDegree_add_le _ _).trans ?_
  apply max_le
  · exact natDegree_mul_le.trans (Nat.add_le_add hLN hHD) |>.trans_eq (by ring)
  · exact natDegree_mul_le.trans (Nat.add_le_add hHN hLD) |>.trans_eq (by ring)

theorem natDegree_fullRationalDenominator_le
    {E : Type*} [CommRing E] {p m d : ℕ} {B : E[X]}
    (hB : B.natDegree ≤ d) :
    (fullRationalDenominator p m B).natDegree ≤
      (d * ∑ t ∈ Finset.range m, p ^ t) * (p ^ m + 1) := by
  let D := d * ∑ t ∈ Finset.range m, p ^ t
  have hLD : (lowRationalDenominator p m B).natDegree ≤ D :=
    natDegree_lowRationalDenominator_le hB
  have hHD : (highRationalDenominator p m B).natDegree ≤ D * p ^ m :=
    natDegree_highRationalDenominator_le hB
  unfold fullRationalDenominator
  exact natDegree_mul_le.trans (Nat.add_le_add hLD hHD) |>.trans_eq (by ring)

/-- Conductor-sized degree bound for the numerator of the cleared trace of
the mapped simple-pole phase. -/
theorem natDegree_fullMappedSimplePoleNumerator_le
    {p m : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) :
    (fullRationalNumerator p m
      (mappedSimplePoleNumeratorPolynomial (E := E) coeff)
      (mappedSimplePoleDenominatorPolynomial (E := E) coeff)).natDegree ≤
      ((InverseRational.poleSupport coeff).card *
          ∑ t ∈ Finset.range m, p ^ t) * (p ^ m + 1) := by
  apply natDegree_fullRationalNumerator_le
  · exact (natDegree_mappedSimplePoleNumeratorPolynomial_le
      (E := E) coeff).trans (Nat.sub_le _ _)
  · exact (natDegree_mappedSimplePoleDenominatorPolynomial
      (E := E) coeff).le

/-- The same conductor-sized bound for the cleared trace denominator. -/
theorem natDegree_fullMappedSimplePoleDenominator_le
    {p m : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Algebra (ZMod p) E]
    (coeff : ZMod p → ZMod p) :
    (fullRationalDenominator p m
      (mappedSimplePoleDenominatorPolynomial (E := E) coeff)).natDegree ≤
      ((InverseRational.poleSupport coeff).card *
          ∑ t ∈ Finset.range m, p ^ t) * (p ^ m + 1) := by
  apply natDegree_fullRationalDenominator_le
  exact (natDegree_mappedSimplePoleDenominatorPolynomial
    (E := E) coeff).le

end RationalStepanov

end Erdos387
