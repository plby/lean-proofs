/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RationalStepanovNonvanishing
import Waring.Analytic.StepanovRootCount

/-!
# Rational Stepanov trace-fiber count

The kernel auxiliary polynomial is nonzero, has controlled degree, and has
its first `R` Hasse derivatives vanishing at every non-pole point in a fixed
trace fiber.  Root counting therefore gives the explicit fiber bound.
-/

namespace Erdos387

open Polynomial
open Waring.Analytic.Stepanov

namespace RationalStepanov

/-- Non-pole points in a fixed trace fiber of the mapped simple-pole
phase. -/
noncomputable def nonpoleTraceFiber
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {E : Type*} [Field E] [Fintype E] [Algebra (ZMod p) E]
    [FiniteDimensional (ZMod p) E]
    (coeff : ZMod p → ZMod p) (c : ZMod p) : Finset E := by
  classical
  exact Finset.univ.filter fun x : E =>
    ¬ RationalWeil.IsMappedPole coeff x ∧
      Algebra.trace (ZMod p) E
        (RationalWeil.mappedSimplePolePhase coeff x) = c

/-- Root counting plus the exact degree factorization. -/
theorem card_le_rationalTraceFiberBound_of_auxiliary
    {E : Type*} [Field E] {p h s : ℕ} (hp : 0 < p)
    {lowN lowD : E[X]}
    (hN : lowN.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    (hD : lowD.natDegree ≤ s * frobeniusOrderSum p (h + 3))
    (pole : E) (a : AuxiliaryCoefficients E p h)
    (ha : rationalAuxiliaryPolynomial p h pole lowN lowD a ≠ 0)
    (points : Finset E)
    (hvanish : ∀ x ∈ points, ∀ r < R p h,
      (hasseDeriv r
        (rationalAuxiliaryPolynomial p h pole lowN lowD a)).eval x = 0) :
    points.card ≤ rationalTraceFiberBound p h s := by
  have hroot : R p h * points.card ≤
      (rationalAuxiliaryPolynomial p h pole lowN lowD a).natDegree :=
    mul_card_le_natDegree_of_hasseDeriv_eval_eq_zero
      (points := points) (r := R p h) ha hvanish
  have hdegree := natDegree_rationalAuxiliaryPolynomial_lt
    hp hN hD pole a
  have hproduct : R p h * points.card <
      R p h * rationalTraceFiberBound p h s := by
    calc
      R p h * points.card ≤
          (rationalAuxiliaryPolynomial p h pole lowN lowD a).natDegree := hroot
      _ < rationalAuxiliaryDegreeBound p h s := hdegree
      _ = R p h * rationalTraceFiberBound p h s :=
        rationalAuxiliaryDegreeBound_eq_R_mul p h s
  exact (Nat.mul_lt_mul_left (Nat.pow_pos hp)).mp hproduct |>.le

/-- A non-pole trace fiber in the chosen even extension has the rational
Stepanov cardinality bound. -/
theorem card_nonpole_trace_fiber_le
    {p : ℕ} [NeZero p] [Fact p.Prime] (hp : 1 < p)
    (coeff : ZMod p → ZMod p)
    (hne : (InverseRational.poleSupport coeff).Nonempty)
    (hs : (InverseRational.poleSupport coeff).card < p)
    (h : ℕ) (c : ZMod p) :
    let E := FiniteField.Extension (ZMod p) p (2 * (h + 3))
    letI : Fintype E := Fintype.ofFinite E
    (nonpoleTraceFiber (E := E) coeff c).card ≤
      rationalTraceFiberBound p h
        (InverseRational.poleSupport coeff).card := by
  classical
  let E := FiniteField.Extension (ZMod p) p (2 * (h + 3))
  letI : CharP E p :=
    (Algebra.charP_iff (ZMod p) E p).mp (ZMod.charP p)
  letI : Fintype E := Fintype.ofFinite E
  let A : E[X] := mappedSimplePoleNumeratorPolynomial coeff
  let B : E[X] := mappedSimplePoleDenominatorPolynomial coeff
  let lowN := lowRationalNumerator p (h + 3) A B
  let lowD := lowRationalDenominator p (h + 3) B
  let highN := highRationalNumerator p (h + 3) A B
  let highD := highRationalDenominator p (h + 3) B
  let points : Finset E := nonpoleTraceFiber coeff c
  obtain ⟨poleBase, hpoleBase⟩ := hne
  let pole : E := algebraMap (ZMod p) E poleBase
  have hAdeg : A.natDegree ≤ (InverseRational.poleSupport coeff).card :=
    (natDegree_mappedSimplePoleNumeratorPolynomial_le
      (E := E) coeff).trans (Nat.sub_le _ _)
  have hBdeg : B.natDegree ≤ (InverseRational.poleSupport coeff).card :=
    (natDegree_mappedSimplePoleDenominatorPolynomial (E := E) coeff).le
  have hNdeg : lowN.natDegree ≤
      (InverseRational.poleSupport coeff).card *
        frobeniusOrderSum p (h + 3) := by
    exact natDegree_lowRationalNumerator_le hAdeg hBdeg
  have hDdeg : lowD.natDegree ≤
      (InverseRational.poleSupport coeff).card *
        frobeniusOrderSum p (h + 3) := by
    exact natDegree_lowRationalDenominator_le hBdeg
  obtain ⟨a, hane, hakernel⟩ := exists_nonzero_rationalAuxiliaryCoefficients
    hp hs (algebraMap (ZMod p) E c) pole lowN lowD
  have ha : rationalAuxiliaryPolynomial p h pole lowN lowD a ≠ 0 := by
    exact rationalAuxiliaryPolynomial_ne_zero
      (E := E) coeff hpoleBase hane
  have hfinrank : Module.finrank (ZMod p) E = 2 * (h + 3) := by
    simpa [E] using
      FiniteField.finrank_zmod_extension (ZMod p) p (2 * (h + 3))
  have hcard : Fintype.card E = p ^ (2 * (h + 3)) := by
    rw [Fintype.card_eq_nat_card]
    change Nat.card
      (FiniteField.Extension (ZMod p) p (2 * (h + 3))) = _
    rw [FiniteField.natCard_extension, Nat.card_zmod]
  have hvanish : ∀ x ∈ points, ∀ r < R p h,
      (hasseDeriv r
        (rationalAuxiliaryPolynomial p h pole lowN lowD a)).eval x = 0 := by
    intro x hx r hr
    have hxdata : ¬ RationalWeil.IsMappedPole coeff x ∧
        Algebra.trace (ZMod p) E
          (RationalWeil.mappedSimplePolePhase coeff x) = c := by
      simpa only [points, nonpoleTraceFiber, Finset.mem_filter,
        Finset.mem_univ, true_and] using hx
    have hxnonpole : ∀ y ∈ InverseRational.poleSupport coeff,
        x ≠ algebraMap (ZMod p) E y := by
      intro y hy hxy
      exact hxdata.1 ⟨y, hy, hxy⟩
    have hxpow : x ^ (p ^ (2 * (h + 3))) = x := by
      rw [← hcard]
      exact FiniteField.pow_card x
    have htrace :
        (fullRationalNumerator p (h + 3) A B).eval x *
            ((fullRationalDenominator p (h + 3) B).eval x)⁻¹ =
          algebraMap (ZMod p) E c := by
      rw [eval_fullRationalTrace_eq_algebraMap_trace
        hfinrank coeff x hxnonpole, hxdata.2]
    have horbit (t : ℕ) : ∀ y ∈ InverseRational.poleSupport coeff,
        x ^ (p ^ t) ≠ algebraMap (ZMod p) E y :=
      frobenius_pow_ne_mappedPole coeff hxnonpole t
    have hlow : lowD.eval x ≠ 0 := by
      change (lowRationalDenominator p (h + 3) B).eval x ≠ 0
      rw [eval_lowRationalDenominator]
      apply Finset.prod_ne_zero_iff.mpr
      intro t ht
      exact eval_mappedSimplePoleDenominatorPolynomial_ne_zero
        coeff (horbit t)
    have hhigh : highD.eval x ≠ 0 := by
      change (highRationalDenominator p (h + 3) B).eval x ≠ 0
      rw [eval_highRationalDenominator, eval_lowRationalDenominator]
      apply Finset.prod_ne_zero_iff.mpr
      intro t ht
      rw [← pow_mul, ← pow_add]
      exact eval_mappedSimplePoleDenominatorPolynomial_ne_zero
        coeff (horbit (h + 3 + t))
    have hrel : highN.eval x * lowD.eval x =
        (algebraMap (ZMod p) E c * lowD.eval x - lowN.eval x) *
          highD.eval x := by
      exact eval_high_mul_low_eq_of_fullRationalTrace
        p (h + 3) A B x (algebraMap (ZMod p) E c) hlow hhigh htrace
    apply hasseDeriv_rationalAuxiliaryPolynomial_eval_eq_zero
      hp (algebraMap (ZMod p) E c) pole hNdeg hDdeg hakernel
      hxpow hlow
    · exact eval_highRationalNumerator p (h + 3) A B x
    · exact eval_highRationalDenominator p (h + 3) B x
    · exact hrel
    · exact hr
  change points.card ≤
    rationalTraceFiberBound p h (InverseRational.poleSupport coeff).card
  exact card_le_rationalTraceFiberBound_of_auxiliary
    (Fact.out : p.Prime).pos hNdeg hDdeg pole a ha points hvanish

end RationalStepanov

end Erdos387
