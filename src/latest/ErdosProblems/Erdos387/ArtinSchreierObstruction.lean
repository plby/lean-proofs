/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.PoleTranslation
import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# A simple-pole obstruction to Artin--Schreier phases

The rational Weil estimate used in BNPZ Section 10 excludes phases of the
form `g ^ p - g + c`.  The differenced reciprocal phase has a surviving
simple pole.  This file proves algebraically that these two facts are
incompatible: every finite pole of an Artin--Schreier phase has order a
multiple of `p`, whereas a simple partial fraction has pole order one.

The proof below avoids a separate valuation API.  It writes a partial
fraction over a common denominator, cross-multiplies a hypothetical
Artin--Schreier representation, cancels the linear pole factor, and evaluates
at its root.
-/

namespace Erdos387

open Polynomial

namespace InverseRational

/-- Common denominator of a finite family of simple partial fractions. -/
noncomputable def simplePoleDenominatorPolynomial
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) : (ZMod p)[X] :=
  ∏ r ∈ poleSupport coeff, (X - C r)

/-- Numerator obtained by putting a finite family of simple partial
fractions over `simplePoleDenominatorPolynomial`. -/
noncomputable def simplePoleNumeratorPolynomial
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) : (ZMod p)[X] :=
  ∑ r ∈ poleSupport coeff,
    C (coeff r) * ∏ s ∈ (poleSupport coeff).erase r, (X - C s)

/-- The common simple-pole denominator is monic. -/
theorem monic_simplePoleDenominatorPolynomial
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) :
    (simplePoleDenominatorPolynomial coeff).Monic := by
  exact monic_prod_X_sub_C (fun r : ZMod p => r) (poleSupport coeff)

/-- Its degree is exactly the number of distinct supported poles. -/
theorem natDegree_simplePoleDenominatorPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime] (coeff : ZMod p → ZMod p) :
    (simplePoleDenominatorPolynomial coeff).natDegree =
      (poleSupport coeff).card := by
  exact natDegree_finsetProd_X_sub_C_eq_card
    (poleSupport coeff) (fun r : ZMod p => r)

/-- The common numerator has degree at most one less than the pole count.
The explicit nonemptiness hypothesis is the only reason the predecessor is
the natural expression for this bound. -/
theorem natDegree_simplePoleNumeratorPolynomial_le
    {p : ℕ} [NeZero p] [Fact p.Prime] (coeff : ZMod p → ZMod p) :
    (simplePoleNumeratorPolynomial coeff).natDegree ≤
      (poleSupport coeff).card - 1 := by
  rw [simplePoleNumeratorPolynomial]
  apply natDegree_sum_le_of_forall_le
  intro r hr
  calc
    (C (coeff r) *
        ∏ s ∈ (poleSupport coeff).erase r, (X - C s)).natDegree ≤
        (∏ s ∈ (poleSupport coeff).erase r, (X - C s)).natDegree :=
      natDegree_C_mul_le _ _
    _ = ((poleSupport coeff).erase r).card :=
      natDegree_finsetProd_X_sub_C_eq_card
        ((poleSupport coeff).erase r) (fun s : ZMod p => s)
    _ = (poleSupport coeff).card - 1 := Finset.card_erase_of_mem hr

/-- Terms outside the coefficient support vanish, so the full finite-field
partial-fraction sum may be restricted exactly to that support. -/
theorem simplePolePhase_eq_sum_poleSupport
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p) (x : ZMod p) :
    simplePolePhase coeff x =
      ∑ r ∈ poleSupport coeff, coeff r * (x - r)⁻¹ := by
  classical
  unfold simplePolePhase
  apply (Finset.sum_subset (Finset.subset_univ (poleSupport coeff)) ?_).symm
  intro r _hrUniv hrSupport
  have hcoeff : coeff r = 0 := by
    simpa only [mem_poleSupport, not_ne_iff] using hrSupport
  simp only [hcoeff, zero_mul]

/-- At a supported pole, the common denominator has the corresponding
linear factor exactly once at the displayed factorization level. -/
theorem simplePoleDenominatorPolynomial_eq_mul_erase
    {p : ℕ} [NeZero p] (coeff : ZMod p → ZMod p)
    {r : ZMod p} (hr : r ∈ poleSupport coeff) :
    simplePoleDenominatorPolynomial coeff =
      (X - C r) * ∏ s ∈ (poleSupport coeff).erase r, (X - C s) := by
  exact (Finset.mul_prod_erase (poleSupport coeff)
    (fun s : ZMod p => X - C s) hr).symm

/-- The complementary product does not vanish at the removed pole. -/
theorem eval_simplePoleComplement_ne_zero
    {p : ℕ} [NeZero p] [Fact p.Prime] (coeff : ZMod p → ZMod p)
    {r : ZMod p} (_hr : r ∈ poleSupport coeff) :
    eval r (∏ s ∈ (poleSupport coeff).erase r, (X - C s)) ≠ 0 := by
  rw [eval_prod, Finset.prod_ne_zero_iff]
  intro s hs
  simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
  exact (Finset.ne_of_mem_erase hs).symm

/-- Evaluation of the common numerator at a supported pole leaves only the
summand belonging to that pole. -/
theorem eval_simplePoleNumeratorPolynomial
    {p : ℕ} [NeZero p] [Fact p.Prime] (coeff : ZMod p → ZMod p)
    {r : ZMod p} (hr : r ∈ poleSupport coeff) :
    eval r (simplePoleNumeratorPolynomial coeff) =
      coeff r *
        eval r (∏ s ∈ (poleSupport coeff).erase r, (X - C s)) := by
  classical
  rw [simplePoleNumeratorPolynomial, eval_finsetSum]
  rw [Finset.sum_eq_single r]
  · simp only [eval_mul, eval_C]
  · intro s hs hsr
    have hrs : r ∈ (poleSupport coeff).erase s :=
      Finset.mem_erase.mpr ⟨hsr.symm, hr⟩
    have hprod :
        eval r (∏ t ∈ (poleSupport coeff).erase s, (X - C t)) = 0 := by
      rw [eval_prod]
      exact Finset.prod_eq_zero hrs (by simp)
    simp only [eval_mul, eval_C, hprod, mul_zero]
  · exact fun hnot => (hnot hr).elim

/-- The common numerator is nonzero at every pole in the coefficient
support.  Thus no cancellation removes that pole. -/
theorem eval_simplePoleNumeratorPolynomial_ne_zero
    {p : ℕ} [NeZero p] [Fact p.Prime] (coeff : ZMod p → ZMod p)
    {r : ZMod p} (hr : r ∈ poleSupport coeff) :
    eval r (simplePoleNumeratorPolynomial coeff) ≠ 0 := by
  rw [eval_simplePoleNumeratorPolynomial coeff hr]
  exact mul_ne_zero ((mem_poleSupport coeff r).mp hr)
    (eval_simplePoleComplement_ne_zero coeff hr)

/-- Away from the support, the common denominator does not vanish. -/
theorem eval_simplePoleDenominatorPolynomial_ne_zero
    {p : ℕ} [NeZero p] [Fact p.Prime] (coeff : ZMod p → ZMod p)
    {x : ZMod p} (hx : x ∉ poleSupport coeff) :
    eval x (simplePoleDenominatorPolynomial coeff) ≠ 0 := by
  rw [simplePoleDenominatorPolynomial, eval_prod,
    Finset.prod_ne_zero_iff]
  intro r hr
  simp only [eval_sub, eval_X, eval_C, sub_ne_zero]
  intro hxr
  apply hx
  rwa [hxr]

/-- The common numerator equals the represented partial-fraction phase times
the common denominator at every point away from the poles. -/
theorem eval_simplePoleNumeratorPolynomial_eq_phase_mul_denominator
    {p : ℕ} [NeZero p] [Fact p.Prime] (coeff : ZMod p → ZMod p)
    {x : ZMod p} (hx : x ∉ poleSupport coeff) :
    eval x (simplePoleNumeratorPolynomial coeff) =
      simplePolePhase coeff x *
        eval x (simplePoleDenominatorPolynomial coeff) := by
  classical
  rw [simplePoleNumeratorPolynomial, eval_finsetSum,
    simplePolePhase_eq_sum_poleSupport, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [eval_mul, eval_C]
  rw [simplePoleDenominatorPolynomial_eq_mul_erase coeff hr, eval_mul]
  simp only [eval_sub, eval_X, eval_C]
  have hxr : x - r ≠ 0 := by
    rw [sub_ne_zero]
    intro h
    apply hx
    rwa [h]
  field_simp [hxr]

/-- Hence the quotient of the common polynomials evaluates to the original
simple-pole phase at every non-pole. -/
theorem simplePolePhase_eq_numerator_mul_inv_denominator
    {p : ℕ} [NeZero p] [Fact p.Prime] (coeff : ZMod p → ZMod p)
    {x : ZMod p} (hx : x ∉ poleSupport coeff) :
    simplePolePhase coeff x =
      eval x (simplePoleNumeratorPolynomial coeff) *
        (eval x (simplePoleDenominatorPolynomial coeff))⁻¹ := by
  have hden := eval_simplePoleDenominatorPolynomial_ne_zero coeff hx
  rw [eval_simplePoleNumeratorPolynomial_eq_phase_mul_denominator coeff hx,
    mul_assoc, mul_inv_cancel₀ hden, mul_one]

/-- A rational function with the displayed simple pole cannot equal
`(P / Q)^p - P / Q + c`.

This cross-multiplied formulation is precisely what a rational-character-sum
theorem needs.  Coprimality of `P,Q` is the reduced-fraction hypothesis. -/
theorem not_artinSchreier_crossMultiply_of_simplePole
    {K : Type*} [Field K] {p : ℕ} (hp : 2 ≤ p)
    {A D P Q : K[X]} {r c : K}
    (hA : eval r A ≠ 0) (hD : eval r D ≠ 0)
    (hPQ : IsCoprime P Q) :
    ¬A * Q ^ p =
      ((X - C r) * D) *
        (P ^ p - P * Q ^ (p - 1) + C c * Q ^ p) := by
  intro heq
  have hp0 : 0 < p := lt_of_lt_of_le (by omega) hp
  have hpm1 : 0 < p - 1 := Nat.sub_pos_of_lt (lt_of_lt_of_le (by omega) hp)
  by_cases hQ : eval r Q = 0
  · have hP : eval r P ≠ 0 := by
      intro hPzero
      obtain ⟨U, V, hUV⟩ := hPQ
      have hevalUV := congrArg (eval r) hUV
      simp only [eval_add, eval_mul, hPzero, hQ, mul_zero, add_zero,
        eval_one, zero_ne_one] at hevalUV
    let R : K[X] := P ^ p - P * Q ^ (p - 1) + C c * Q ^ p
    have hR : eval r R ≠ 0 := by
      simp only [R, eval_add, eval_sub, eval_pow, eval_mul, eval_C, hQ,
        zero_pow hp0.ne', zero_pow hpm1.ne', mul_zero, sub_zero, mul_zero,
        add_zero]
      exact pow_ne_zero p hP
    have hroot : Q.IsRoot r := hQ
    obtain ⟨S, hS⟩ := (dvd_iff_isRoot.mpr hroot)
    let L : K[X] := X - C r
    have hQeq : Q = L * S := by simpa only [L] using hS
    have hpdecomp : p - 1 + 1 = p := Nat.sub_add_cancel hp0
    have hwithL :
        L * (A * L ^ (p - 1) * S ^ p) = L * (D * R) := by
      calc
        L * (A * L ^ (p - 1) * S ^ p) =
            A * (L ^ (p - 1) * L) * S ^ p := by ring
        _ = A * (L ^ p * S ^ p) := by rw [← pow_succ, hpdecomp]; ring
        _ = A * (L * S) ^ p := by rw [mul_pow]
        _ = A * Q ^ p := by rw [hQeq]
        _ = ((X - C r) * D) * R := by simpa only [R] using heq
        _ = L * (D * R) := by simp only [L]; ring
    have hcancel : A * L ^ (p - 1) * S ^ p = D * R :=
      mul_left_cancel₀ (by simpa only [L] using X_sub_C_ne_zero r) hwithL
    have heval := congrArg (eval r) hcancel
    have hz : 0 = eval r D * eval r R := by
      simpa only [eval_mul, eval_pow, L, eval_sub, eval_X, eval_C,
        sub_self, zero_pow hpm1.ne', mul_zero, zero_mul] using heval
    exact (mul_ne_zero hD hR) hz.symm
  · have heval := congrArg (eval r) heq
    have hz : eval r A * eval r Q ^ p = 0 := by
      simpa only [eval_mul, eval_pow, eval_sub, eval_X, eval_C,
        sub_self, zero_mul] using heval
    exact (mul_ne_zero hA (pow_ne_zero p hQ)) hz

/-- A nonempty coefficient support supplies an explicit simple pole and hence
rules out every reduced Artin--Schreier representation of its common
partial-fraction numerator and denominator. -/
theorem not_artinSchreier_simplePolePolynomials
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (coeff : ZMod p → ZMod p) {r : ZMod p}
    (hr : r ∈ poleSupport coeff)
    (P Q : (ZMod p)[X]) (hPQ : IsCoprime P Q) (c : ZMod p) :
    ¬simplePoleNumeratorPolynomial coeff * Q ^ p =
      simplePoleDenominatorPolynomial coeff *
        (P ^ p - P * Q ^ (p - 1) + C c * Q ^ p) := by
  rw [simplePoleDenominatorPolynomial_eq_mul_erase coeff hr]
  exact not_artinSchreier_crossMultiply_of_simplePole
    ((Fact.out : p.Prime).two_le)
    (eval_simplePoleNumeratorPolynomial_ne_zero coeff hr)
    (eval_simplePoleComplement_ne_zero coeff hr) hPQ

/-- The iterated difference of a single reciprocal phase is not
Artin--Schreier whenever the source's shift and pole-cardinality hypotheses
hold. -/
theorem iteratedDifference_not_artinSchreier
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {c pole : ZMod p} (hc : c ≠ 0)
    (shifts : List (ZMod p × ZMod p))
    (hdistinct : ∀ t ∈ shifts, t.1 ≠ t.2)
    (hpow : 2 ^ shifts.length < p)
    (P Q : (ZMod p)[X]) (hPQ : IsCoprime P Q) (constant : ZMod p) :
    ¬simplePoleNumeratorPolynomial
          (iteratedDifferenceCoefficient
            (singlePoleCoefficient c pole) shifts) * Q ^ p =
      simplePoleDenominatorPolynomial
          (iteratedDifferenceCoefficient
            (singlePoleCoefficient c pole) shifts) *
        (P ^ p - P * Q ^ (p - 1) + C constant * Q ^ p) := by
  obtain ⟨r, hr⟩ :=
    singlePole_iteratedDifference_nonempty hc shifts hdistinct hpow
  exact not_artinSchreier_simplePolePolynomials _ hr P Q hPQ constant

end InverseRational

end Erdos387
