/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.ArtinSchreierObstruction
import ErdosProblems.Erdos387.InverseRationalFunction

/-!
# Partial fractions for the exact positive-shift inverse phase

InverseWeyl.iteratedInversePhase stores its shifts as natural numbers and
uses the positive increment h + 1.  The pole-survival and Artin--Schreier
modules instead use pairs of prime-field translates.  This file proves that
the two recursions are literally the same after replacing each natural shift
by the pair (h + 1, 0).
-/

namespace Erdos387

open Polynomial

namespace InverseRational

/-- Encode every positive natural shift as the pair of translates used by
the simple-pole coefficient recursion. -/
def positiveShiftPairs
    (p : ℕ) [NeZero p] (hs : List ℕ) : List (ZMod p × ZMod p) :=
  hs.map fun h => (((h + 1 : ℕ) : ZMod p), 0)

@[simp] theorem length_positiveShiftPairs
    (p : ℕ) [NeZero p] (hs : List ℕ) :
    (positiveShiftPairs p hs).length = hs.length := by
  simp [positiveShiftPairs]

/-- Prime-field version of the exact recursively differenced reciprocal
phase, with a prime-field rather than natural base point. -/
noncomputable def zmodIteratedInversePhase
    (p : ℕ) [NeZero p] (c a : ZMod p) :
    List ℕ → ZMod p → ZMod p
  | [], x => c * (a + x)⁻¹
  | h :: hs, x =>
      zmodIteratedInversePhase p c a hs
          (x + ((h + 1 : ℕ) : ZMod p)) -
        zmodIteratedInversePhase p c a hs x

/-- Evaluating the prime-field recursion at a natural residue recovers the
original InverseWeyl phase exactly. -/
theorem zmodIteratedInversePhase_natCast
    (p : ℕ) [NeZero p] (c a : ZMod p) (hs : List ℕ) (x : ℕ) :
    zmodIteratedInversePhase p c a hs (x : ZMod p) =
      InverseWeyl.iteratedInversePhase p c a hs x := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih =>
      simp only [zmodIteratedInversePhase,
        InverseWeyl.iteratedInversePhase]
      rw [show (x : ZMod p) + ((h + 1 : ℕ) : ZMod p) =
          ((x + h + 1 : ℕ) : ZMod p) by push_cast; ring,
        ih, ih]

/-- Paired translate-differencing by (h+1,0) is the same recursion as
positive-shift differencing. -/
theorem iteratedTranslateDifference_positiveShiftPairs
    {p : ℕ} [NeZero p] (c a : ZMod p) (hs : List ℕ) (x : ZMod p) :
    iteratedTranslateDifference
        (fun y : ZMod p => c * (a + y)⁻¹)
        (positiveShiftPairs p hs) x =
      zmodIteratedInversePhase p c a hs x := by
  induction hs generalizing x with
  | nil => rfl
  | cons h hs ih =>
      simp only [positiveShiftPairs, List.map_cons,
        iteratedTranslateDifference, zmodIteratedInversePhase,
        add_zero]
      change iteratedTranslateDifference
          (fun y : ZMod p => c * (a + y)⁻¹)
            (positiveShiftPairs p hs) (x + ((h + 1 : ℕ) : ZMod p)) -
          iteratedTranslateDifference
            (fun y : ZMod p => c * (a + y)⁻¹)
              (positiveShiftPairs p hs) x = _
      rw [ih, ih]

/-- The iterated coefficient family represents the exact positive-shift
inverse phase. -/
theorem simplePolePhase_iteratedPositiveShiftCoefficient
    {p : ℕ} [NeZero p] (c a : ZMod p) (hs : List ℕ) (x : ZMod p) :
    simplePolePhase
        (iteratedDifferenceCoefficient
          (singlePoleCoefficient c (-a)) (positiveShiftPairs p hs)) x =
      zmodIteratedInversePhase p c a hs x := by
  rw [simplePolePhase_iteratedDifferenceCoefficient,
    show simplePolePhase (singlePoleCoefficient c (-a)) =
        (fun y : ZMod p => c * (a + y)⁻¹) by
      funext y
      exact simplePolePhase_singlePoleCoefficient_neg c a y]
  exact iteratedTranslateDifference_positiveShiftPairs c a hs x

/-- The common partial-fraction polynomials evaluate to the exact positive
shift phase away from their finite pole support. -/
theorem zmodIteratedInversePhase_eq_commonFraction
    {p : ℕ} [NeZero p] [Fact p.Prime]
    (c a : ZMod p) (hs : List ℕ) {x : ZMod p}
    (hx : x ∉ poleSupport
      (iteratedDifferenceCoefficient
        (singlePoleCoefficient c (-a)) (positiveShiftPairs p hs))) :
    zmodIteratedInversePhase p c a hs x =
      Polynomial.eval x (simplePoleNumeratorPolynomial
        (iteratedDifferenceCoefficient
          (singlePoleCoefficient c (-a)) (positiveShiftPairs p hs))) *
      (Polynomial.eval x (simplePoleDenominatorPolynomial
        (iteratedDifferenceCoefficient
          (singlePoleCoefficient c (-a)) (positiveShiftPairs p hs))))⁻¹ := by
  rw [← simplePolePhase_iteratedPositiveShiftCoefficient c a hs x]
  exact simplePolePhase_eq_numerator_mul_inv_denominator _ hx

/-- If every positive increment is smaller than the prime, every encoded
translate pair is genuinely distinct. -/
theorem positiveShiftPairs_distinct
    {p : ℕ} [NeZero p] [Fact p.Prime] (hs : List ℕ)
    (hshift : ∀ h ∈ hs, h + 1 < p) :
    ∀ t ∈ positiveShiftPairs p hs, t.1 ≠ t.2 := by
  intro t ht
  obtain ⟨h, hh, rfl⟩ := List.mem_map.mp ht
  simp only [ne_eq]
  rw [show (((h + 1 : ℕ) : ZMod p) = 0) ↔ p ∣ h + 1 by
    exact ZMod.natCast_eq_zero_iff (h + 1) p]
  exact Nat.not_dvd_of_pos_of_lt (by omega) (hshift h hh)

/-- The exact positive-shift phase retains a pole under the numerical
hypotheses used by the Weyl process. -/
theorem positiveShift_iteratedDifference_nonempty
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {c a : ZMod p} (hc : c ≠ 0) (hs : List ℕ)
    (hshift : ∀ h ∈ hs, h + 1 < p)
    (hpow : 2 ^ hs.length < p) :
    (poleSupport
      (iteratedDifferenceCoefficient
        (singlePoleCoefficient c (-a))
        (positiveShiftPairs p hs))).Nonempty := by
  apply singlePole_iteratedDifference_nonempty hc
  · exact positiveShiftPairs_distinct hs hshift
  · simpa using hpow

/-- The number of distinct poles of the exact positive-shift phase is at
most the full `2^j` subset-sum envelope. -/
theorem card_positiveShift_poleSupport_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {c a : ZMod p} (hc : c ≠ 0) (hs : List ℕ) :
    (poleSupport
      (iteratedDifferenceCoefficient
        (singlePoleCoefficient c (-a))
        (positiveShiftPairs p hs))).card ≤ 2 ^ hs.length := by
  calc
    (poleSupport
      (iteratedDifferenceCoefficient
        (singlePoleCoefficient c (-a))
        (positiveShiftPairs p hs))).card ≤
        2 ^ (positiveShiftPairs p hs).length *
          (poleSupport (singlePoleCoefficient c (-a))).card :=
      card_poleSupport_iteratedDifferenceCoefficient_le _ _
    _ = 2 ^ hs.length := by
      rw [length_positiveShiftPairs,
        poleSupport_singlePoleCoefficient (pole := -a) hc]
      simp

/-- The denominator conductor of the exact positive-shift common fraction
is at most `2^j`. -/
theorem natDegree_positiveShift_denominator_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {c a : ZMod p} (hc : c ≠ 0) (hs : List ℕ) :
    (simplePoleDenominatorPolynomial
      (iteratedDifferenceCoefficient
        (singlePoleCoefficient c (-a))
        (positiveShiftPairs p hs))).natDegree ≤ 2 ^ hs.length := by
  rw [natDegree_simplePoleDenominatorPolynomial]
  exact card_positiveShift_poleSupport_le hc hs

/-- The numerator conductor obeys the same `2^j` envelope. -/
theorem natDegree_positiveShift_numerator_le
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {c a : ZMod p} (hc : c ≠ 0) (hs : List ℕ) :
    (simplePoleNumeratorPolynomial
      (iteratedDifferenceCoefficient
        (singlePoleCoefficient c (-a))
        (positiveShiftPairs p hs))).natDegree ≤ 2 ^ hs.length := by
  exact (natDegree_simplePoleNumeratorPolynomial_le _).trans
    ((Nat.sub_le _ _).trans (card_positiveShift_poleSupport_le hc hs))

/-- Consequently the common fraction for the exact positive-shift inverse
phase is not a reduced Artin--Schreier phase. -/
theorem positiveShift_not_artinSchreier
    {p : ℕ} [NeZero p] [Fact p.Prime]
    {c a : ZMod p} (hc : c ≠ 0) (hs : List ℕ)
    (hshift : ∀ h ∈ hs, h + 1 < p)
    (hpow : 2 ^ hs.length < p)
    (P Q : (ZMod p)[X]) (hPQ : IsCoprime P Q) (constant : ZMod p) :
    ¬simplePoleNumeratorPolynomial
          (iteratedDifferenceCoefficient
            (singlePoleCoefficient c (-a))
            (positiveShiftPairs p hs)) * Q ^ p =
      simplePoleDenominatorPolynomial
          (iteratedDifferenceCoefficient
            (singlePoleCoefficient c (-a))
            (positiveShiftPairs p hs)) *
        (P ^ p - P * Q ^ (p - 1) + Polynomial.C constant * Q ^ p) := by
  exact iteratedDifference_not_artinSchreier hc
    (positiveShiftPairs p hs) (positiveShiftPairs_distinct hs hshift)
    (by simpa using hpow) P Q hPQ constant

end InverseRational

end Erdos387
