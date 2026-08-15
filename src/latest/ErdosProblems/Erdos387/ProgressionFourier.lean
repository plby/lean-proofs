/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.AdditiveCharacterOrthogonality
import Waring.Analytic.FourierCoefficientSum

/-!
# Exact finite Fourier expansion of progression counts

The difficult Section 8--10 estimates cannot sum the absolute `+2` endpoint
error from elementary progression counting.  This file keeps the endpoint
oscillation: membership in one residue class is expanded exactly by additive
characters, on an arbitrary finite set of natural numbers.
-/

namespace Erdos387

open scoped BigOperators ComplexConjugate

namespace ProgressionFourier

/-- Natural numbers in `s` that occupy the residue class `a (mod q)`. -/
def residueClass (q : ℕ) [NeZero q] (s : Finset ℕ) (a : ZMod q) :
    Finset ℕ :=
  s.filter fun n => (n : ZMod q) = a

/-- The Fourier coefficient of a finite natural-number set modulo `q`. -/
noncomputable def coefficient (q : ℕ) [NeZero q]
    (s : Finset ℕ) (h : ZMod q) : ℂ :=
  ∑ n ∈ s, ZMod.stdAddChar (h * (n : ZMod q))

theorem sum_character_sub (q : ℕ) [NeZero q]
    (n : ℕ) (a : ZMod q) :
    (∑ h : ZMod q,
        ZMod.stdAddChar (h * ((n : ZMod q) - a))) =
      if (n : ZMod q) = a then (q : ℂ) else 0 := by
  simpa [sub_eq_zero] using
    AdditiveOrthogonality.sum_stdAddChar_mul q ((n : ZMod q) - a)

/-- Orthogonality before dividing by the modulus. -/
theorem modulus_mul_card_residueClass
    (q : ℕ) [NeZero q] (s : Finset ℕ) (a : ZMod q) :
    (q : ℂ) * ((residueClass q s a).card : ℂ) =
      ∑ h : ZMod q, ∑ n ∈ s,
        ZMod.stdAddChar (h * ((n : ZMod q) - a)) := by
  classical
  rw [Finset.sum_comm]
  calc
    (q : ℂ) * ((residueClass q s a).card : ℂ) =
        ∑ n ∈ s, if (n : ZMod q) = a then (q : ℂ) else 0 := by
      rw [show (∑ n ∈ s, if (n : ZMod q) = a then (q : ℂ) else 0) =
          (q : ℂ) *
            ∑ n ∈ s, if (n : ZMod q) = a then (1 : ℂ) else 0 by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        split <;> simp_all]
      rw [Finset.sum_boole]
      rfl
    _ = ∑ n ∈ s, ∑ h : ZMod q,
          ZMod.stdAddChar (h * ((n : ZMod q) - a)) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [sum_character_sub]

/-- Exact Fourier inversion for a progression count. -/
theorem card_residueClass_eq
    (q : ℕ) [NeZero q] (s : Finset ℕ) (a : ZMod q) :
    (((residueClass q s a).card : ℕ) : ℂ) =
      (q : ℂ)⁻¹ *
        ∑ h : ZMod q, ∑ n ∈ s,
          ZMod.stdAddChar (h * ((n : ZMod q) - a)) := by
  have hq : (q : ℂ) ≠ 0 := by
    exact_mod_cast NeZero.ne q
  apply (mul_left_cancel₀ hq)
  rw [← mul_assoc, mul_inv_cancel₀ hq, one_mul]
  exact modulus_mul_card_residueClass q s a

/-- Split the phase into the Fourier coefficient of `s` and the residue
class phase. -/
theorem sum_character_sub_eq_phase_mul_coefficient
    (q : ℕ) [NeZero q] (s : Finset ℕ) (a h : ZMod q) :
    (∑ n ∈ s, ZMod.stdAddChar (h * ((n : ZMod q) - a))) =
      ZMod.stdAddChar (-h * a) * coefficient q s h := by
  rw [coefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- The source-facing exact progression formula: zero frequency plus all
nonzero frequencies, with the interval/set coefficient separated from the
CRT residue phase. -/
theorem card_residueClass_eq_phase_sum
    (q : ℕ) [NeZero q] (s : Finset ℕ) (a : ZMod q) :
    (((residueClass q s a).card : ℕ) : ℂ) =
      (q : ℂ)⁻¹ *
        ∑ h : ZMod q,
          ZMod.stdAddChar (-h * a) * coefficient q s h := by
  rw [card_residueClass_eq]
  congr 1
  apply Finset.sum_congr rfl
  intro h hh
  exact sum_character_sub_eq_phase_mul_coefficient q s a h

/-- Integer analogue, used directly for half-open analytic intervals. -/
def intResidueClass (q : ℕ) [NeZero q] (s : Finset ℤ) (a : ZMod q) :
    Finset ℤ :=
  s.filter fun n => (n : ZMod q) = a

/-- Positive-sign Fourier coefficient of a finite integer set. -/
noncomputable def intCoefficient (q : ℕ) [NeZero q]
    (s : Finset ℤ) (h : ZMod q) : ℂ :=
  ∑ n ∈ s, ZMod.stdAddChar (h * (n : ZMod q))

theorem int_modulus_mul_card_residueClass
    (q : ℕ) [NeZero q] (s : Finset ℤ) (a : ZMod q) :
    (q : ℂ) * ((intResidueClass q s a).card : ℂ) =
      ∑ h : ZMod q, ∑ n ∈ s,
        ZMod.stdAddChar (h * ((n : ZMod q) - a)) := by
  classical
  rw [Finset.sum_comm]
  calc
    (q : ℂ) * ((intResidueClass q s a).card : ℂ) =
        ∑ n ∈ s, if (n : ZMod q) = a then (q : ℂ) else 0 := by
      rw [show (∑ n ∈ s, if (n : ZMod q) = a then (q : ℂ) else 0) =
          (q : ℂ) *
            ∑ n ∈ s, if (n : ZMod q) = a then (1 : ℂ) else 0 by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        split <;> simp_all]
      rw [Finset.sum_boole]
      rfl
    _ = ∑ n ∈ s, ∑ h : ZMod q,
          ZMod.stdAddChar (h * ((n : ZMod q) - a)) := by
      apply Finset.sum_congr rfl
      intro n hn
      symm
      simpa [sub_eq_zero] using
        AdditiveOrthogonality.sum_stdAddChar_mul q ((n : ZMod q) - a)

theorem int_sum_character_sub_eq_phase_mul_coefficient
    (q : ℕ) [NeZero q] (s : Finset ℤ) (a h : ZMod q) :
    (∑ n ∈ s, ZMod.stdAddChar (h * ((n : ZMod q) - a))) =
      ZMod.stdAddChar (-h * a) * intCoefficient q s h := by
  rw [intCoefficient, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [← AddChar.map_add_eq_mul]
  congr 1
  ring

/-- Exact character expansion on an arbitrary finite integer set. -/
theorem int_card_residueClass_eq_phase_sum
    (q : ℕ) [NeZero q] (s : Finset ℤ) (a : ZMod q) :
    (((intResidueClass q s a).card : ℕ) : ℂ) =
      (q : ℂ)⁻¹ *
        ∑ h : ZMod q,
          ZMod.stdAddChar (-h * a) * intCoefficient q s h := by
  have hq : (q : ℂ) ≠ 0 := by
    exact_mod_cast NeZero.ne q
  apply (mul_left_cancel₀ hq)
  rw [← mul_assoc, mul_inv_cancel₀ hq, one_mul]
  rw [int_modulus_mul_card_residueClass]
  apply Finset.sum_congr rfl
  intro h hh
  exact int_sum_character_sub_eq_phase_mul_coefficient q s a h

/-- Our positive-sign interval coefficient is the existing checked
negative-sign coefficient at the negated frequency. -/
theorem intCoefficient_Ioc
    (q : ℕ) [NeZero q] (M : ℤ) (m : ℕ) (h : ZMod q) :
    intCoefficient q (Finset.Ioc M (M + m)) h =
      Waring.Analytic.intervalFourierCoefficient M m (-h) := by
  unfold intCoefficient Waring.Analytic.intervalFourierCoefficient
  apply Finset.sum_congr rfl
  intro x hx
  congr 1
  ring

/-- The checked logarithmic `L¹` interval-kernel bound, transported to the
positive-sign convention of the progression formula. -/
theorem sum_norm_intCoefficient_Ioc_le
    (q : ℕ) [NeZero q] (M : ℤ) (m : ℕ) (hm : m ≤ q) :
    (∑ h : ZMod q,
        ‖intCoefficient q (Finset.Ioc M (M + m)) h‖) ≤
      (q : ℝ) * (Real.log q + 1) := by
  simp_rw [intCoefficient_Ioc]
  calc
    (∑ h : ZMod q,
        ‖Waring.Analytic.intervalFourierCoefficient M m (-h)‖) =
        ∑ h : ZMod q,
          ‖Waring.Analytic.intervalFourierCoefficient M m h‖ := by
      exact Fintype.sum_equiv (Equiv.neg (ZMod q)) _ _ (fun _h => rfl)
    _ ≤ (q : ℝ) * (Real.log q + 1) :=
      Waring.Analytic.sum_norm_intervalFourierCoefficient_le q M m hm

end ProgressionFourier

end Erdos387
