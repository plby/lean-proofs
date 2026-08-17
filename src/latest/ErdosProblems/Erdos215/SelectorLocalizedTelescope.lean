/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos215.SelectorFinal
import ErdosProblems.Erdos215.SelectorPrimeExtension

/-!
# Exact arithmetic for localized correction terms

This file packages the additive arithmetic of `localizedQuotient` in the
forms used by the new--new consistency calculation (4.15a)--(4.16).  Integer
division is additive only after the relevant numerators are known to be
divisible by the local modulus; every lemma below therefore carries those
divisibility hypotheses explicitly.
-/

namespace Erdos215.Selector.LocalizedTelescope

open Erdos215.Selector

set_option relaxedAutoImplicit false
set_option autoImplicit false

noncomputable section

/-- A localized quotient of zero is zero. -/
@[simp] lemma localizedQuotient_zero (q : ℕ) (Dinv : ZMod q) :
    localizedQuotient q Dinv 0 = 0 := by
  simp [localizedQuotient]

/-- Equality-directed form of additivity.  This is convenient when the
integer numerator identity has already been proved separately. -/
lemma localizedQuotient_add_eq_of_eq
    (q : ℕ) (hq : q ≠ 0) (Dinv : ZMod q)
    (A B C : ℤ) (hA : (q : ℤ) ∣ A) (hB : (q : ℤ) ∣ B)
    (hABC : A + B = C) :
    localizedQuotient q Dinv A + localizedQuotient q Dinv B =
      localizedQuotient q Dinv C := by
  rw [← hABC, localizedQuotient_add q hq Dinv A B hA hB]

/-- The same equality-directed addition lemma with all three divisibilities
available.  The third one is logically redundant, but this signature matches
the componentwise hypotheses normally present in the selector proof. -/
lemma localizedQuotient_add_eq_of_eq_of_dvd
    (q : ℕ) (hq : q ≠ 0) (Dinv : ZMod q)
    (A B C : ℤ) (hA : (q : ℤ) ∣ A) (hB : (q : ℤ) ∣ B)
    (_hC : (q : ℤ) ∣ C) (hABC : A + B = C) :
    localizedQuotient q Dinv A + localizedQuotient q Dinv B =
      localizedQuotient q Dinv C :=
  localizedQuotient_add_eq_of_eq q hq Dinv A B C hA hB hABC

/-- Equality-directed form of negation. -/
lemma localizedQuotient_neg_eq_of_eq
    (q : ℕ) (hq : q ≠ 0) (Dinv : ZMod q)
    (A B : ℤ) (hA : (q : ℤ) ∣ A) (hAB : -A = B) :
    -localizedQuotient q Dinv A = localizedQuotient q Dinv B := by
  rw [← hAB, localizedQuotient_neg q hq Dinv A hA]

/-- Equality-directed form of subtraction. -/
lemma localizedQuotient_sub_eq_of_eq
    (q : ℕ) (hq : q ≠ 0) (Dinv : ZMod q)
    (A B C : ℤ) (hA : (q : ℤ) ∣ A) (hB : (q : ℤ) ∣ B)
    (hABC : A - B = C) :
    localizedQuotient q Dinv A - localizedQuotient q Dinv B =
      localizedQuotient q Dinv C := by
  rw [← hABC, localizedQuotient_sub q hq Dinv A B hA hB]

/-- Moving a divisible summand from the right side to the left side commutes
with the localized quotient. -/
lemma localizedQuotient_eq_sub_of_eq_add
    (q : ℕ) (hq : q ≠ 0) (Dinv : ZMod q)
    (A B C : ℤ) (hA : (q : ℤ) ∣ A) (hB : (q : ℤ) ∣ B)
    (hABC : A = B + C) :
    localizedQuotient q Dinv A - localizedQuotient q Dinv B =
      localizedQuotient q Dinv C := by
  apply localizedQuotient_sub_eq_of_eq q hq Dinv A B C hA hB
  omega

/-- A three-numerator version of additivity: the correction terms telescope
whenever their literal integer numerators do. -/
lemma localizedQuotient_add_sub_eq_of_eq
    (q : ℕ) (hq : q ≠ 0) (Dinv : ZMod q)
    (A B C T : ℤ)
    (hA : (q : ℤ) ∣ A) (hB : (q : ℤ) ∣ B) (hC : (q : ℤ) ∣ C)
    (hABC : A + B - C = T) :
    localizedQuotient q Dinv A + localizedQuotient q Dinv B -
        localizedQuotient q Dinv C =
      localizedQuotient q Dinv T := by
  have hAB : (q : ℤ) ∣ A + B := dvd_add hA hB
  calc
    localizedQuotient q Dinv A + localizedQuotient q Dinv B -
          localizedQuotient q Dinv C =
        localizedQuotient q Dinv (A + B) -
          localizedQuotient q Dinv C := by
            rw [localizedQuotient_add q hq Dinv A B hA hB]
    _ = localizedQuotient q Dinv ((A + B) - C) := by
          rw [localizedQuotient_sub q hq Dinv (A + B) C hAB hC]
    _ = localizedQuotient q Dinv T := by rw [hABC]

/-- The precise four-label correction-term telescope in (4.15a). -/
lemma localizedQuotient_four_label_telescope
    (q : ℕ) (hq : q ≠ 0) (Dinv : ZMod q)
    (j₁ j₂ j₃ j₄ : ℤ)
    (h₃₄ : (q : ℤ) ∣ j₃ - j₄) (h₁₃ : (q : ℤ) ∣ j₁ - j₃)
    (h₂₄ : (q : ℤ) ∣ j₂ - j₄) :
    localizedQuotient q Dinv (j₃ - j₄) +
          localizedQuotient q Dinv (j₁ - j₃) -
        localizedQuotient q Dinv (j₂ - j₄) =
      localizedQuotient q Dinv (j₁ - j₂) := by
  exact localizedQuotient_telescope q hq Dinv j₁ j₂ j₃ j₄ h₃₄ h₁₃ h₂₄

/-- The literal integer identity underlying the four-label telescope. -/
lemma four_label_numerator_identity (j₁ j₂ j₃ j₄ : ℤ) :
    (j₃ - j₄) + (j₁ - j₃) - (j₂ - j₄) = j₁ - j₂ := by
  ring

/-- Integer difference of two finite representatives. -/
def finIntDiff {n : ℕ} (i j : Fin n) : ℤ := (i.1 : ℤ) - (j.1 : ℤ)

@[simp] lemma finIntDiff_self {n : ℕ} (i : Fin n) : finIntDiff i i = 0 := by
  simp [finIntDiff]

lemma finIntDiff_neg {n : ℕ} (i j : Fin n) :
    finIntDiff j i = -finIntDiff i j := by
  simp only [finIntDiff]
  ring

lemma finIntDiff_add {n : ℕ} (i j k : Fin n) :
    finIntDiff i j + finIntDiff j k = finIntDiff i k := by
  simp only [finIntDiff]
  ring

lemma finIntDiff_sub {n : ℕ} (i j k : Fin n) :
    finIntDiff i j - finIntDiff k j = finIntDiff i k := by
  simp only [finIntDiff]
  ring

/-- Finite-representative form of the exact numerator identity in (4.15a). -/
lemma finIntDiff_four_label_identity {n : ℕ} (j₁ j₂ j₃ j₄ : Fin n) :
    finIntDiff j₃ j₄ + finIntDiff j₁ j₃ - finIntDiff j₂ j₄ =
      finIntDiff j₁ j₂ := by
  simp only [finIntDiff]
  ring

/-- Cast a finite-representative difference into a modular ring without
passing through natural subtraction. -/
lemma finIntDiff_cast {n q : ℕ} (i j : Fin n) :
    ((finIntDiff i j : ℤ) : ZMod q) =
      ((i.1 : ℕ) : ZMod q) - ((j.1 : ℕ) : ZMod q) := by
  simp only [finIntDiff]
  push_cast
  rfl

/-- Divisibility of a finite-representative difference is exactly equality
of the two residues modulo the divisor. -/
lemma dvd_finIntDiff_iff_cast_eq
    {n q : ℕ} (i j : Fin n) :
    (q : ℤ) ∣ finIntDiff i j ↔
      ((i.1 : ℕ) : ZMod q) = ((j.1 : ℕ) : ZMod q) := by
  rw [← sub_eq_zero]
  rw [← finIntDiff_cast]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).symm

/-- The four-label telescope specialized directly to finite labels. -/
lemma localizedQuotient_fin_telescope
    {n : ℕ} (q : ℕ) (hq : q ≠ 0) (Dinv : ZMod q)
    (j₁ j₂ j₃ j₄ : Fin n)
    (h₃₄ : (q : ℤ) ∣ finIntDiff j₃ j₄)
    (h₁₃ : (q : ℤ) ∣ finIntDiff j₁ j₃)
    (h₂₄ : (q : ℤ) ∣ finIntDiff j₂ j₄) :
    localizedQuotient q Dinv (finIntDiff j₃ j₄) +
          localizedQuotient q Dinv (finIntDiff j₁ j₃) -
        localizedQuotient q Dinv (finIntDiff j₂ j₄) =
      localizedQuotient q Dinv (finIntDiff j₁ j₂) := by
  apply localizedQuotient_add_sub_eq_of_eq q hq Dinv
    (finIntDiff j₃ j₄) (finIntDiff j₁ j₃)
    (finIntDiff j₂ j₄) (finIntDiff j₁ j₂)
    h₃₄ h₁₃ h₂₄
  exact finIntDiff_four_label_identity j₁ j₂ j₃ j₄

end

end Erdos215.Selector.LocalizedTelescope
