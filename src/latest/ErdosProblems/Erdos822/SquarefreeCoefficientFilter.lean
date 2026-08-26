/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos822.ShiftedSquareResidues
import ErdosProblems.Erdos822.SymmetricScale
import Mathlib.Data.Nat.Squarefree

/-!
# Removing repeated large prime factors from shifted coefficients

The paper's medium-range root count is valid for squarefree moduli.  We
therefore record the honest finite filter which forbids a repeated prime
factor above the smooth cutoff, together with the exact consequence needed
for a common divisor whose prime factors are all above that cutoff.
-/

namespace Erdos822

/-- Odd cofactors whose shifted coefficient has no repeated prime factor
strictly above y. -/
noncomputable def largeSquarefreeShiftedOddCofactors
    (N y : ℕ) : Finset ℕ := by
  classical
  exact (oddRawCofactors N).filter fun m =>
    ∀ p : ℕ, p.Prime → y < p → ¬ p ^ 2 ∣ shiftedTotient m

@[simp]
theorem mem_largeSquarefreeShiftedOddCofactors_iff
    {N y m : ℕ} :
    m ∈ largeSquarefreeShiftedOddCofactors N y ↔
      m ∈ oddRawCofactors N ∧
        ∀ p : ℕ, p.Prime → y < p →
          ¬ p ^ 2 ∣ shiftedTotient m := by
  simp [largeSquarefreeShiftedOddCofactors]

theorem largeSquarefreeShiftedOddCofactors_subset_oddRaw
    (N y : ℕ) :
    largeSquarefreeShiftedOddCofactors N y ⊆ oddRawCofactors N := by
  intro m hm
  exact (mem_largeSquarefreeShiftedOddCofactors_iff.mp hm).1

/-- Any divisor supported above the cutoff of a filtered shifted
coefficient is squarefree. -/
theorem squarefree_of_dvd_shiftedTotient_of_largeSquarefree
    {N y m h : ℕ}
    (hm : m ∈ largeSquarefreeShiftedOddCofactors N y)
    (hh : h ∣ shiftedTotient m)
    (hlarge : ∀ p : ℕ, p.Prime → p ∣ h → y < p) :
    Squarefree h := by
  rw [Nat.squarefree_iff_prime_squarefree]
  intro p hp hpp
  have hph : p ∣ h :=
    dvd_trans (dvd_mul_right p p) hpp
  have hpLarge : y < p := hlarge p hp hph
  have hpsq : p ^ 2 ∣ shiftedTotient m := by
    rw [pow_two]
    exact dvd_trans hpp hh
  exact (mem_largeSquarefreeShiftedOddCofactors_iff.mp hm).2
    p hp hpLarge hpsq

/-- In particular, a common shifted coefficient is squarefree as soon as
all of its prime factors are above the cutoff and one endpoint passes the
large-squarefree filter. -/
theorem shiftedCoefficientGcd_squarefree_of_largeSquarefree
    {N y m m' : ℕ}
    (hm : m ∈ largeSquarefreeShiftedOddCofactors N y)
    (hlarge : ∀ p : ℕ, p.Prime →
      p ∣ shiftedCoefficientGcd m m' → y < p) :
    Squarefree (shiftedCoefficientGcd m m') := by
  apply squarefree_of_dvd_shiftedTotient_of_largeSquarefree hm
  · unfold shiftedCoefficientGcd
    exact Nat.gcd_dvd_left _ _
  · exact hlarge

end Erdos822
