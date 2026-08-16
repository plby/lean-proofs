import Wikipedia.SzemeredisTheorem.ArithmeticProgression.Count
import Mathlib.Data.Int.ModEq

/-!
# Unwrapping cyclic progressions in a short interval

A progression obtained by transference lives in `ZMod N`.  The prime weight
is supported on an interval much shorter than a full residue system.  In
that situation the standard representatives have second difference zero
over the integers, so they form an ordinary integer progression.
-/

namespace Wikipedia.SzemeredisTheorem

/-- The standard natural representative of the `j`th term of a cyclic
progression. -/
def cyclicAPVal {N : ℕ} [NeZero N] (a d : ZMod N) (j : ℕ) : ℕ :=
  (a + (j : ZMod N) * d).val

@[simp]
theorem cyclicAPVal_cast {N : ℕ} [NeZero N]
    (a d : ZMod N) (j : ℕ) :
    (cyclicAPVal a d j : ZMod N) = a + (j : ZMod N) * d :=
  ZMod.natCast_zmod_val _

/-- Three points in an integer interval of width `U-L` have second
difference of absolute value at most twice that width. -/
theorem abs_secondDifference_le {L U z₀ z₁ z₂ : ℤ}
    (hz₀ : L ≤ z₀ ∧ z₀ ≤ U)
    (hz₁ : L ≤ z₁ ∧ z₁ ≤ U)
    (hz₂ : L ≤ z₂ ∧ z₂ ≤ U) :
    |z₂ - 2 * z₁ + z₀| ≤ 2 * (U - L) := by
  rw [abs_le]
  constructor <;> linarith

/-- The standard representatives of a cyclic progression supported in an
interval of width less than `N/2` have vanishing integer second
differences. -/
theorem cyclicAPVal_secondDifference_eq_zero {k N : ℕ} [NeZero N]
    (a d : ZMod N) (L U : ℤ)
    (hmem :
      ∀ i : ℕ, i < k →
        L ≤ cyclicAPVal a d i ∧ cyclicAPVal a d i ≤ U)
    (hwidth : 2 * (U - L) < (N : ℤ))
    (j : ℕ) (hj : j + 2 < k) :
    (cyclicAPVal a d (j + 2) : ℤ) -
        2 * cyclicAPVal a d (j + 1) +
        cyclicAPVal a d j = 0 := by
  let z : ℤ :=
    (cyclicAPVal a d (j + 2) : ℤ) -
      2 * cyclicAPVal a d (j + 1) +
      cyclicAPVal a d j
  apply Int.eq_zero_of_abs_lt_dvd (m := (N : ℤ)) (x := z)
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    dsimp [z]
    push_cast
    simp only [cyclicAPVal_cast, Nat.cast_add, Nat.cast_ofNat]
    ring
  · exact lt_of_le_of_lt
      (abs_secondDifference_le
        (hmem j (by omega))
        (hmem (j + 1) (by omega))
        (hmem (j + 2) hj))
      hwidth

/-- A sequence with zero second differences is affine. -/
theorem eq_affine_of_secondDifference_zero
    (z : ℕ → ℤ) (k : ℕ)
    (hsecond :
      ∀ j : ℕ, j + 2 < k →
        z (j + 2) - 2 * z (j + 1) + z j = 0) :
    ∀ j : ℕ, j < k →
      z j = z 0 + (j : ℤ) * (z 1 - z 0) := by
  intro j
  induction j using Nat.twoStepInduction with
  | zero =>
      intro
      ring
  | one =>
      intro
      ring
  | more j ihj ihj₁ =>
      intro hj
      have hj₀ : j < k := by omega
      have hj₁ : j + 1 < k := by omega
      have hs := hsecond j hj
      rw [ihj hj₀, ihj₁ hj₁] at hs
      push_cast at hs ⊢
      linarith

/-- Short support converts all standard representatives of a cyclic
progression into one ordinary integer affine progression. -/
theorem cyclicAPVal_eq_affine {k N : ℕ} [NeZero N]
    (a d : ZMod N) (L U : ℤ)
    (hmem :
      ∀ j : ℕ, j < k →
        L ≤ cyclicAPVal a d j ∧ cyclicAPVal a d j ≤ U)
    (hwidth : 2 * (U - L) < (N : ℤ)) :
    ∀ j : ℕ, j < k →
      (cyclicAPVal a d j : ℤ) =
        cyclicAPVal a d 0 +
          (j : ℤ) *
            ((cyclicAPVal a d 1 : ℤ) - cyclicAPVal a d 0) := by
  apply eq_affine_of_secondDifference_zero
  intro j hj
  exact cyclicAPVal_secondDifference_eq_zero a d L U hmem hwidth j hj

/-- A nonzero cyclic common difference gives distinct zeroth and first
standard representatives. -/
theorem cyclicAPVal_one_sub_zero_ne_zero {N : ℕ} [NeZero N]
    (a d : ZMod N) (hd : d ≠ 0) :
    (cyclicAPVal a d 1 : ℤ) - cyclicAPVal a d 0 ≠ 0 := by
  intro hzero
  have hval : cyclicAPVal a d 1 = cyclicAPVal a d 0 := by
    exact_mod_cast sub_eq_zero.mp hzero
  have had : a + d = a := by
    apply ZMod.val_injective N
    simpa [cyclicAPVal] using hval
  apply hd
  apply add_left_cancel (a := a)
  simpa using had

/-- The integer common difference exposed by short-interval unwrapping is
nonzero whenever the cyclic difference is nonzero. -/
theorem cyclicAPVal_isIntegerAP {k N : ℕ} [NeZero N]
    (a d : ZMod N) (hd : d ≠ 0) (L U : ℤ)
    (hmem :
      ∀ j : ℕ, j < k →
        L ≤ cyclicAPVal a d j ∧ cyclicAPVal a d j ≤ U)
    (hwidth : 2 * (U - L) < (N : ℤ)) :
    ∃ s : ℤ, s ≠ 0 ∧
      ∀ j : ℕ, j < k →
        (cyclicAPVal a d j : ℤ) =
          cyclicAPVal a d 0 + (j : ℤ) * s := by
  refine ⟨(cyclicAPVal a d 1 : ℤ) - cyclicAPVal a d 0,
    cyclicAPVal_one_sub_zero_ne_zero a d hd, ?_⟩
  exact cyclicAPVal_eq_affine a d L U hmem hwidth

end Wikipedia.SzemeredisTheorem
