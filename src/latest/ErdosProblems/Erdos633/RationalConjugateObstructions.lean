import ErdosProblems.Erdos633.RationalAngleResidues
import Mathlib.Data.Rat.Floor

/-!
# Five explicit conjugate-angle obstructions

Angles are measured as rational fractions of pi. The fractional residues
are used together or complemented together according to their sum. Five
explicit units violate the putative outer-corner identity.

These are unconditional arithmetic obstructions. Applying them to a geometric
tiling still requires proving that conjugation preserves its actual corner
counts; no such geometric statement is postulated in this file.
-/

namespace Erdos633

def rationalConjugateAngle (α β γ : ℚ) (k : ℕ) (θ : ℚ) : ℚ :=
  if Int.fract (k * α) + Int.fract (k * β) + Int.fract (k * γ) = 1 then
    Int.fract (k * θ)
  else 1 - Int.fract (k * θ)

def RationalCornerConjugationIdentity (α β γ : ℚ) (p q : ℕ) : Prop :=
  ∀ k : ℕ, k.Coprime (4 * α.den * β.den * γ.den) →
    p * rationalConjugateAngle α β γ k α +
      q * rationalConjugateAngle α β γ k β = 1

theorem rationalConjugateAngle_sum (α β γ : ℚ) (k : ℕ)
    (hs : Int.fract (k * α) + Int.fract (k * β) + Int.fract (k * γ) = 1 ∨
      Int.fract (k * α) + Int.fract (k * β) + Int.fract (k * γ) = 2) :
    rationalConjugateAngle α β γ k α + rationalConjugateAngle α β γ k β +
      rationalConjugateAngle α β γ k γ = 1 := by
  rcases hs with hs | hs
  · simp only [rationalConjugateAngle, hs, if_true]
  · have hne : Int.fract (k * α) + Int.fract (k * β) + Int.fract (k * γ) ≠ 1 := by
      rw [hs]
      norm_num
    simp only [rationalConjugateAngle, if_neg hne]
    linarith

theorem rational_three_two_quarter_obstruction :
    ¬ RationalCornerConjugationIdentity (1 / 4) (1 / 8) (5 / 8) 3 2 := by
  intro h
  have h3 := h 3 (by norm_num)
  norm_num [rationalConjugateAngle] at h3

theorem rational_three_two_sixth_obstruction :
    ¬ RationalCornerConjugationIdentity (1 / 6) (1 / 4) (7 / 12) 3 2 := by
  intro h
  have h5 := h 5 (by norm_num)
  norm_num [rationalConjugateAngle] at h5

theorem rational_three_two_tenth_obstruction :
    ¬ RationalCornerConjugationIdentity (1 / 10) (7 / 20) (11 / 20) 3 2 := by
  intro h
  have h7 := h 7 (by norm_num)
  norm_num [rationalConjugateAngle] at h7

theorem rational_three_two_three_tenths_obstruction :
    ¬ RationalCornerConjugationIdentity (3 / 10) (1 / 20) (13 / 20) 3 2 := by
  intro h
  have h3 := h 3 (by norm_num)
  norm_num [rationalConjugateAngle] at h3

theorem rational_five_two_sixth_obstruction :
    ¬ RationalCornerConjugationIdentity (1 / 6) (1 / 12) (3 / 4) 5 2 := by
  intro h
  have h5 := h 5 (by norm_num)
  norm_num [rationalConjugateAngle] at h5

/-- Every reduced-angle candidate in the three-two case fails one of the
four explicit conjugations. -/
theorem rational_three_two_conjugation_impossible (α β γ : ℚ)
    (hangle : α = 1 / 4 ∨ α = 1 / 6 ∨ α = 1 / 10 ∨ α = 3 / 10)
    (hrel : 3 * α + 2 * β = 1) (hsum : α + β + γ = 1) :
    ¬ RationalCornerConjugationIdentity α β γ 3 2 := by
  rcases hangle with rfl | rfl | rfl | rfl
  · have hβ : β = 1 / 8 := by linarith
    have hγ : γ = 5 / 8 := by linarith
    subst β γ
    exact rational_three_two_quarter_obstruction
  · have hβ : β = 1 / 4 := by linarith
    have hγ : γ = 7 / 12 := by linarith
    subst β γ
    exact rational_three_two_sixth_obstruction
  · have hβ : β = 7 / 20 := by linarith
    have hγ : γ = 11 / 20 := by linarith
    subst β γ
    exact rational_three_two_tenth_obstruction
  · have hβ : β = 1 / 20 := by linarith
    have hγ : γ = 13 / 20 := by linarith
    subst β γ
    exact rational_three_two_three_tenths_obstruction

theorem rational_five_two_conjugation_impossible (α β γ : ℚ)
    (hangle : α = 1 / 6) (hrel : 5 * α + 2 * β = 1) (hsum : α + β + γ = 1) :
    ¬ RationalCornerConjugationIdentity α β γ 5 2 := by
  subst α
  have hβ : β = 1 / 12 := by linarith
  have hγ : γ = 3 / 4 := by linarith
  subst β γ
  exact rational_five_two_sixth_obstruction

end Erdos633
