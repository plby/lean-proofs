import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Padics.Hensel

/-!
# Newton and simple-root lifting

This file records the simple-root lifting assertion of Milne's Proposition
7.31 and the p-adic Newton theorem underlying Theorem 7.32.
-/

namespace Towers.NumberTheory.Milne

open Polynomial

noncomputable section

section Henselian

variable {A : Type*} [CommRing A] [HenselianLocalRing A]

/-- Milne, Proposition 7.31, existence clause: a simple root modulo the
maximal ideal of a Henselian local ring lifts to a root in the ring. -/
theorem simple_maximal_lifts
    (f : A[X]) (hf : f.Monic) (a0 : A)
    (hroot : f.eval a0 ∈ IsLocalRing.maximalIdeal A)
    (hsimple : IsUnit (f.derivative.eval a0)) :
    ∃ a : A, f.IsRoot a ∧ a - a0 ∈ IsLocalRing.maximalIdeal A :=
  HenselianLocalRing.is_henselian f hf a0 hroot hsimple

end Henselian

section PadicNewton

variable {p : ℕ} [Fact p.Prime]
variable {R : Type*} [CommSemiring R] [Algebra R ℤ_[p]]

/-- Milne, Theorem 7.32, in Mathlib's constructive p-adic form.  Under the
Newton inequality, a root exists; it lies in the derivative-radius ball, its
derivative has the same norm as at the starting point, and it is the unique
root in that ball. -/
theorem padic_newton_root
    (f : R[X]) (a0 : ℤ_[p])
    (hnewton : ‖f.aeval a0‖ < ‖f.derivative.aeval a0‖ ^ 2) :
    ∃ a : ℤ_[p],
      f.aeval a = 0 ∧
        ‖a - a0‖ < ‖f.derivative.aeval a0‖ ∧
          ‖f.derivative.aeval a‖ = ‖f.derivative.aeval a0‖ ∧
            ∀ b : ℤ_[p], f.aeval b = 0 →
              ‖b - a0‖ < ‖f.derivative.aeval a0‖ → b = a :=
  hensels_lemma hnewton

end PadicNewton

end

end Towers.NumberTheory.Milne
