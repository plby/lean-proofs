import Wikipedia.NoExoticSixSphere.HilbertSchmidtCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# Integration by parts for the Hilbert--Schmidt form

This is the fundamental theorem of calculus applied to the already verified
derivative of the actual finite-dimensional bilinear form.
-/

namespace NoExoticSixSphere.HilbertSchmidt

open GLOrthonormalization MeasureTheory

variable {n : ℕ} {V W V' W' : ℝ → Vector n →L[ℝ] Vector n}

theorem integral_innerForm_derivative
    (hV : Continuous V) (hW : Continuous W)
    (hV' : Continuous V') (hW' : Continuous W')
    (hdV : ∀ t, HasDerivAt V (V' t) t) (hdW : ∀ t, HasDerivAt W (W' t) t)
    (l u : ℝ) :
    (∫ t in l..u, innerForm (V t) (W' t)) =
      innerForm (V u) (W u) - innerForm (V l) (W l) -
        ∫ t in l..u, innerForm (V' t) (W t) := by
  have hleft : Continuous (fun t ↦ innerForm (V t) (W' t)) :=
    Continuous.comp
      (g := fun p : (Vector n →L[ℝ] Vector n) × (Vector n →L[ℝ] Vector n) ↦
        innerForm p.1 p.2) (f := fun t ↦ (V t, W' t))
      (contDiff_innerForm (n := n)).continuous (hV.prodMk hW')
  have hright : Continuous (fun t ↦ innerForm (V' t) (W t)) :=
    Continuous.comp
      (g := fun p : (Vector n →L[ℝ] Vector n) × (Vector n →L[ℝ] Vector n) ↦
        innerForm p.1 p.2) (f := fun t ↦ (V' t, W t))
      (contDiff_innerForm (n := n)).continuous (hV'.prodMk hW)
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (a := l) (b := u) (fun t _ ↦ hasDerivAt_innerForm (hdV t) (hdW t))
    ((hleft.intervalIntegrable l u).add (hright.intervalIntegrable l u))
  rw [intervalIntegral.integral_add (hleft.intervalIntegrable l u)
    (hright.intervalIntegrable l u)] at hftc
  linarith

end NoExoticSixSphere.HilbertSchmidt
