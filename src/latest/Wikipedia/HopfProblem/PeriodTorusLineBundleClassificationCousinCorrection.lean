import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousinForcing

/-!
# Verification of the common Cousin correction

Subtracting a common primitive preserves the original transition functions.
When that primitive solves the two actually constructed forcing equations,
the corrected local functions are genuinely holomorphic by the proved
two-variable Cauchy--Riemann criterion.  This file verifies the correction;
it does not postulate existence of a global primitive.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousin

open PeriodTorusLineBundleClassification

namespace Cocycle

variable {ι : Type*} (C : Cocycle ι)

def correctedCochain (u : ℂ × ℂ → ℂ) (i : ι) (x : ℂ × ℂ) : ℂ :=
  C.cochain i x - u x

theorem correctedCochain_sub (u : ℂ × ℂ → ℂ) (i j : ι) {x : ℂ × ℂ}
    (hi : x ∈ C.domain i) (hj : x ∈ C.domain j) :
    C.correctedCochain u i x - C.correctedCochain u j x = C.transition i j x := by
  calc
    C.correctedCochain u i x - C.correctedCochain u j x =
        C.cochain i x - C.cochain j x := by
      dsimp only [correctedCochain]
      ring
    _ = C.transition i j x := C.cochain_sub i j hi hj

/-- The actual common forcing equations suffice for the corrected local
functions to be holomorphic in both variables jointly. -/
theorem correctedCochain_analyticOnNhd {u : ℂ × ℂ → ℂ} (hu : ContDiff ℝ ∞ u)
    (h₁ : ∀ x, dbarFirst u x = C.forcingFirst x)
    (h₂ : ∀ x, dbarSecond u x = C.forcingSecond x) (i : ι) :
    AnalyticOnNhd ℂ (C.correctedCochain u i) (C.domain i) := by
  apply analyticOnNhd_sub_of_coordinate_dbar_eq (C.isOpen_domain i)
    ((C.cochain_contDiffOn i).differentiableOn (by simp))
    ((hu.differentiable (by simp)).differentiableOn)
  · intro x hx
    exact (C.forcingFirst_eq hx).symm.trans (h₁ x).symm
  · intro x hx
    exact (C.forcingSecond_eq hx).symm.trans (h₂ x).symm

end Cocycle

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousin
