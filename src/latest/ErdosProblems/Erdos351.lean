/- leanprover/lean4:v4.30.0  mathlib v4.30.0 -/
import Util.PolynomialEgyptianSums

/-! ## #351 wrapper -/

namespace Erdos351

open Polynomial

/-- FC-named alias for `imageSet`. -/
def imageSet (P : ℚ[X]) : Set ℚ := PolynomialEgyptianSums.imageSet P

/-- FC-named alias for `IsStronglyComplete (imageSet P)`. -/
def HasCompleteImage (P : ℚ[X]) : Prop :=
  PolynomialEgyptianSums.IsStronglyComplete (imageSet P)

/-- **`formal-conjectures` upstream form for #351** under `answer := True`.

Direct from `PolynomialEgyptianSums.corollary_7_pos_leading`. -/
theorem erdos_351 :
    True ↔ ∀ P : ℚ[X], 0 < P.natDegree → 0 < P.leadingCoeff →
      HasCompleteImage P := by
  refine ⟨fun _ P _ hlc => ?_, fun _ => trivial⟩
  exact PolynomialEgyptianSums.corollary_7_pos_leading P hlc

#print axioms erdos_351
-- 'Erdos351.erdos_351' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos351
