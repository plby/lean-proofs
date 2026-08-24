/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter MeasureTheory Set
open scoped ENNReal

namespace Erdos1195

def IntegerRatioFree (S : Set ℝ) : Prop :=
  ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → x ≠ y → ∀ z : ℤ, x / y ≠ (z : ℝ)

noncomputable def countingFunction (S : Set ℝ) (x : ℝ) : ℝ :=
  (volume (S ∩ Ioo 0 x)).toReal

def HasErdos1195Witness (F : ℝ → ℝ) : Prop :=
  ∃ S : Set ℝ, MeasurableSet S ∧ volume S = ∞ ∧ IntegerRatioFree S ∧
    ∀ᶠ x in atTop, F x ≤ countingFunction S x

theorem erdos_1195
    (F : ℝ → ℝ)
    (hF0 : ∀ x ∈ Ici (1 : ℝ), 0 ≤ F x)
    (hmono : MonotoneOn F (Ici (1 : ℝ)))
    (hFtop : Tendsto F atTop atTop) :
    HasErdos1195Witness F ↔
      IntegrableOn (fun x => F x / x ^ 2) (Ici (1 : ℝ)) := by
  sorry

end Erdos1195
