/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

noncomputable section

namespace Erdos185

open scoped Classical in
abbrev Word (n : ℕ) := Fin n → Fin 3

end Erdos185

namespace Erdos185

open scoped Classical in
def toRealPoint {n : ℕ} (x : Word n) : Fin n → ℝ :=
  fun i ↦ ((x i : ℕ) : ℝ)

end Erdos185

namespace Erdos185

open scoped Classical in
def IsMoserSet {n : ℕ} (A : Finset (Word n)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ A, ∀ z ∈ A,
    x ≠ y → x ≠ z → y ≠ z →
      ¬ Collinear ℝ
        ({toRealPoint x, toRealPoint y, toRealPoint z} : Set (Fin n → ℝ))

end Erdos185

namespace Erdos185

open scoped Classical in
noncomputable def candidates (n : ℕ) : Finset (Finset (Word n)) := by
  classical
  exact (Finset.univ : Finset (Word n)).powerset.filter IsMoserSet

end Erdos185

namespace Erdos185

open scoped Classical in
noncomputable def f3 (n : ℕ) : ℕ :=
  (candidates n).sup Finset.card

end Erdos185

namespace Erdos185

open scoped Classical in
theorem erdos_185 :
    Asymptotics.IsLittleO Filter.atTop
      (fun n : ℕ ↦ (f3 n : ℝ))
      (fun n : ℕ ↦ (3 : ℝ) ^ n) := by
  sorry

end Erdos185

end
