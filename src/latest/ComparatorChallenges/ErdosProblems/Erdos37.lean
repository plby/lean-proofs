/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open scoped ENNReal NNReal Pointwise Real
open Finset Set Filter
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace
open MeasureTheory
open Filter Topology

noncomputable section

namespace Erdos37

open scoped Classical in
def positivePart (A : Set ℕ) : Set ℕ :=
  {n | 0 < n ∧ n ∈ A}

end Erdos37

namespace Erdos37

open scoped Classical in
def IsLacunary (A : Set ℕ) : Prop :=
  (positivePart A).Infinite ∧
    ∃ q : ℝ, 1 < q ∧
      ∀ i : ℕ,
        q * (Nat.nth (· ∈ positivePart A) i : ℝ) ≤
          (Nat.nth (· ∈ positivePart A) (i + 1) : ℝ)

end Erdos37

namespace Erdos37

open scoped Classical in
noncomputable abbrev sd (A : Set ℕ) : ℝ :=
  @schnirelmannDensity A (fun n => Classical.propDecidable (n ∈ A))

end Erdos37

namespace Erdos37

open scoped Classical in
def IsEssentialComponent (A : Set ℕ) : Prop :=
  ∀ B : Set ℕ,
    0 < sd B →
    sd B < 1 →
    sd B < sd (A + B)

end Erdos37

namespace Erdos37

open scoped Classical in
theorem erdos_37 :
    ∀ A : Set ℕ, IsLacunary A → ¬ IsEssentialComponent A := by
  sorry

end Erdos37

end
