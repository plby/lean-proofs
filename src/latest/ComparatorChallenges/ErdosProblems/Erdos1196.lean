/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1196

open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

def PrimitiveSet (A : Set ℕ) : Prop :=
  ∀ ⦃m n : ℕ⦄, m ∈ A → n ∈ A → m ∣ n → m = n
end PrimitiveSetsAboveX

open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open scoped ArithmeticFunction BigOperators Topology
open Filter

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open scoped ArithmeticFunction BigOperators Topology
open Filter

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open scoped ArithmeticFunction BigOperators Topology

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open scoped ArithmeticFunction BigOperators Topology

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open scoped ArithmeticFunction BigOperators Topology

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open scoped BigOperators

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open scoped ArithmeticFunction BigOperators

namespace PrimitiveSetsAboveX

end PrimitiveSetsAboveX

open Filter
open scoped Asymptotics BigOperators

def IsPrimitive {M : Type*} [CommMonoid M] (A : Set M) : Prop :=
  ∀ᵉ (x ∈ A) (y ∈ A), x ∣ y → Associated x y
end Erdos1196



open scoped ArithmeticFunction BigOperators
open scoped ArithmeticFunction BigOperators Topology
open Filter MeasureTheory
open scoped BigOperators
open Filter
open scoped Asymptotics BigOperators

namespace Erdos1196.PrimitiveSetsAboveX

open scoped Classical in
theorem mainTheorem :
    ∃ C : ℝ, ∃ x₀ : ℕ,
      ∀ ⦃x : ℕ⦄, x₀ ≤ x →
        ∀ {A : Set ℕ}, PrimitiveSet A → A ⊆ Set.Ici x →
          Summable (A.indicator (fun m : ℕ => 1 / ((m : ℝ) * Real.log (m : ℝ)))) ∧
            (∑' m : ℕ, A.indicator (fun k : ℕ => 1 / ((k : ℝ) * Real.log (k : ℝ))) m) ≤
              1 + C / Real.log (x : ℝ) := by
  sorry

end Erdos1196.PrimitiveSetsAboveX
namespace Erdos1196

open scoped Classical in
theorem erdos_1196 :
    ∃ o : ℕ → ℝ, o =o[Filter.atTop] (1 : ℕ → ℝ) ∧
      ∀ x > (0 : ℕ), ∀ A ⊆ Set.Ici x, IsPrimitive A →
        ∑' (a : A), (1 / ((a.val : ℝ).log * a)) < 1 + o x := by
  sorry

end Erdos1196
