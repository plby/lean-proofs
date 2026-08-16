import Mathlib

namespace Erdos206

set_option linter.style.setOption false
set_option linter.flexible false

open scoped BigOperators ENNReal
open Finset MeasureTheory Set

namespace EgyptianFractions

noncomputable def egyptianSum (S : Finset ℕ) : ℝ :=
  S.sum (fun m => (1 : ℝ) / m)

def ValidEgyptian (S : Finset ℕ) : Prop :=
  ∀ m ∈ S, 0 < m

def IsUnderapprox (S : Finset ℕ) (x : ℝ) : Prop :=
  ValidEgyptian S ∧ egyptianSum S < x

def IsBestNTerm (S : Finset ℕ) (n : ℕ) (x : ℝ) : Prop :=
  S.card = n ∧ IsUnderapprox S x ∧
    ∀ T : Finset ℕ, T.card = n → IsUnderapprox T x → egyptianSum T ≤ egyptianSum S

def EventuallyGreedy (x : ℝ) : Prop :=
  x > 0 ∧ ∃ (m : ℕ → ℕ), StrictMono m ∧ (∀ k, 0 < m k) ∧
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      IsBestNTerm (Finset.image m (Finset.range n)) n x
end EgyptianFractions

end Erdos206

attribute [local instance] Classical.propDecidable

open scoped BigOperators ENNReal
open Finset MeasureTheory Set

namespace Erdos206.EgyptianFractions

theorem erdos_206 : volume {x : ℝ | EventuallyGreedy x} = 0 := by
  sorry

end Erdos206.EgyptianFractions
