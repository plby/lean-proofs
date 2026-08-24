/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open MeasureTheory

namespace Erdos206

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

theorem erdos_206 : volume {x : ℝ | EventuallyGreedy x} = 0 := by
  sorry

end EgyptianFractions

end Erdos206
