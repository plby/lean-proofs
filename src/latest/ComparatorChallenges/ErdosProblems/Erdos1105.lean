/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1105

open SimpleGraph Asymptotics Filter

/-- A copy is rainbow if distinct source edges receive distinct colors. -/
def IsRainbow {α V C : Type*} {H : SimpleGraph α} {G : SimpleGraph V}
    (f : H.Copy G) (c : G.edgeSet → C) : Prop :=
  Function.Injective (c ∘ f.mapEdgeSet)

/-- The maximum number of colors actually used on edges of `K_n` without a rainbow `H`. -/
noncomputable def antiRamseyNum {α : Type*} [Fintype α]
    (H : SimpleGraph α) (n : ℕ) : ℕ :=
  sSup {q | ∃ c : (⊤ : SimpleGraph (Fin n)).edgeSet → Fin q,
    Function.Surjective c ∧ ∀ f : H.Copy (⊤ : SimpleGraph (Fin n)), ¬IsRainbow f c}

def CycleStatement : Prop :=
  ∀ k : ℕ, 3 ≤ k →
    ((fun n : ℕ ↦ (antiRamseyNum (cycleGraph k) n : ℝ) -
        (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * n) =O[atTop]
      (fun _ : ℕ ↦ (1 : ℝ)))

def PathStatement : Prop :=
  ∀ (k n : ℕ), 5 ≤ k → k ≤ n →
    let ℓ := (k - 1) / 2
    let ε := if Odd k then 1 else 2
    antiRamseyNum (pathGraph k) n =
      max ((k - 2).choose 2 + 1)
        ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε)

theorem erdos_1105_parts_i : CycleStatement := by
  sorry

theorem erdos_1105_parts_ii : PathStatement := by
  sorry

end Erdos1105
