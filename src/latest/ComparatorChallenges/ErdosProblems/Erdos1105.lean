/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This file audits the formal specification proposed for Erdős Problem 1105.

The classical anti-Ramsey theorem is true, but the upstream definition below colors
all of `Sym2 (Fin n)`, including diagonal pairs.  The formal path assertion is false
already for `k = n = 5`, and the formal cycle asymptotic is false already for triangles.
We give kernel-checked counterexamples to both proposed theorem types.

Mathematical details and a Leanization plan for a corrected definition are in
`tex/1105.tex`.
-/

import Mathlib

namespace Erdos1105

open SimpleGraph

/-- A graph homomorphism is rainbow when distinct source edges receive distinct colors.
This is the definition used by the upstream formal-conjectures specification. -/
def IsRainbow {α V : Type*} {H : SimpleGraph α} {G : SimpleGraph V}
    (f : H →g G) {C : Type*} (c : Sym2 V → C) : Prop :=
  Function.Injective fun e : H.edgeSet ↦ c (Sym2.map f e)

/-- The upstream anti-Ramsey definition.  Its coloring domain includes diagonal pairs. -/
noncomputable def antiRamseyNum {α : Type*} [Fintype α]
    (H : SimpleGraph α) (n : ℕ) : ℕ :=
  sSup {q | ∃ c : Sym2 (Fin n) → Fin q, Function.Surjective c ∧
    ∀ f : H →g (⊤ : SimpleGraph (Fin n)), ¬IsRainbow f c}

theorem not_erdos_1105_parts_ii_type :
    ¬(∀ (k n : ℕ), 5 ≤ k → k ≤ n →
      let ℓ := (k - 1) / 2
      let ε := if Odd k then 1 else 2
      antiRamseyNum (pathGraph k) n =
        max ((k - 2).choose 2 + 1)
          ((ℓ - 1).choose 2 + (ℓ - 1) * (n - ℓ + 1) + ε)) := by
  sorry

open Asymptotics Filter

theorem not_erdos_1105_parts_i_type :
    ¬(∀ k : ℕ, 3 ≤ k →
      ((fun n : ℕ ↦ (antiRamseyNum (cycleGraph k) n : ℝ) -
          (((k : ℝ) - 2) / 2 + 1 / ((k : ℝ) - 1)) * n) =O[atTop]
        (fun _ : ℕ ↦ (1 : ℝ)))) := by
  sorry
