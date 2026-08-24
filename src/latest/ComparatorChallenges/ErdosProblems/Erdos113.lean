/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos113

def HasThreeHalvesExtremalBound {V : Type*} (H : SimpleGraph V) : Prop :=
  (fun n : ℕ ↦ (SimpleGraph.extremalNumber n H : ℝ)) =O[atTop]
    (fun n : ℕ ↦ (n : ℝ) ^ ((3 : ℝ) / 2))

def IsTwoDegenerate {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, S.Nonempty →
    ∃ v : S, (G.neighborSet v ∩ S).ncard ≤ 2

theorem not_erdos_113 :
    ¬ (∀ (V : Type) [Fintype V], ∀ H : SimpleGraph V,
      H.IsBipartite → (HasThreeHalvesExtremalBound H ↔ IsTwoDegenerate H)) := by
  sorry

end Erdos113
