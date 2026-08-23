/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter
open scoped Asymptotics Real SimpleGraph
open scoped BigOperators

noncomputable section

namespace Erdos113

open scoped Classical in
def HasThreeHalvesExtremalBound {V : Type*} (H : SimpleGraph V) : Prop :=
  (fun n : ℕ ↦ (SimpleGraph.extremalNumber n H : ℝ)) =O[atTop]
    (fun n : ℕ ↦ (n : ℝ) ^ ((3 : ℝ) / 2))

end Erdos113

namespace Erdos113

open scoped Classical in
def IsTwoDegenerate {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∀ S : Set V, S.Nonempty →
    ∃ v : S, (G.neighborSet v ∩ S).ncard ≤ 2

end Erdos113

namespace Erdos113

open scoped Classical in
def ErdosSimonovitsConjecture : Prop :=
  ∀ (V : Type) [Fintype V], ∀ H : SimpleGraph V,
    H.IsBipartite → (HasThreeHalvesExtremalBound H ↔ IsTwoDegenerate H)

end Erdos113

namespace Erdos113

open scoped Classical in
theorem erdos113_resolution : ¬ ErdosSimonovitsConjecture := by
  sorry

end Erdos113

end
