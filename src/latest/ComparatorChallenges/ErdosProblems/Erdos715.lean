/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos182

/-- A nonempty, not necessarily induced or spanning, regular subgraph. -/
def ContainsRegularSubgraph {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ H : G.Subgraph, H.verts.Nonempty ∧
    ∀ v : H.verts, (H.coe.neighborSet v).ncard = k

end Erdos182

namespace Erdos715

variable {V : Type*} [Fintype V]

open scoped Classical in
/-- Every finite nonempty simple 4-regular graph contains a nonempty
3-regular subgraph. -/
theorem erdos_715 [Nonempty V] (G : SimpleGraph V)
    (hreg : G.IsRegularOfDegree 4) : Erdos182.ContainsRegularSubgraph G 3 := by
  sorry

universe u

open scoped Classical in
/-- Every finite nonempty simple regular graph of this degree contains
a nonempty cubic subgraph. -/
def IsCubicForcingDegree (r : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [Nonempty W], ∀ G : SimpleGraph W,
    G.IsRegularOfDegree r → Erdos182.ContainsRegularSubgraph G 3

/-- There exists a cubic-forcing degree. -/
theorem erdos_715_exists_degree : ∃ r : ℕ, IsCubicForcingDegree.{u} r := by
  sorry

end Erdos715
