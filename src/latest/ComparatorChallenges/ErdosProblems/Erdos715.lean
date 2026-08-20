import Mathlib

open Finset Fintype
open scoped Classical

namespace Erdos182

/-- A nonempty, not necessarily induced or spanning, regular subgraph. -/
def ContainsRegularSubgraph {V : Type*} [Fintype V]
    (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ H : G.Subgraph, H.verts.Nonempty ∧
    ∀ v : H.verts, (H.coe.neighborSet v).ncard = k

end Erdos182

namespace Erdos715

open Erdos182

variable {V : Type*} [Fintype V]

/-- Every finite nonempty simple 4-regular graph contains a nonempty
3-regular subgraph. -/
theorem erdos_715 [Nonempty V] (G : SimpleGraph V)
    (hreg : G.IsRegularOfDegree 4) : ContainsRegularSubgraph G 3 := by
  sorry

universe u

/-- Every finite nonempty simple regular graph of this degree contains
a nonempty cubic subgraph. -/
def IsCubicForcingDegree (r : ℕ) : Prop :=
  ∀ (W : Type u) [Fintype W] [Nonempty W], ∀ G : SimpleGraph W,
    G.IsRegularOfDegree r → ContainsRegularSubgraph G 3

/-- There exists a cubic-forcing degree. -/
theorem erdos_715_exists_degree : ∃ r : ℕ, IsCubicForcingDegree.{u} r := by
  sorry

end Erdos715
