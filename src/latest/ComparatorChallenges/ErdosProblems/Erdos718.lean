import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open SimpleGraph

noncomputable section


namespace Erdos718

open scoped Classical in
abbrev CliqueEdge (r : ℕ) := {e : Fin r × Fin r // e.1 < e.2}

end Erdos718

namespace Erdos718

open scoped Classical in
def walkInteriorSet {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : Set V :=
  {x | x ∈ p.support ∧ x ≠ u ∧ x ≠ v}

end Erdos718

namespace Erdos718

open scoped Classical in
structure CliqueSubdivision {V : Type*} (G : SimpleGraph V) (r : ℕ) where
  branch : Fin r ↪ V
  path : ∀ e : CliqueEdge r, G.Walk (branch e.1.1) (branch e.1.2)
  path_isPath : ∀ e, (path e).IsPath
  interior_avoids_branch : ∀ e,
    Disjoint (walkInteriorSet (path e)) (Set.range branch)
  interior_pairwise : Pairwise fun e f =>
    Disjoint (walkInteriorSet (path e)) (walkInteriorSet (path f))

end Erdos718

namespace Erdos718

open scoped Classical in
def ContainsCliqueSubdivision {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  Nonempty (CliqueSubdivision G r)

end Erdos718

namespace Erdos718

open scoped Classical in
theorem erdos_718 :
    ∃ C : ℝ, 0 < C ∧
      ∀ (r : ℕ) (V : Type) [Fintype V] [Nonempty V]
        (G : SimpleGraph V),
        C * (r : ℝ) ^ 2 * (Fintype.card V : ℝ) ≤
            (G.edgeSet.ncard : ℝ) →
          ContainsCliqueSubdivision G r := by
  sorry

end Erdos718

end
