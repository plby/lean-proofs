/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.DegreeSum
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Finset.Sym
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Monotone
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

open Function Set
open SimpleGraph

noncomputable section

namespace Erdos717

open scoped Classical in
noncomputable def chiNat {V : Type*} (G : SimpleGraph V) : ℕ :=
  G.chromaticNumber.toNat

end Erdos717

namespace Erdos717

open scoped Classical in
abbrev CliqueEdge (r : ℕ) := {e : Fin r × Fin r // e.1 < e.2}

end Erdos717

namespace Erdos717

open scoped Classical in
def walkInteriorSet {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : Set V :=
  {x | x ∈ p.support ∧ x ≠ u ∧ x ≠ v}

end Erdos717

namespace Erdos717

open scoped Classical in
structure CliqueSubdivision {V : Type*} (G : SimpleGraph V) (r : ℕ) where
  branch : Fin r ↪ V
  path : ∀ e : CliqueEdge r, G.Walk (branch e.1.1) (branch e.1.2)
  path_isPath : ∀ e, (path e).IsPath
  interior_avoids_branch : ∀ e,
    Disjoint (walkInteriorSet (path e)) (Set.range branch)
  interior_pairwise : Pairwise fun e f =>
    Disjoint (walkInteriorSet (path e)) (walkInteriorSet (path f))

end Erdos717

namespace Erdos717

open scoped Classical in
def ContainsCliqueSubdivision {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  Nonempty (CliqueSubdivision G r)

end Erdos717

namespace Erdos717

open scoped Classical in
noncomputable def cliqueSubdivisionNumber {V : Type*} [Fintype V]
    (G : SimpleGraph V) : ℕ := by
  classical
  exact Nat.findGreatest (ContainsCliqueSubdivision G) (Fintype.card V)

end Erdos717

namespace Erdos717

open scoped Classical in
def Erdos717Bound : Prop :=
  ∃ C : ℝ, 0 < C ∧
    ∀ (V : Type) [Fintype V] (G : SimpleGraph V),
      2 ≤ Fintype.card V →
      (chiNat G : ℝ) ≤
        C * (Real.sqrt (Fintype.card V : ℝ) / Real.log (Fintype.card V : ℝ)) *
          (cliqueSubdivisionNumber G : ℝ)

end Erdos717

namespace Erdos717

open scoped Classical in
theorem erdos_717 : Erdos717Bound := by
  sorry

end Erdos717

end
