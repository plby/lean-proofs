/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos1018

abbrev CliqueEdge (r : ℕ) := {e : Fin r × Fin r // e.1 < e.2}

def walkInteriorSet {V : Type*} {G : SimpleGraph V} {u v : V}
    (p : G.Walk u v) : Set V :=
  {x | x ∈ p.support ∧ x ≠ u ∧ x ≠ v}

structure CliqueSubdivision {V : Type*} (G : SimpleGraph V) (r : ℕ) where
  branch : Fin r ↪ V
  path : ∀ e : CliqueEdge r, G.Walk (branch e.1.1) (branch e.1.2)
  path_isPath : ∀ e, (path e).IsPath
  interior_avoids_branch : ∀ e,
    Disjoint (walkInteriorSet (path e)) (Set.range branch)
  interior_pairwise : Pairwise fun e f =>
    Disjoint (walkInteriorSet (path e)) (walkInteriorSet (path f))

def ContainsCliqueSubdivision {V : Type*} (G : SimpleGraph V) (r : ℕ) : Prop :=
  Nonempty (CliqueSubdivision G r)

abbrev K33Edge := Fin 3 × Fin 3

structure K33Subdivision {V : Type*} (G : SimpleGraph V) where
  left : Fin 3 ↪ V
  right : Fin 3 ↪ V
  branch_disjoint : Disjoint (Set.range left) (Set.range right)
  path : ∀ e : K33Edge, G.Walk (left e.1) (right e.2)
  path_isPath : ∀ e, (path e).IsPath
  interior_avoids_branch : ∀ e,
    Disjoint (walkInteriorSet (path e))
      (Set.range left ∪ Set.range right)
  interior_pairwise : Pairwise fun e f =>
    Disjoint (walkInteriorSet (path e))
      (walkInteriorSet (path f))

def ContainsK33Subdivision {V : Type*} (G : SimpleGraph V) : Prop :=
  Nonempty (K33Subdivision G)

def IsNonplanar {V : Type*} (G : SimpleGraph V) : Prop :=
  ContainsCliqueSubdivision G 5 ∨ ContainsK33Subdivision G

theorem erdos_1018 :
    ∀ ε : ℝ, 0 < ε → ∃ C N : ℕ, ∀ n : ℕ, N ≤ n →
      ∀ G : SimpleGraph (Fin n),
        (n : ℝ) ^ ((1 : ℝ) + ε) ≤ (G.edgeSet.ncard : ℝ) →
          ∃ S : G.Subgraph,
            S.verts.ncard ≤ C ∧ Erdos1018.IsNonplanar S.coe := by
  sorry

end Erdos1018
