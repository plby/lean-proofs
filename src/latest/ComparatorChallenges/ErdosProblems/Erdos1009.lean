/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

namespace Erdos207

abbrev TripleOn (V : Type*) [DecidableEq V] := {s : Finset V // s.card = 3}

abbrev TripleSystemOn (V : Type*) [DecidableEq V] := Finset (TripleOn V)

def IsPackingOn {V : Type*} [DecidableEq V]
    (C : TripleSystemOn V) : Prop :=
  ∀ u v : V, u ≠ v → ∀ T ∈ C, u ∈ T.1 → v ∈ T.1 →
    ∀ U ∈ C, u ∈ U.1 → v ∈ U.1 → T = U

end Erdos207

namespace Erdos1009

abbrev TriangleFamilyOn (V : Type*) [DecidableEq V] := Erdos207.TripleSystemOn V

abbrev TriangleOn (V : Type*) [DecidableEq V] := Erdos207.TripleOn V

def IsGraphTriangle {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (T : TriangleOn V) : Prop :=
  ∀ ⦃u⦄, u ∈ T.1 → ∀ ⦃v⦄, v ∈ T.1 → u ≠ v → G.Adj u v

def IsTrianglePacking {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (P : TriangleFamilyOn V) : Prop :=
  Erdos207.IsPackingOn P ∧ ∀ T ∈ P, IsGraphTriangle G T

theorem erdos_1009 :
    ∀ c : ℝ, 0 < c → ∃ f : ℕ, ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
      G.edgeSet.ncard ≥ n ^ 2 / 4 + k →
      (k : ℝ) < c * n →
      ∃ P : Erdos1009.TriangleFamilyOn (Fin n), Erdos1009.IsTrianglePacking G P ∧ k ≤ P.card + f := by
  sorry

end Erdos1009
