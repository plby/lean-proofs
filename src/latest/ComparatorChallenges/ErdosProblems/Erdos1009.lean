import Mathlib

open Finset
open scoped Sym2

noncomputable section

attribute [local instance] Classical.propDecidable

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

end Erdos1009

namespace Erdos1009

abbrev TriangleOn (V : Type*) [DecidableEq V] := Erdos207.TripleOn V

end Erdos1009

namespace Erdos1009

def IsGraphTriangle {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (T : TriangleOn V) : Prop :=
  ∀ ⦃u⦄, u ∈ T.1 → ∀ ⦃v⦄, v ∈ T.1 → u ≠ v → G.Adj u v

end Erdos1009

namespace Erdos1009

def IsTrianglePacking {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (P : TriangleFamilyOn V) : Prop :=
  Erdos207.IsPackingOn P ∧ ∀ T ∈ P, IsGraphTriangle G T

end Erdos1009

namespace Erdos1009

def Erdos1009Statement : Prop :=
  ∀ c : ℝ, 0 < c → ∃ f : ℕ, ∀ (n k : ℕ) (G : SimpleGraph (Fin n)),
    G.edgeSet.ncard ≥ n ^ 2 / 4 + k →
    (k : ℝ) < c * n →
    ∃ P : TriangleFamilyOn (Fin n), IsTrianglePacking G P ∧ k ≤ P.card + f

end Erdos1009

namespace Erdos1009

theorem erdos1009 : Erdos1009Statement := by
  sorry

end Erdos1009

end
