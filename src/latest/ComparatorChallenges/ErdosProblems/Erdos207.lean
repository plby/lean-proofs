import Mathlib

namespace Erdos207

abbrev TripleOn (V : Type*) [DecidableEq V] := {s : Finset V // s.card = 3}

abbrev TripleSystemOn (V : Type*) [DecidableEq V] := Finset (TripleOn V)

abbrev TripleSystem (n : ℕ) := TripleSystemOn (Fin n)

def verticesOn {V : Type*} [DecidableEq V] (C : TripleSystemOn V) : Finset V :=
  C.biUnion fun T ↦ T.1

def IsSteinerOn {V : Type*} [DecidableEq V] (H : TripleSystemOn V) : Prop :=
  ∀ u v : V, u ≠ v → ∃! T : TripleOn V, T ∈ H ∧ u ∈ T.1 ∧ v ∈ T.1

abbrev IsSteiner {n : ℕ} (H : TripleSystem n) : Prop := IsSteinerOn H

def LocallySparseOn {V : Type*} [DecidableEq V] (g : ℕ)
    (H : TripleSystemOn V) : Prop :=
  ∀ C : TripleSystemOn V, C ⊆ H → 2 ≤ C.card → C.card ≤ g →
    C.card + 3 ≤ (verticesOn C).card

abbrev LocallySparse {n : ℕ} (g : ℕ) (H : TripleSystem n) : Prop :=
  LocallySparseOn g H

def Admissible (n : ℕ) : Prop :=
  n % 6 = 1 ∨ n % 6 = 3

theorem erdos_207 :
    ∀ g : ℕ, 2 ≤ g → ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Admissible n →
      ∃ H : TripleSystem n, IsSteiner H ∧ LocallySparse g H := by
  sorry

end Erdos207
