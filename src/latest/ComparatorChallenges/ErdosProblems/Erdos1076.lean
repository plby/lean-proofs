/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 1076

For arbitrarily large orders, there are `(5,3)`-free three-uniform
hypergraphs with normalized density greater than `1 / 6`.
-/

namespace Erdos1076

/-! ## The finite extremal problem -/

/-- A triple on a finite vertex type. -/
abbrev TripleOn (V : Type*) [DecidableEq V] := {s : Finset V // s.card = 3}

/-- A finite three-uniform hypergraph. -/
abbrev TripleSystemOn (V : Type*) [DecidableEq V] := Finset (TripleOn V)

/-- A three-uniform hypergraph on `Fin n`. -/
abbrev TripleSystem (n : ℕ) := TripleSystemOn (Fin n)

/-- The vertices spanned by a finite family of triples. -/
def verticesOn {V : Type*} [DecidableEq V]
    (C : TripleSystemOn V) : Finset V :=
  C.biUnion fun e ↦ e.1

/-- `FkFree k G` means that no `k - 2` triples of `G` span at most `k`
vertices.  For ambient order at least `k`, this is equivalent to avoiding the
family of all three-uniform hypergraphs with `k` vertices and `k - 2` edges
(isolated vertices may be added to a configuration spanning fewer vertices). -/
def FkFree {V : Type*} [DecidableEq V] (k : ℕ)
    (G : TripleSystemOn V) : Prop :=
  ∀ C : TripleSystemOn V, C ⊆ G → C.card = k - 2 →
    k < (verticesOn C).card

/-- The extremal number from Problem 1076, as a finite maximum. -/
noncomputable def extremalNumber (k n : ℕ) : ℕ :=
  by
    classical
    exact (Finset.univ : Finset (TripleSystem n)).sup fun G ↦
      if FkFree k G then G.card else 0

theorem not_erdos_1076 :
    ¬ (∀ k : ℕ, 5 ≤ k →
      Filter.Tendsto
        (fun n : ℕ ↦ (Erdos1076.extremalNumber k n : ℝ) / (n : ℝ) ^ 2)
        Filter.atTop (nhds (1 / 6 : ℝ))) := by
  sorry

end Erdos1076
