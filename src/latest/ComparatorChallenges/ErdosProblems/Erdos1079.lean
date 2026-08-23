/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

/-!
# Erdős Problem 1079

We prove the dense-neighbourhood extension of Turán's theorem.  In fact, the witness can be
chosen to have maximum degree.  At the strict Turán threshold the neighbourhood inequality is
strict, which is Bondy's strengthening of the Bollobás--Thomason result.
-/

open Finset Fintype
open scoped Classical SimpleGraph

namespace Erdos1079

attribute [local instance] Fintype.ofFinite

/-- The extremal number `ex(n, K_r)`. -/
noncomputable def cliqueExtremalNumber (n r : ℕ) : ℕ :=
  SimpleGraph.extremalNumber n (⊤ : SimpleGraph (Fin r))

/-- The number of edges of a finite graph, stated without a decidability parameter. -/
noncomputable def edgeCount {V : Type*} [Finite V] (G : SimpleGraph V) : ℕ :=
  Nat.card G.edgeSet

/-- The graph induced by the open neighbourhood of `v`. -/
abbrev link {V : Type*} [Finite V] (G : SimpleGraph V) (v : V) :
    SimpleGraph (G.neighborFinset v) :=
  G.induce (G.neighborFinset v)

/-- The number of edges spanned by the open neighbourhood of `v`. -/
noncomputable def linkEdgeCount {V : Type*} [Finite V]
    (G : SimpleGraph V) (v : V) : ℕ :=
  {e : Sym2 V | e ∈ G.edgeSet ∧ ∀ x, x ∈ e → G.Adj v x}.ncard

theorem erdos_problem_1079_strict {n r : ℕ} (hr : 4 ≤ r) (hn : 2 ≤ n)
    (G : SimpleGraph (Fin n))
    (hG : cliqueExtremalNumber n r < edgeCount G) :
    ∃ v : Fin n,
      G.degree v = G.maxDegree ∧
      n ≤ 2 * G.degree v ∧
      cliqueExtremalNumber (G.degree v) (r - 1) < linkEdgeCount G v := by
  sorry

end Erdos1079
