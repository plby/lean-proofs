/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 916.
https://www.erdosproblems.com/forum/thread/916

Informal authors:
- Carsten Thomassen

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos916.md
-/
import ErdosProblems.Erdos916.AHTSourceTheorem66
import ErdosProblems.Erdos916.AHTFinalAssembly

namespace Erdos916

universe u

/-- Erdős Problem 916: a finite simple graph on at least four vertices with
`2n - 2` edges contains a cycle and an exterior vertex adjacent to at least
three vertices of that cycle. -/
theorem erdos_916 {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 4 ≤ Fintype.card V)
    (hedges : G.edgeFinset.card = 2 * Fintype.card V - 2) :
    HasWheelWitness G := by
  exact erdos_916_of_ahtTheorem66 aht_theorem66 G hcard hedges

/-- Ununderscored alias for the public Erdős 916 theorem. -/
theorem erdos916 {V : Type u} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hcard : 4 ≤ Fintype.card V)
    (hedges : G.edgeFinset.card = 2 * Fintype.card V - 2) :
    HasWheelWitness G :=
  erdos_916 G hcard hedges

end Erdos916
