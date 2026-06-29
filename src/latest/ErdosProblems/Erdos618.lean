/- leanprover/lean4:v4.32.0  mathlib v4.32.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 618.
https://www.erdosproblems.com/forum/thread/618

Informal authors:
- Noga Alon

Formal authors:
- Aristotle
- Boris Alexeev

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos618.md
-/
import ErdosProblems.Erdos134

namespace Erdos618

open Erdos134

/-- The maximum degree of a graph on `Fin n` (as a natural number). -/
noncomputable def maxDegreeFin {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  classical
  exact Finset.univ.sup (fun v : Fin n =>
    @SimpleGraph.degree (Fin n) G v inferInstance)

open scoped Classical in
/-- For a graph `G` on `n` vertices, `h2 G` is the smallest number of edges that need
to be added to obtain a supergraph with diameter ≤ 2 that is still triangle-free
(expressed as `CliqueFree 3`). -/
noncomputable def h2 {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ := by
  exact sInf {k : ℕ |
    ∃ H : SimpleGraph (Fin n),
      G ≤ H ∧
      H.CliqueFree 3 ∧
      (∀ x y : Fin n, x ≠ y → H.Adj x y ∨ ∃ z, H.Adj x z ∧ H.Adj z y) ∧
      ((H.edgeFinset \ G.edgeFinset).card = k)}

/-
Positive answer (asymptotic form):

For a family of triangle-free graphs `G n` on `n` vertices, if the maximum degree is `o(n^(1/2))`
then `h₂(G n)` is `o(n^2)`, where `h₂` counts the minimum number of edges to add to make the
graph triangle-free and of diameter ≤ 2.
-/
theorem erdos_618
    (G : ∀ n : ℕ, SimpleGraph (Fin n))
    (hTriangleFree : ∀ n : ℕ, (G n).CliqueFree 3)
    (hMaxDeg :
      (fun n : ℕ => (maxDegreeFin (G n) : ℝ))
        =o[Filter.atTop] (fun n : ℕ => Real.rpow (n : ℝ) ((1 : ℝ) / 2))) :
    (fun n : ℕ => (h2 (G n) : ℝ))
      =o[Filter.atTop] (fun n : ℕ => (n : ℝ) ^ (2 : ℕ)) := by
        sorry
-- 'Erdos618.erdos_618' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos618
