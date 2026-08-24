/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open SimpleGraph Filter

namespace Erdos1092

open scoped Classical in
/--
Let `f r m` be maximal such that if every `m`-vertex subgraph of any finite
graph can be made `r`-colourable by deleting at most `f r m` edges, then the
ambient graph is `(r + 1)`-colourable.
-/
noncomputable def f (r m : ℕ) : ℕ :=
  sSup {k : ℕ |
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
      (∀ H : Subgraph G, Fintype.card H.verts = m →
        ∃ E : Finset (Sym2 H.verts),
          E ⊆ H.coe.edgeFinset ∧ E.card ≤ k ∧
          chromaticNumber (H.coe.deleteEdges E) ≤ (r : ℕ∞)) →
      chromaticNumber G ≤ (r + 1 : ℕ∞)}

theorem f_asymptotic_2 :
    ¬ (fun (n : ℕ) => (n : ℝ)) =o[atTop] (fun (n : ℕ) => (f 2 n : ℝ)) := by
  sorry

theorem not_erdos_1092 :
    ¬ ∀ r : ℕ,
      (fun n : ℕ => ((r : ℝ) * n)) =o[atTop]
        (fun n : ℕ => (f r n : ℝ)) := by
  sorry
