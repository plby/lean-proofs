/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/- A graph-level arithmetic interface to dependent random choice. -/

import ErdosProblems.Erdos717.SparseHighDensity

open Function Set
open SimpleGraph

namespace Erdos717

/-- It is enough to check the DRC second-moment inequality at the full
ambient cardinality and at half the source edge count. -/
theorem exists_short_path_reservoir_of_edge_square
    {V : Type*} [Fintype V] [DecidableEq V]
    (H G : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel G.Adj]
    (hHG : H ≤ G) (X0 L : ℕ)
    (hE : 0 < H.edgeFinset.card)
    (hX0 : 20 ≤ X0) (hLX : 5 * L ≤ X0)
    (hlarge : 4 * Fintype.card V *
      (Fintype.card V * (X0 * X0) +
        40 * (Fintype.card V * Fintype.card V * L)) ≤
      H.edgeFinset.card * H.edgeFinset.card) :
    ∃ U : Finset V,
      X0 / 5 ≤ U.card ∧ (U : Set V) ⊆ H.support ∧
      ∀ {r : ℕ} (branch : Fin r ↪ V),
        Set.range branch ⊆ (U : Set V) →
        6 * (Finset.univ.filter fun q : Erdos718.CliqueEdge r =>
          ¬G.Adj (branch q.1.1) (branch q.1.2)).card + 2 ≤ L →
        Erdos718.ContainsCliqueSubdivision G r := by
  apply exists_short_path_reservoir H G hHG X0 L hE hX0 hLX
  intro s t e hs ht hHe
  have hmono : t * (t * (X0 * X0) + 40 * (s * s * L)) ≤
      Fintype.card V *
        (Fintype.card V * (X0 * X0) +
          40 * (Fintype.card V * Fintype.card V * L)) := by
    apply Nat.mul_le_mul ht
    apply Nat.add_le_add
    · exact Nat.mul_le_mul_right (X0 * X0) ht
    · apply Nat.mul_le_mul_left 40
      exact Nat.mul_le_mul (Nat.mul_le_mul hs hs) le_rfl
  have hfour : 4 *
      (t * (t * (X0 * X0) + 40 * (s * s * L))) ≤
      H.edgeFinset.card * H.edgeFinset.card := by
    calc
      4 * (t * (t * (X0 * X0) + 40 * (s * s * L))) ≤
          4 * (Fintype.card V *
            (Fintype.card V * (X0 * X0) +
              40 * (Fintype.card V * Fintype.card V * L))) :=
        Nat.mul_le_mul_left 4 hmono
      _ = 4 * Fintype.card V *
          (Fintype.card V * (X0 * X0) +
            40 * (Fintype.card V * Fintype.card V * L)) := by ring
      _ ≤ H.edgeFinset.card * H.edgeFinset.card := hlarge
  have hedge : H.edgeFinset.card * H.edgeFinset.card ≤ 4 * (e * e) := by
    nlinarith
  omega

end Erdos717
