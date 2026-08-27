import Arxiv.Arxiv2411_18291.NibbleHorizon
import Arxiv.Arxiv2411_18291.NibbleHalfWidths
import Arxiv.Arxiv2411_18291.RegularNibbleCriterion

/-! # Sufficient scalar conditions at the end of the nibble -/

namespace Arxiv2411_18291

structure NibbleEndConditions (k : ℕ) (a g n p₀ : ℝ) (d : ℕ) : Prop where
  count_many_edges : 264 * (k : ℝ) ^ 3 ≤ a ^ 3 * g
  face_many_vertices : 4 * (d : ℝ) ≤ a * n
  face_error : 128 * (k : ℝ) * a ≤ p₀

namespace CliqueRemovalProcess

variable {V : Type*} [Fintype V] {q r : ℕ}

theorem nibble_all_half_widths (G : Hypergraph V (r + 1)) {a D p₀ : ℝ}
    (P : NibbleComparisonParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (R : NibbleEndConditions (q.choose (r + 1)) a G.card (Fintype.card V) p₀ (q - r))
    (t : NibbleTrack V r) : nibbleStepBound q G D t ≤ nibbleCriticalWidth G a D t / 2 := by
  rcases t with b | (⟨e, b⟩ | f)
  · exact P.count_step_half_width R.count_many_edges
  · exact P.edge_step_half_width
  · exact P.face_step_half_width (Nat.cast_nonneg _) R.face_many_vertices

theorem nibble_all_width_gaps (hqr : r + 1 < q) (G : Hypergraph V (r + 1)) {a D p₀ : ℝ}
    (P : NibbleComparisonParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (R : NibbleEndConditions (q.choose (r + 1)) a G.card (Fintype.card V) p₀ (q - r))
    (t : NibbleTrack V r) : nibbleStepBound q G D t < nibbleCriticalWidth G a D t := by
  have hhalf := nibble_all_half_widths G P R t
  have hpos := nibbleStepBound_pos hqr G P.graph_pos P.degree_pos t
  linarith only [hhalf, hpos]

theorem exists_packing_at_nibble_horizon [DecidableEq V] (hqr : r + 1 < q)
    (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) {a D p₀ : ℝ}
    (P : NibbleComparisonParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (Q : NibbleCountConditions (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (R : NibbleEndConditions (q.choose (r + 1)) a G.card (Fintype.card V) p₀ (q - r))
    (hd : ∀ e ∈ G, |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - D| ≤ a ^ 3 * D)
    (hsmall : nibbleFailureBound q G a D (nibbleHorizon (q.choose (r + 1)) G.card p₀) < 1) :
    ∃ C : Finset (Block V q), C ⊆ H ∧ C.card = nibbleHorizon (q.choose (r + 1)) G.card p₀ ∧
      IsDecomposition (cliqueSupport (r + 1) C) C ∧
        IsGraphBounded (G \ cliqueSupport (r + 1) C) (3 * p₀) := by
  have hk : 0 < q.choose (r + 1) := by have h := P.rank; omega
  exact exists_regular_nibble_packing hqr G H hHG P Q hd _
    (nibbleHorizon_density_ge hk P.graph_pos P.floor_le_one)
    (nibble_all_width_gaps hqr G P R) hsmall
    (P.horizon_face_density_lt R.face_error).le

end CliqueRemovalProcess

end Arxiv2411_18291
