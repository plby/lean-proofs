import Arxiv.Arxiv2411_18291.LogNibbleHalfWidths
import Arxiv.Arxiv2411_18291.RegularLogNibbleCriterion
import Arxiv.Arxiv2411_18291.NibbleHorizon

/-! # Window gaps and the rounded endpoint for logarithmic packing -/

namespace Arxiv2411_18291

structure LogNibbleEndConditions (k : ℕ) (a g n : ℝ) (d : ℕ) : Prop where
  count_many_edges : 264 * (k : ℝ) ^ 3 ≤ a ^ 3 * g
  face_many_vertices : 4 * (d : ℝ) ≤ a * n

namespace CliqueRemovalProcess

variable {V : Type*} [Fintype V] {q r : ℕ}

theorem log_nibble_all_half_widths (G : Hypergraph V (r + 1)) {a D p₀ : ℝ}
    (P : LogNibbleParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (R : LogNibbleEndConditions (q.choose (r + 1)) a G.card (Fintype.card V) (q - r))
    (t : NibbleTrack V r) : nibbleStepBound q G D t ≤ nibbleCriticalWidth G a D t / 2 := by
  rcases t with b | (⟨e, b⟩ | f)
  · exact P.count_step_half_width R.count_many_edges
  · exact P.edge_step_half_width
  · exact P.face_step_half_width (Nat.cast_nonneg _) R.face_many_vertices

theorem log_nibble_all_width_gaps (hqr : r + 1 < q) (G : Hypergraph V (r + 1)) {a D p₀ : ℝ}
    (P : LogNibbleParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (R : LogNibbleEndConditions (q.choose (r + 1)) a G.card (Fintype.card V) (q - r))
    (t : NibbleTrack V r) : nibbleStepBound q G D t < nibbleCriticalWidth G a D t := by
  have hhalf := log_nibble_all_half_widths G P R t
  have hpos := nibbleStepBound_pos hqr G P.graph_pos P.degree_pos t
  linarith only [hhalf, hpos]

theorem exists_packing_at_log_nibble_horizon [DecidableEq V] (hqr : r + 1 < q)
    (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) {a D p₀ : ℝ}
    (P : LogNibbleParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (R : LogNibbleEndConditions (q.choose (r + 1)) a G.card (Fintype.card V) (q - r))
    (hd : ∀ e ∈ G, |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - D| ≤ a ^ 3 * D)
    (hsmall : nibbleFailureBound q G a D (nibbleHorizon (q.choose (r + 1)) G.card p₀) < 1) :
    ∃ C : Finset (Block V q), C ⊆ H ∧ C.card = nibbleHorizon (q.choose (r + 1)) G.card p₀ ∧
      IsDecomposition (cliqueSupport (r + 1) C) C ∧
        IsGraphBounded (G \ cliqueSupport (r + 1) C) (p₀ + 3 * a) := by
  have hk : 0 < q.choose (r + 1) := by have h := P.rank; omega
  apply exists_regular_log_nibble_packing hqr G H hHG P hd _
    (nibbleHorizon_density_ge hk P.graph_pos P.floor_le_one)
    (log_nibble_all_width_gaps hqr G P R) hsmall
  have h := nibbleHorizon_density_lt hk (p₀ := p₀) P.graph_pos
  have hs := P.density_step_le_error_quarter
  have ha := P.error_pos
  linarith only [h, hs, ha]

end CliqueRemovalProcess

end Arxiv2411_18291
