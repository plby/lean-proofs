import Arxiv.Arxiv2411_18291.LogNibblePackingCriterion
import Arxiv.Arxiv2411_18291.LogNibbleInitialBounds

/-! # Logarithmic packing with the paper's original initial regularity hypothesis -/

open Finset

noncomputable section

namespace Arxiv2411_18291.CliqueRemovalProcess

theorem exists_regular_log_nibble_packing {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}
    (hqr : r + 1 < q) (G : Hypergraph V (r + 1)) (H : Finset (Block V q))
    (hHG : ∀ Q ∈ H, cliqueEdges (r + 1) Q ⊆ G) {a D p₀ : ℝ}
    (P : LogNibbleParameters (q.choose (r + 1)) a G.card D p₀
      ((Fintype.card V : ℝ) ^ (q - (r + 1) - 1)))
    (hd : ∀ e ∈ G, |((H.filter fun Q => e.val ⊆ Q.val).card : ℝ) - D| ≤ a ^ 3 * D)
    (N : ℕ) (hfloor : p₀ ≤ removalDensity (q.choose (r + 1)) G.card N)
    (hgap : ∀ t, nibbleStepBound q G D t < nibbleCriticalWidth G a D t)
    (hsmall : nibbleFailureBound q G a D N < 1) {θ : ℝ}
    (hθ : removalDensity (q.choose (r + 1)) G.card N + 2 * a ≤ θ) :
    ∃ C : Finset (Block V q), C ⊆ H ∧ C.card = N ∧
      IsDecomposition (cliqueSupport (r + 1) C) C ∧
        IsGraphBounded (G \ cliqueSupport (r + 1) C) θ := by
  have ha1 : a ≤ 1 := P.error_le_one
  have hglobal := initial_degree_upper_bound G H hHG P.degree_pos.le
    (pow_le_one₀ P.error_pos.le ha1 : a ^ 3 ≤ 1) hd
  exact exists_packing_of_log_nibble_bounds hqr G H hHG P hglobal N hfloor hgap
    (log_nibble_initial_below_critical hqr G H hHG P hd) hsmall hθ

end Arxiv2411_18291.CliqueRemovalProcess
