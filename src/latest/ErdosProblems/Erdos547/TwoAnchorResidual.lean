import ErdosProblems.Erdos547.TwoAnchorAssembly
import ErdosProblems.Erdos547.ResidualBudgets

/-!
# Completing both residual budgets after allocating the private piece
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace SaturationDecomposition

theorem assemble_residual_totals {μ : FractionalMatching G} {w : EdgeWeights G} {c d : V}
    (D : SaturationDecomposition μ w d)
    (E : CrossAnchorSplit D.cross D.active (w.truncate D.full.load D.full.load_nonneg) c)
    (hcd : G.Adj c d) (γ δ r s : ℝ) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ)
    (hr : 0 < r) (hs : 0 < s) (hsum : r + s = 2 * E.shared.total)
    (hlo : max (r / (1 + γ)) (γ * (r / (1 + γ))) +
      min (s / (1 + δ)) (δ * (s / (1 + δ))) ≤ E.shared.total) :
    ∃ σ : SkewMatching G γ, ∃ τ : SkewMatching G δ,
      AnchoredPair σ τ w d c ∧ PairDominated σ τ μ ∧
      σ.total = 2 * D.full.total + E.privatePart.total + r ∧
      w.saturation μ.load c - σ.total ≤ τ.total := by
  obtain ⟨_, _, hsumA, _⟩ := positive_skew_parts r γ hr hγ
  obtain ⟨_, _, hsumB, _⟩ := positive_skew_parts s δ hs hδ
  have hhi : E.shared.total ≤ min (r / (1 + γ)) (γ * (r / (1 + γ))) +
      max (s / (1 + δ)) (δ * (s / (1 + δ))) := by
    linarith [min_add_max (r / (1 + γ)) (γ * (r / (1 + γ))),
      min_add_max (s / (1 + δ)) (δ * (s / (1 + δ)))]
  obtain ⟨σs, τs, hdoms, htotal, hlower, hout, hfit⟩ := exists_completion_of_totals
    E.shared D.active D.activeᶜ disjoint_compl_right E.shared_between
    (w.truncate D.full.load D.full.load_nonneg) c (fun _ hu ↦ E.shared_fits_inactive hu)
    γ δ r s hγ hδ hr hs hlo hhi
  obtain ⟨σ, τ, hp, hd, ht, hlarge⟩ := D.assemble_private_piece E hcd E.privatePart
    (fun _ _ ↦ le_rfl) σs τs hdoms hout hfit ((le_max_right _ _).trans hlower)
  refine ⟨σ, τ, hp, hd, ?_, hlarge⟩
  rw [ht, htotal]
  ring

end SaturationDecomposition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.SaturationDecomposition.assemble_residual_totals
