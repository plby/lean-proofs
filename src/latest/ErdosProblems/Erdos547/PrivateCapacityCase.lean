import ErdosProblems.Erdos547.TwoAnchorAssembly
import ErdosProblems.Erdos547.FullPieceFilling

/-!
# Filling any target within the full and private pieces
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace SaturationDecomposition

theorem pair_of_private_capacity {μ : FractionalMatching G} {w : EdgeWeights G} {c d : V}
    (D : SaturationDecomposition μ w d)
    (E : CrossAnchorSplit D.cross D.active (w.truncate D.full.load D.full.load_nonneg) c)
    (hcd : G.Adj c d) (γ δ : ℝ) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hsat : a + b ≤ w.saturation μ.load c)
    (hsize : a ≤ 2 * D.full.total + E.privatePart.total) :
    ∃ σ : SkewMatching G γ, ∃ τ : SkewMatching G δ,
      AnchoredPair σ τ w d c ∧ PairDominated σ τ μ ∧ σ.total = a ∧ τ.total = b := by
  by_cases hfull : a ≤ 2 * D.full.total
  · exact exists_pair_of_full_piece μ D.full D.full_le w hcd D.full_fits
      γ δ hγ hδ a b ha hb hsat hfull
  have hq0 : 0 ≤ a - 2 * D.full.total := by linarith
  have hqP : a - 2 * D.full.total ≤ E.privatePart.total := by linarith
  obtain ⟨Q, hQ, hQtotal⟩ := E.privatePart.exists_submatching_total _ hq0 hqP
  let wI := w.truncate D.full.load D.full.load_nonneg
  let r := wI.saturation E.shared.load c
  have hr : 0 ≤ r := wI.saturation_nonneg E.shared.load E.shared.load_nonneg c
  obtain ⟨τs, hτs, hfit, htotal⟩ := exists_skew_of_saturation_exact E.shared wI c δ hδ r hr le_rfl
  let σs := SkewMatching.zero G γ hγ
  have hσtotal : σs.total = 0 := by simp only [σs, SkewMatching.total, SkewMatching.zero,
    Finset.sum_const_zero]
  have hdom : PairDominated σs τs E.shared := (PairDominated.single_left τs γ hγ hτs).swap
  have hout (u : V) (_ : u ∉ D.active) : σs.outLoad u = 0 := by
    simp only [σs, SkewMatching.outLoad, SkewMatching.zero, Finset.sum_const_zero, zero_div]
  have hlower : wI.saturation E.shared.load c - σs.total ≤ τs.total := by
    rw [hσtotal, sub_zero, htotal]
  obtain ⟨σ, τ, hp, hd, ht, hlarge⟩ :=
    D.assemble_private_piece E hcd Q hQ σs τs hdom hout hfit hlower
  have hσ : σ.total = a := by rw [hσtotal, hQtotal] at ht; linarith
  have hτ : b ≤ τ.total := by linarith
  exact hp.trim hd a b ha hb hσ.ge hτ

end SaturationDecomposition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.SaturationDecomposition.pair_of_private_capacity
