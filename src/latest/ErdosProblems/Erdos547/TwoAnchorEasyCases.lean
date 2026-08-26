import ErdosProblems.Erdos547.CrossAnchorSplit
import ErdosProblems.Erdos547.FullPieceFilling

/-!
# The large-private-piece case of the two-anchor matching lemma
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

namespace SaturationDecomposition

theorem pair_of_large_remainder {μ : FractionalMatching G} {w : EdgeWeights G} {c d : V}
    (D : SaturationDecomposition μ w d)
    (E : CrossAnchorSplit D.cross D.active (w.truncate D.full.load D.full.load_nonneg) c)
    (hcd : G.Adj c d) (hdeg : 2 * w.saturation μ.load d ≤ w.saturation μ.load c)
    (γ δ : ℝ) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hA : a ≤ w.saturation μ.load d) (hB : b ≤ 2 * D.full.total + E.privatePart.total) :
    ∃ σ : SkewMatching G γ, ∃ τ : SkewMatching G δ,
      AnchoredPair σ τ w d c ∧ PairDominated σ τ μ ∧ σ.total = a ∧ τ.total = b := by
  have hpieces (u v : V) : D.used.weight u v + D.remainder.weight u v ≤ μ.weight u v := by
    change D.used.weight u v + (μ.weight u v - D.used.weight u v) ≤ _
    linarith
  have hleft : a ≤ w.saturation D.used.load d := by rwa [D.used_saturation]
  have hright : b ≤ (w.truncate D.used.load D.used.load_nonneg).saturation D.remainder.load c :=
    hB.trans (D.remainder_saturation_lower c E hdeg)
  exact exists_filling_disjoint D.used D.remainder μ hpieces w hcd.symm γ δ hγ hδ a b ha hb
    hleft hright

end SaturationDecomposition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.SaturationDecomposition.pair_of_large_remainder
