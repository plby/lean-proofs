import ErdosProblems.Erdos547.GESaturationDegree
import ErdosProblems.Erdos547.TwoAnchorMatching

/-!
# The fractional-cover cases of the degree structure theorem

The maximum-saturation lower bound avoids constructing a separate fractional
extension when the high-degree vertex lies outside the GE separator.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

/-- Actual allocations and adjacent anchors with the specified total loads. -/
def HasAnchoredTotals (w : EdgeWeights G) (γ δ a b : ℝ) : Prop :=
  ∃ c d : V, ∃ σ : SkewMatching G γ, ∃ τ : SkewMatching G δ,
    AnchoredPair σ τ w c d ∧ σ.total = a ∧ τ.total = b

theorem HasAnchoredTotals.swap {w : EdgeWeights G} {γ δ a b : ℝ}
    (h : HasAnchoredTotals w γ δ a b) : HasAnchoredTotals w δ γ b a := by
  obtain ⟨c, d, σ, τ, hp, hσ, hτ⟩ := h
  exact ⟨d, c, τ, σ, hp.swap, hτ, hσ⟩

theorem hasAnchoredTotals_of_saturations (μ : FractionalMatching G) (w : EdgeWeights G)
    {c d : V} (hcd : G.Adj c d) (γ δ a b : ℝ) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ)
    (ha : 0 < a) (hb : 0 < b)
    (hc : a + b ≤ w.saturation μ.load c) (hd : (a + b) / 2 ≤ w.saturation μ.load d) :
    HasAnchoredTotals w γ δ a b := by
  obtain ⟨σ, τ, hp, _, hσ, hτ⟩ := exists_two_anchor_matching μ w hcd γ δ a b hγ hδ ha hb hc hd
  rcases hp with hp | hp
  · exact ⟨c, d, σ, τ, hp, hσ, hτ⟩
  · exact ⟨d, c, σ, τ, hp, hσ, hτ⟩

variable [DecidableEq V]

namespace GallaiEdmondsPartition

theorem anchoredTotals_of_separator_saturation (D : GallaiEdmondsPartition G)
    (w : EdgeWeights G) (μ : FractionalMatching G) (hμ : D.IsFractionalGE μ)
    {c : V} (hc : c ∈ D.separator) (γ δ a b : ℝ) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ)
    (ha : 0 < a) (hb : 0 < b) (hdeg : ∀ v, (a + b) / 2 ≤ w.degree v)
    (hsat : a + b ≤ w.saturation μ.load c) : HasAnchoredTotals w γ δ a b := by
  obtain ⟨d, hcd, _⟩ := D.isMatching (D.covers hc)
  have hd : d ∉ D.separator := by
    rcases D.crosses c d hcd with h | h
    · exact h.2
    · exact (h.2 hc).elim
  apply hasAnchoredTotals_of_saturations μ w (D.matching.adj_sub hcd)
    γ δ a b hγ hδ ha hb hsat
  rw [hμ.saturation_of_not_separator w hd]
  exact hdeg d

theorem anchoredTotals_of_outside_separator (D : GallaiEdmondsPartition G)
    (w : EdgeWeights G) {c : V} (hc : c ∉ D.separator)
    (γ δ a b : ℝ) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (ha : 0 < a) (hb : 0 < b)
    (hdeg : ∀ v, (a + b) / 2 ≤ w.degree v) (hlarge : a + b ≤ w.degree c) :
    HasAnchoredTotals w γ δ a b := by
  obtain ⟨d, hcd⟩ := w.exists_neighbour_of_degree_pos c (by linarith)
  obtain ⟨μ, hμ, hmax⟩ := D.exists_max_saturation w d
  have hm : D.IsMaxSaturation w d μ := ⟨hμ, hmax⟩
  apply hasAnchoredTotals_of_saturations μ w hcd γ δ a b hγ hδ ha hb
  · rwa [hμ.saturation_of_not_separator w hc]
  · exact hm.saturation_ge_min_degree ((a + b) / 2) hdeg

/-- If the cover cases fail, every chosen high-degree anchor lies in the
separator and has a deficient singleton for its maximum GE saturation. -/
theorem initial_obstruction (D : GallaiEdmondsPartition G) (w : EdgeWeights G)
    {c : V} (γ δ a b : ℝ) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (ha : 0 < a) (hb : 0 < b)
    (hdeg : ∀ v, (a + b) / 2 ≤ w.degree v) (hlarge : a + b ≤ w.degree c)
    (hnot : ¬ HasAnchoredTotals w γ δ a b) :
    c ∈ D.separator ∧ ∃ μ : FractionalMatching G,
      D.IsMaxSaturation w c μ ∧ w.saturation μ.load c < a + b ∧
      ∃ d ∈ D.reachableVertices w c μ, G.Adj c d ∧ μ.load d < w.weight c d := by
  classical
  have hc : c ∈ D.separator := by
    by_contra hn
    exact hnot (D.anchoredTotals_of_outside_separator w hn γ δ a b hγ hδ ha hb hdeg hlarge)
  obtain ⟨μ, hμ, hmax⟩ := D.exists_max_saturation w c
  have hsat : w.saturation μ.load c < a + b := by
    by_contra hn
    exact hnot (D.anchoredTotals_of_separator_saturation w μ hμ hc γ δ a b
      hγ hδ ha hb hdeg (le_of_not_gt hn))
  obtain ⟨d, hdef⟩ := w.exists_deficient_of_saturation_lt_degree μ.load c (hsat.trans_le hlarge)
  have hcd : G.Adj c d := by
    by_contra hn
    rw [w.supported c d hn] at hdef
    exact (not_lt_of_ge (μ.load_nonneg d) hdef)
  exact ⟨hc, μ, ⟨hμ, hmax⟩, hsat, d,
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, d, hμ.deficient_singleton hdef,
      hdef, Relation.ReflTransGen.refl⟩, hcd, hdef⟩

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.anchoredTotals_of_outside_separator
#print axioms Erdos547.DPRS.GallaiEdmondsPartition.initial_obstruction
