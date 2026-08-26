import ErdosProblems.Erdos547.GreedyAnchored
import ErdosProblems.Erdos547.StructuralCover

/-!
# Completing an anchored allocation using a free-region supply estimate
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ δ : ℝ}

theorem AnchoredPair.finish_from_free_supply {β : SkewMatching G γ} {α : SkewMatching G δ}
    {w : EdgeWeights G} {c d : V} (hp : AnchoredPair β α w c d)
    (H U : Finset V) (A B : ℝ) (htα : α.total = A) (hB : β.total ≤ B) (hγ : 0 < γ)
    (hanchor : (B - β.total) / (1 + γ) + A + (∑ u ∈ H, β.load u) ≤ w.degreeOn H c)
    (hsupply : ∀ z ∈ H, A + B - β.total ≤ w.degreeOn U z - ∑ u ∈ U, β.load u) :
    HasAnchoredTotals w γ δ B A := by
  classical
  let κ := (B - β.total) / (1 + γ)
  have hκ : 0 ≤ κ := div_nonneg (sub_nonneg.mpr hB) β.denominator_pos.le
  have hκeq : (1 + γ) * κ = B - β.total :=
    mul_div_cancel₀ _ β.denominator_pos.ne'
  have hsum (S : Finset V) : (∑ u ∈ S, α.load u) ≤ A := by
    rw [← htα, ← α.sum_load]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun u _ _ ↦ α.load_nonneg u)
  have hhead : κ + (∑ u ∈ H, (β.load u + α.load u)) ≤ w.degreeOn H c := by
    rw [Finset.sum_add_distrib]
    linarith [hsum H]
  have htail (z : V) (hz : z ∈ H) :
      (1 + γ) * κ + (∑ u ∈ U, (β.load u + α.load u)) ≤
        ((U.filter (G.Adj z)).card : ℝ) := by
    rw [hκeq, Finset.sum_add_distrib]
    have hh := hsupply z hz
    have hu := w.degreeOn_le_card_neighbours z U
    linarith [hsum U]
  obtain ⟨ρ, hc, hpair, ht, _⟩ := hp.second_greedy H U κ hκ hγ hhead htail
  refine ⟨c, d, β.add ρ hc, α, hpair, ?_, htα⟩
  rw [SkewMatching.add_total, ht, hκeq]
  ring

end Erdos547.DPRS

#print axioms Erdos547.DPRS.AnchoredPair.finish_from_free_supply
