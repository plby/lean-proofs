import ErdosProblems.Erdos547.ReachableBudget
import ErdosProblems.Erdos547.GreedyAnchored
import ErdosProblems.Erdos547.StructuralCover

/-!
# Greedy completion from a half-full reachable set
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {γ δ : ℝ}

namespace GallaiEdmondsPartition

theorem IsMaxSaturation.finish_from_reachable_load {D : GallaiEdmondsPartition G}
    {w : EdgeWeights G} {c d : V} {μ : FractionalMatching G}
    (h : D.IsMaxSaturation w c μ) {σ : SkewMatching G γ} {τ : SkewMatching G δ}
    (hp : AnchoredPair σ τ w c d) (hdom : PairDominated σ τ μ) (hγ : 0 < γ)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hτ : τ.total = b)
    (hlarge : a + b ≤ w.degree c) (hdeg : ∀ v, (a + b) / 2 ≤ w.degree v)
    (hsat : w.saturation μ.load c ≤ σ.total + τ.total)
    (hR : (a + b) / 2 ≤ ∑ u ∈ D.reachableVertices w c μ, (σ.load u + τ.load u)) :
    HasAnchoredTotals w γ δ a b := by
  classical
  by_cases hσ : a ≤ σ.total
  · obtain ⟨σ', τ', hp', _, hσ', hτ'⟩ := hp.trim hdom a b ha hb hσ hτ.ge
    exact ⟨c, d, σ', τ', hp', hσ', hτ'⟩
  let R := D.reachableVertices w c μ
  let κ := (a - σ.total) / (1 + γ)
  have hden : 0 < 1 + γ := by linarith
  have hκ : 0 ≤ κ := div_nonneg (by linarith) hden.le
  have hmul : (1 + γ) * κ = a - σ.total := mul_div_cancel₀ _ (ne_of_gt hden)
  have hκbound : κ ≤ a - σ.total := by nlinarith [mul_nonneg hγ.le hκ]
  have hγκ : γ * κ ≤ a - σ.total := by nlinarith
  have hsum : (∑ u ∈ R, (σ.load u + τ.load u)) +
      (∑ u ∈ Rᶜ, (σ.load u + τ.load u)) = σ.total + τ.total := by
    rw [Finset.sum_add_sum_compl, Finset.sum_add_distrib, σ.sum_load, τ.sum_load]
  have hload : (∑ u ∈ R, (σ.load u + τ.load u)) ≤ ∑ u ∈ R, μ.load u :=
    Finset.sum_le_sum fun u _ ↦ hdom.load_le u
  have htail : κ + (∑ u ∈ R, (σ.load u + τ.load u)) ≤ w.degreeOn R c := by
    have he := h.reachable_degree_identity
    change w.degreeOn R c + _ = _ at he
    linarith
  have hhead (x : V) (hx : x ∈ R) :
      γ * κ + (∑ u ∈ Rᶜ, (σ.load u + τ.load u)) ≤ ((Rᶜ.filter (G.Adj x)).card : ℝ) := by
    have hc : w.degree x ≤ ((Rᶜ.filter (G.Adj x)).card : ℝ) :=
      w.degree_le_card_of_neighbours_subset x _ (fun y hxy ↦
        Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr (h.neighbour_not_reachable hx hxy), hxy⟩)
    change (a + b) / 2 ≤ ∑ u ∈ R, (σ.load u + τ.load u) at hR
    linarith [hdeg x]
  obtain ⟨ρ, hs, hpair, htotal, _⟩ := hp.first_greedy R Rᶜ disjoint_compl_right
    κ hκ hγ htail hhead
  refine ⟨c, d, σ.add ρ hs, τ, hpair, ?_, hτ⟩
  rw [SkewMatching.add_total, htotal, hmul]
  ring

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.IsMaxSaturation.finish_from_reachable_load
