import ErdosProblems.Erdos547.IndependentSkewLoad
import ErdosProblems.Erdos547.AdditiveSaturation
import ErdosProblems.Erdos547.GreedyAnchored
import ErdosProblems.Erdos547.StructuralCover

/-!
# Greedy completion using an independent separator and a saturation profile
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ δ : ℝ}

theorem finish_anchored_totals_from_cut {σ : SkewMatching G γ} {τ : SkewMatching G δ}
    {w : EdgeWeights G} {c d : V} (hp : AnchoredPair σ τ w c d)
    (R S : Finset V) (hdis : Disjoint R S) (l : V → ℝ)
    (hload : ∀ u, σ.load u + τ.load u ≤ l u)
    (hR : ∀ u ∈ R, l u ≤ w.weight c u) (hC : ∀ u ∉ R, w.weight c u ≤ l u)
    (hsat : w.saturation l c ≤ σ.total + τ.total)
    (hzero : ∀ u ∈ S, ∀ v ∈ S, σ.weight u v = 0) (htail : τ.RunsFrom S)
    (hN : ∀ x ∈ R, ∀ y, G.Adj x y → y ∈ S)
    (a b : ℝ) (ha : 0 ≤ a) (hτ : τ.total = b) (hγ : 0 < γ)
    (hlarge : a + b ≤ w.degree c)
    (hdeg : ∀ x ∈ R, max (a / (1 + γ)) (γ * (a / (1 + γ))) +
      b / (1 + δ) ≤ w.degree x) : HasAnchoredTotals w γ δ a b := by
  classical
  by_cases hσ : a ≤ σ.total
  · obtain ⟨σ', hs, ht⟩ := σ.exists_suballocation_total a ha hσ
    exact ⟨c, d, σ', τ, hp.of_suballocations hs (fun _ _ ↦ ⟨le_rfl, le_rfl⟩), ht, hτ⟩
  let κ := (a - σ.total) / (1 + γ)
  have hden : 0 < 1 + γ := by linarith
  have hκ : 0 ≤ κ := div_nonneg (by linarith) hden.le
  have hmul : (1 + γ) * κ = a - σ.total := mul_div_cancel₀ _ (ne_of_gt hden)
  have hκbound : κ ≤ a - σ.total := by nlinarith [mul_nonneg hγ.le hκ]
  have htailBudget : κ + (∑ u ∈ R, (σ.load u + τ.load u)) ≤ w.degreeOn R c := by
    have he := w.degreeOn_add_saturation l c R hR hC
    have hsum := Finset.sum_le_sum (s := R) (fun u _ ↦ hload u)
    linarith
  have hnumeric : γ * κ + max 1 γ * σ.total / (1 + γ) ≤
      max (a / (1 + γ)) (γ * (a / (1 + γ))) := by
    have he := max_mul_of_nonneg (1 : ℝ) γ (div_nonneg ha hden.le)
    rw [one_mul] at he
    rw [← he]
    change γ * ((a - σ.total) / (1 + γ)) + max 1 γ * σ.total / (1 + γ) ≤ _
    simp only [← mul_div_assoc, ← add_div]
    apply div_le_div_of_nonneg_right _ hden.le
    nlinarith [mul_nonneg (sub_nonneg.mpr (le_max_right (1 : ℝ) γ))
      (show 0 ≤ a - σ.total by linarith)]
  have hheadBudget (x : V) (hx : x ∈ R) :
      γ * κ + (∑ u ∈ S, (σ.load u + τ.load u)) ≤ ((S.filter (G.Adj x)).card : ℝ) := by
    have hc := w.degree_le_card_of_neighbours_subset x (S.filter (G.Adj x))
      (fun y hxy ↦ Finset.mem_filter.mpr ⟨hN x hx y hxy, hxy⟩)
    rw [Finset.sum_add_distrib, htail.sum_load_side, hτ]
    linarith [σ.sum_load_independent_le S hzero, hdeg x hx]
  obtain ⟨ρ, hs, hp', htρ, _⟩ := hp.first_greedy R S hdis κ hκ hγ htailBudget hheadBudget
  refine ⟨c, d, σ.add ρ hs, τ, hp', ?_, hτ⟩
  rw [SkewMatching.add_total, htρ, hmul]
  ring

end Erdos547.DPRS

#print axioms Erdos547.DPRS.finish_anchored_totals_from_cut
