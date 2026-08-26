import ErdosProblems.Erdos547.GreedyAllowances

/-!
# The three anchored greedy allocation lemmas

These statements use positive skew and the underlying graph neighbourhoods.
The conclusions have exact prescribed weight and preserve every constraint
of the original anchored pair.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ δ : ℝ}

theorem AnchoredPair.extend_of_residual_allocation
    {σ : SkewMatching G γ} {τ : SkewMatching G δ} {w : EdgeWeights G} {c d : V}
    (h : AnchoredPair σ τ w c d) (A B : Finset V) (κ : ℝ)
    (hex : ∃ ρ : SkewMatching G γ,
      (∀ u, ρ.outLoad u ≤ tailAllowance w c (fun u ↦ σ.load u + τ.load u) A u) ∧
      (∀ u, ρ.load u ≤ 1 - (σ.load u + τ.load u)) ∧
      (∀ u v, ¬ (u ∈ A ∧ v ∈ B) → ρ.weight u v = 0) ∧ ρ.total = (1 + γ) * κ) :
    ∃ ρ : SkewMatching G γ, ∃ hs : ∀ u, σ.load u + ρ.load u ≤ 1,
      AnchoredPair (σ.add ρ hs) τ w c d ∧ ρ.total = (1 + γ) * κ ∧
      ∀ u v, ¬ (u ∈ A ∧ v ∈ B) → ρ.weight u v = 0 := by
  obtain ⟨ρ, hout, hload, hsupp, htotal⟩ := hex
  have hc (u : V) : σ.load u + τ.load u + ρ.load u ≤ 1 := by linarith [hload u]
  have ha (u : V) : ρ.outLoad u ≤ max 0 (w.weight c u - (σ.load u + τ.load u)) :=
    (hout u).trans (tailAllowance_le w c _ A u)
  obtain ⟨hs, hpair⟩ := h.add_with_allowance hc ha
  exact ⟨ρ, hs, hpair, htotal, hsupp⟩

open scoped Classical in
theorem AnchoredPair.first_greedy {σ : SkewMatching G γ} {τ : SkewMatching G δ}
    {w : EdgeWeights G} {c d : V} (h : AnchoredPair σ τ w c d)
    (A B : Finset V) (hdis : Disjoint A B) (κ : ℝ) (hκ : 0 ≤ κ) (hγ : 0 < γ)
    (hA : κ + (∑ u ∈ A, (σ.load u + τ.load u)) ≤ w.degreeOn A c)
    (hB : ∀ x ∈ A, γ * κ + (∑ u ∈ B, (σ.load u + τ.load u)) ≤
      ((B.filter (G.Adj x)).card : ℝ)) :
    ∃ ρ : SkewMatching G γ, ∃ hs : ∀ u, σ.load u + ρ.load u ≤ 1,
      AnchoredPair (σ.add ρ hs) τ w c d ∧ ρ.total = (1 + γ) * κ ∧
      ∀ u v, ¬ (u ∈ A ∧ v ∈ B) → ρ.weight u v = 0 := by
  classical
  let l := fun u ↦ σ.load u + τ.load u
  have hl (u : V) : 0 ≤ l u := add_nonneg (σ.load_nonneg u) (τ.load_nonneg u)
  have hN (x : V) (hx : x ∈ A) : γ * κ ≤ ∑ y ∈ B.filter (G.Adj x), (1 - l y) :=
    residual_capacity_sum_ge l hl (B.filter (G.Adj x)) B (Finset.filter_subset _ _)
      (γ * κ) (hB x hx)
  apply h.extend_of_residual_allocation A B κ
  exact exists_greedy_disjoint A B hdis (tailAllowance w c l A) (fun u ↦ 1 - l u)
    (tailAllowance_nonneg w c l A) (tailAllowance_le_capacity w c l h.capacity A)
    (fun u ↦ by linarith [hl u]) (fun u hu ↦ if_neg hu) κ hκ
    (tailAllowance_sum_ge w c l A κ hA) γ hγ hN

open scoped Classical in
theorem AnchoredPair.second_greedy {σ : SkewMatching G γ} {τ : SkewMatching G δ}
    {w : EdgeWeights G} {c d : V} (h : AnchoredPair σ τ w c d)
    (A B : Finset V) (κ : ℝ) (hκ : 0 ≤ κ) (hγ : 0 < γ)
    (hA : κ + (∑ u ∈ A, (σ.load u + τ.load u)) ≤ w.degreeOn A c)
    (hB : ∀ x ∈ A, (1 + γ) * κ + (∑ u ∈ B, (σ.load u + τ.load u)) ≤
      ((B.filter (G.Adj x)).card : ℝ)) :
    ∃ ρ : SkewMatching G γ, ∃ hs : ∀ u, σ.load u + ρ.load u ≤ 1,
      AnchoredPair (σ.add ρ hs) τ w c d ∧ ρ.total = (1 + γ) * κ ∧
      ∀ u v, ¬ (u ∈ A ∧ v ∈ B) → ρ.weight u v = 0 := by
  classical
  let l := fun u ↦ σ.load u + τ.load u
  have hl (u : V) : 0 ≤ l u := add_nonneg (σ.load_nonneg u) (τ.load_nonneg u)
  have hN (x : V) (hx : x ∈ A) : (1 + γ) * κ ≤ ∑ y ∈ B.filter (G.Adj x), (1 - l y) :=
    residual_capacity_sum_ge l hl (B.filter (G.Adj x)) B (Finset.filter_subset _ _)
      ((1 + γ) * κ) (hB x hx)
  apply h.extend_of_residual_allocation A B κ
  exact exists_greedy_overlapping A B (tailAllowance w c l A) (fun u ↦ 1 - l u)
    (tailAllowance_nonneg w c l A) (tailAllowance_le_capacity w c l h.capacity A)
    (fun u ↦ by linarith [hl u]) (fun u hu ↦ if_neg hu) κ hκ
    (tailAllowance_sum_ge w c l A κ hA) γ hγ hN

open scoped Classical in
theorem AnchoredPair.third_greedy {σ : SkewMatching G γ} {τ : SkewMatching G δ}
    {w : EdgeWeights G} {c d : V} (h : AnchoredPair σ τ w c d)
    (A B : Finset V) (hdis : Disjoint A B) (κ : ℝ) (hκ : 0 ≤ κ) (hγ : 0 < γ)
    (hB : γ * κ + (∑ u ∈ B, (σ.load u + τ.load u)) ≤ (B.card : ℝ))
    (hA : ∀ y ∈ B, κ + (∑ u ∈ A, (σ.load u + τ.load u)) ≤
      w.degreeOn (A.filter (G.Adj y)) c) :
    ∃ ρ : SkewMatching G γ, ∃ hs : ∀ u, σ.load u + ρ.load u ≤ 1,
      AnchoredPair (σ.add ρ hs) τ w c d ∧ ρ.total = (1 + γ) * κ ∧
      ∀ u v, ¬ (u ∈ A ∧ v ∈ B) → ρ.weight u v = 0 := by
  classical
  let l := fun u ↦ σ.load u + τ.load u
  have hl (u : V) : 0 ≤ l u := add_nonneg (σ.load_nonneg u) (τ.load_nonneg u)
  have hB' : γ * κ ≤ ∑ u ∈ B, (1 - l u) :=
    residual_capacity_sum_ge l hl B B (fun _ h ↦ h) (γ * κ) hB
  have hN (y : V) (hy : y ∈ B) : κ ≤
      ∑ u ∈ A.filter (G.Adj y), tailAllowance w c l A u := by
    have hh := degreeOn_sub_load_le_allowance_sum w c l A (A.filter (G.Adj y))
      (Finset.filter_subset _ _)
    have hs : (∑ u ∈ A.filter (G.Adj y), l u) ≤ ∑ u ∈ A, l u :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun u _ _ ↦ hl u)
    have hdegree := hA y hy
    change κ + (∑ u ∈ A, l u) ≤ _ at hdegree
    linarith
  apply h.extend_of_residual_allocation A B κ
  exact exists_greedy_reverse A B hdis (tailAllowance w c l A) (fun u ↦ 1 - l u)
    (tailAllowance_nonneg w c l A) (tailAllowance_le_capacity w c l h.capacity A)
    (fun u ↦ by linarith [hl u]) (fun u hu ↦ if_neg hu) κ hκ γ hγ hB' hN

end Erdos547.DPRS

#print axioms Erdos547.DPRS.AnchoredPair.first_greedy
#print axioms Erdos547.DPRS.AnchoredPair.second_greedy
#print axioms Erdos547.DPRS.AnchoredPair.third_greedy
