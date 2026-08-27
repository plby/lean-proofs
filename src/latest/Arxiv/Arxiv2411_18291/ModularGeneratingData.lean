import Arxiv.Arxiv2411_18291.GoodCliqueEdges

/-!
# Constructing a good subgraph and its modular generators

Select the bounded generators, mark saturated cliques, and remove edges
with many saturated cliques. All resulting counts are explicit in the
input face bound, edge count, and chosen thresholds.
-/

open Finset

noncomputable section

namespace Arxiv2411_18291

variable {V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

structure ModularGeneratingData (K : Hypergraph V (r + 1)) (D : Finset (Block V q))
    (N : ℕ) where
  generators : Finset (Block V q)
  saturated : Finset (Block V q)
  good : Hypergraph V (r + 1)
  generators_subset : generators ⊆ D
  saturated_subset : saturated ⊆ D
  good_subset : good ⊆ K
  generates : ∀ Q ∈ D \ saturated,
    modularCliqueVector N (r + 1) Q ∈ generatedSubgroup (modularCliqueVector N (r + 1)) generators

theorem exists_modular_generating_data (N : ℕ) (hN : 0 < N)
    (K : Hypergraph V (r + 1)) (D : Finset (Block V q))
    (hD : ∀ Q ∈ D, cliqueEdges (r + 1) Q ⊆ K) (cap : ℕ) (hcap : 0 < cap)
    {L μ ε τ : ℝ} (hL0 : 0 ≤ L) (hτ : 0 < τ)
    (hface : ∀ S : Block V r, ((D.filter fun Q => S.val ⊆ Q.val).card : ℝ) ≤ L)
    (hedge : ∀ e ∈ K, |((D.filter fun Q => e.val ⊆ Q.val).card : ℝ) - μ| ≤ ε * μ) :
    ∃ C : ModularGeneratingData K D N,
      (∀ S : Block V r, (C.generators.filter fun Q => S.val ⊆ Q.val).card ≤ cap) ∧
      C.generators.card ≤ N * K.card ∧
      (C.saturated.card : ℝ) ≤ (q.choose r * (N * K.card) : ℕ) * L / cap ∧
      ((K \ C.good).card : ℝ) ≤ (q.choose (r + 1) : ℝ) * C.saturated.card / τ ∧
      ∀ e ∈ C.good,
        |(((D \ C.saturated).filter fun Q => e.val ⊆ Q.val).card : ℝ) - μ| < ε * μ + τ := by
  obtain ⟨G, hGD, hdegree, hsize, _, hgen⟩ :=
    exists_modular_generators_outside_saturation N hN K D hD cap
  let S := saturatedCliques D G r cap
  let C : ModularGeneratingData K D N := {
    generators := G
    saturated := S
    good := goodCliqueEdges K S τ
    generators_subset := hGD
    saturated_subset := filter_subset _ _
    good_subset := filter_subset _ _
    generates := hgen }
  refine ⟨C, hdegree, hsize, ?_, ?_, ?_⟩
  · have hbound := saturatedCliques_weighted_bound D G r cap (N * K.card) hsize hL0
      (fun T _ => hface T)
    apply (le_div_iff₀ (by exact_mod_cast hcap : (0 : ℝ) < cap)).mpr
    simpa only [mul_comm] using hbound
  · apply (le_div_iff₀ hτ).mpr
    simpa only [mul_comm] using goodCliqueEdges_bad_count K S τ
  · intro e he
    exact goodCliqueEdges_remaining_error K D S C.saturated_subset hedge he

end Arxiv2411_18291
