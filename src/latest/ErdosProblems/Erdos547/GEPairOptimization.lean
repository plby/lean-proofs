import ErdosProblems.Erdos547.GEPairs
import ErdosProblems.Erdos547.MixedCompactness

/-!
# Existence of an optimal GE pair

Every constraint is closed in the product of two compact feasible allocation
sets. The initial zero-skew pair proves nonemptiness.
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V}

def mixedLoad (γ : ℝ) (p : (V → V → ℝ) × (V → V → ℝ)) (u : V) : ℝ :=
  (∑ v, p.1 u v) / (1 + γ) + γ * (∑ v, p.1 v u) / (1 + γ) + ∑ v, p.2 u v

namespace GallaiEdmondsPartition

def gePairConstraints (D : GallaiEdmondsPartition G) (w : EdgeWeights G) (c : V)
    (μ : FractionalMatching G) (γ : ℝ) : Set ((V → V → ℝ) × (V → V → ℝ)) := {p |
  (∀ u, mixedLoad γ p u ≤ 1) ∧
  (∀ u v, ¬ (u ∈ D.reachableNeighbours w c μ ∧ v ∈ D.reachableVertices w c μ) → p.1 u v = 0) ∧
  (∀ u, (∑ v, p.1 u v) / (1 + γ) ≤ w.weight c u) ∧
  (∀ u ∈ D.reachableVertices w c μ, mixedLoad γ p u ≤ w.weight c u) ∧
  (∀ u ∉ D.reachableVertices w c μ, w.weight c u ≤ mixedLoad γ p u) ∧
  (∀ u ∈ D.separator, mixedLoad γ p u = 1) ∧
  (∀ u v, u ∉ D.reachableVertices w c μ ∪ D.reachableNeighbours w c μ →
    v ∉ D.reachableVertices w c μ ∪ D.reachableNeighbours w c μ → p.2 u v = μ.weight u v) ∧
  ∀ u v, (u ∈ D.reachableVertices w c μ ∪ D.reachableNeighbours w c μ ∨
    v ∈ D.reachableVertices w c μ ∪ D.reachableNeighbours w c μ) →
    ¬ D.ReachableCross w c μ u v → p.2 u v = 0}

theorem mem_gePairConstraints_iff (D : GallaiEdmondsPartition G) (w : EdgeWeights G)
    (c : V) (μ : FractionalMatching G) {γ : ℝ} (σ : SkewMatching G γ) (ν : FractionalMatching G) :
    (σ.weight, ν.weight) ∈ D.gePairConstraints w c μ γ ↔ D.IsGEPair w c μ σ ν := by
  constructor
  · intro h
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1,
      h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩
  · intro h
    exact ⟨h.capacity, h.skew_supported, h.fits, h.reachable_upper, h.outside_lower,
      h.covers_separator, h.fixed_outside, h.fractional_cross⟩

theorem isClosed_gePairConstraints (D : GallaiEdmondsPartition G) (w : EdgeWeights G)
    (c : V) (μ : FractionalMatching G) (γ : ℝ) : IsClosed (D.gePairConstraints w c μ γ) := by
  have hL (u : V) : Continuous (fun p : (V → V → ℝ) × (V → V → ℝ) ↦ mixedLoad γ p u) := by
    unfold mixedLoad
    fun_prop
  have h₁ : IsClosed {p : (V → V → ℝ) × (V → V → ℝ) | ∀ u, mixedLoad γ p u ≤ 1} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_le (hL u) continuous_const
  have h₂ : IsClosed {p : (V → V → ℝ) × (V → V → ℝ) |
      ∀ u v, ¬ (u ∈ D.reachableNeighbours w c μ ∧ v ∈ D.reachableVertices w c μ) →
        p.1 u v = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_iInter fun v ↦ isClosed_iInter fun _ ↦
      isClosed_eq (by fun_prop) continuous_const
  have h₃ : IsClosed {p : (V → V → ℝ) × (V → V → ℝ) |
      ∀ u, (∑ v, p.1 u v) / (1 + γ) ≤ w.weight c u} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_le (by fun_prop) continuous_const
  have h₄ : IsClosed {p : (V → V → ℝ) × (V → V → ℝ) |
      ∀ u ∈ D.reachableVertices w c μ, mixedLoad γ p u ≤ w.weight c u} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_iInter fun _ ↦ isClosed_le (hL u) continuous_const
  have h₅ : IsClosed {p : (V → V → ℝ) × (V → V → ℝ) |
      ∀ u ∉ D.reachableVertices w c μ, w.weight c u ≤ mixedLoad γ p u} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_iInter fun _ ↦ isClosed_le continuous_const (hL u)
  have h₆ : IsClosed {p : (V → V → ℝ) × (V → V → ℝ) |
      ∀ u ∈ D.separator, mixedLoad γ p u = 1} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_iInter fun _ ↦ isClosed_eq (hL u) continuous_const
  have h₇ : IsClosed {p : (V → V → ℝ) × (V → V → ℝ) |
      ∀ u v, u ∉ D.reachableVertices w c μ ∪ D.reachableNeighbours w c μ →
        v ∉ D.reachableVertices w c μ ∪ D.reachableNeighbours w c μ → p.2 u v = μ.weight u v} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_iInter fun v ↦ isClosed_iInter fun _ ↦
      isClosed_iInter fun _ ↦ isClosed_eq (by fun_prop) continuous_const
  have h₈ : IsClosed {p : (V → V → ℝ) × (V → V → ℝ) |
      ∀ u v, (u ∈ D.reachableVertices w c μ ∪ D.reachableNeighbours w c μ ∨
        v ∈ D.reachableVertices w c μ ∪ D.reachableNeighbours w c μ) →
        ¬ D.ReachableCross w c μ u v → p.2 u v = 0} := by
    simp only [Set.ofPred_forall]
    exact isClosed_iInter fun u ↦ isClosed_iInter fun v ↦ isClosed_iInter fun _ ↦
      isClosed_iInter fun _ ↦ isClosed_eq (by fun_prop) continuous_const
  exact h₁.inter (h₂.inter (h₃.inter (h₄.inter (h₅.inter (h₆.inter (h₇.inter h₈))))))

theorem exists_optimal_gePair (D : GallaiEdmondsPartition G) (w : EdgeWeights G) (c : V)
    (μ : FractionalMatching G) (hμ : D.IsMaxSaturation w c μ) (γ : ℝ) (hγ : 0 ≤ γ) :
    ∃ σ : SkewMatching G γ, ∃ ν : FractionalMatching G, D.IsGEPair w c μ σ ν ∧
      ∀ τ : SkewMatching G γ, ∀ ξ : FractionalMatching G, D.IsGEPair w c μ τ ξ →
        w.saturation (fun u ↦ τ.load u + ξ.load u) c ≤
          w.saturation (fun u ↦ σ.load u + ν.load u) c := by
  have hne : ∃ σ : SkewMatching G γ, ∃ ν : FractionalMatching G,
      (σ.weight, ν.weight) ∈ D.gePairConstraints w c μ γ := by
    refine ⟨SkewMatching.zero G γ hγ, μ, ?_⟩
    exact (D.mem_gePairConstraints_iff w c μ _ _).mpr (hμ.initial_gePair γ hγ)
  obtain ⟨σ, ν, hpair, hmax⟩ := exists_maximizing_mixed_with_constraints G γ hγ
    (D.gePairConstraints w c μ γ) (D.isClosed_gePairConstraints w c μ γ) hne
    (fun p ↦ ∑ u, min (w.weight c u) (mixedLoad γ p u)) (by unfold mixedLoad; fun_prop)
  refine ⟨σ, ν, (D.mem_gePairConstraints_iff w c μ σ ν).mp hpair, ?_⟩
  intro τ ξ hτ
  exact hmax τ ξ ((D.mem_gePairConstraints_iff w c μ τ ξ).mpr hτ)

end GallaiEdmondsPartition

end Erdos547.DPRS

#print axioms Erdos547.DPRS.GallaiEdmondsPartition.exists_optimal_gePair
