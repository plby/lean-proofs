import ErdosProblems.Erdos547.SeparatedRows

/-!
# Constructing a dominated pair from its raw oriented weights
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem PairDominated.load_eq_of_total_eq {γ δ : ℝ}
    {σ : SkewMatching G γ} {τ : SkewMatching G δ} {μ : FractionalMatching G}
    (h : PairDominated σ τ μ) (ht : σ.total + τ.total = 2 * μ.total) (u : V) :
    σ.load u + τ.load u = μ.load u := by
  have hsum : (∑ v, (μ.load v - (σ.load v + τ.load v))) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, μ.sum_load, σ.sum_load, τ.sum_load, ht]
    ring
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun v _ ↦ sub_nonneg.mpr (h.load_le v))).mp
    hsum u (Finset.mem_univ u)
  linarith

theorem exists_pair_of_endpoint_bounds (μ : FractionalMatching G) (γ δ : ℝ)
    (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (f g : V → V → ℝ)
    (hf : ∀ u v, 0 ≤ f u v) (hg : ∀ u v, 0 ≤ g u v)
    (hc : ∀ u v, (f u v + γ * f v u) / (1 + γ) +
      (g u v + δ * g v u) / (1 + δ) ≤ μ.weight u v) :
    ∃ σ : SkewMatching G γ, ∃ τ : SkewMatching G δ, PairDominated σ τ μ ∧
      (∀ u v, σ.weight u v = f u v) ∧ ∀ u v, τ.weight u v = g u v := by
  have hγden : 0 < 1 + γ := by linarith
  have hδden : 0 < 1 + δ := by linarith
  have hfn (u v : V) : 0 ≤ (f u v + γ * f v u) / (1 + γ) :=
    div_nonneg (add_nonneg (hf u v) (mul_nonneg hγ (hf v u))) hγden.le
  have hgn (u v : V) : 0 ≤ (g u v + δ * g v u) / (1 + δ) :=
    div_nonneg (add_nonneg (hg u v) (mul_nonneg hδ (hg v u))) hδden.le
  have hfb (u v : V) : (f u v + γ * f v u) / (1 + γ) ≤ μ.weight u v := by
    linarith [hc u v, hgn u v]
  have hgb (u v : V) : (g u v + δ * g v u) / (1 + δ) ≤ μ.weight u v := by
    linarith [hc u v, hfn u v]
  exact ⟨SkewMatching.ofDominatedWeight μ γ hγ f hf hfb,
    SkewMatching.ofDominatedWeight μ δ hδ g hg hgb, hc, fun _ _ ↦ rfl, fun _ _ ↦ rfl⟩

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_pair_of_endpoint_bounds
