import ErdosProblems.Erdos547.SkewMatching

/-!
# Comparing fractional and skew allocations at their endpoints
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ δ : ℝ}

namespace SkewMatching

/-- The load at `u` contributed by the two orientations of the edge `uv`. -/
def endpointWeight (σ : SkewMatching G γ) (u v : V) : ℝ :=
  (σ.weight u v + γ * σ.weight v u) / (1 + γ)

theorem endpointWeight_nonneg (σ : SkewMatching G γ) (u v : V) :
    0 ≤ σ.endpointWeight u v :=
  div_nonneg (add_nonneg (σ.nonnegative u v) (mul_nonneg σ.skew_nonneg
    (σ.nonnegative v u))) σ.denominator_pos.le

theorem sum_endpointWeight (σ : SkewMatching G γ) (u : V) :
    (∑ v, σ.endpointWeight u v) = σ.load u := by
  simp only [endpointWeight, load, outLoad, inLoad, ← Finset.sum_div,
    Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

/-- A suballocation may have a different skew; both endpoint contributions
of each oriented arc must be dominated. -/
def IsSuballocation (τ : SkewMatching G δ) (σ : SkewMatching G γ) : Prop :=
  ∀ u v, τ.weight u v / (1 + δ) ≤ σ.weight u v / (1 + γ) ∧
    δ * τ.weight u v / (1 + δ) ≤ γ * σ.weight u v / (1 + γ)

theorem IsSuballocation.endpoint_le {τ : SkewMatching G δ} {σ : SkewMatching G γ}
    (h : τ.IsSuballocation σ) (u v : V) : τ.endpointWeight u v ≤ σ.endpointWeight u v := by
  simp only [endpointWeight, add_div]
  exact add_le_add (h u v).1 (h v u).2

theorem IsSuballocation.load_le {τ : SkewMatching G δ} {σ : SkewMatching G γ}
    (h : τ.IsSuballocation σ) (u : V) : τ.load u ≤ σ.load u := by
  rw [← τ.sum_endpointWeight, ← σ.sum_endpointWeight]
  exact Finset.sum_le_sum fun v _ ↦ h.endpoint_le u v

theorem IsSuballocation.total_le {τ : SkewMatching G δ} {σ : SkewMatching G γ}
    (h : τ.IsSuballocation σ) : τ.total ≤ σ.total := by
  rw [← τ.sum_load, ← σ.sum_load]
  exact Finset.sum_le_sum fun u _ ↦ h.load_le u

/-- Domination by a symmetric fractional matching is required in both
orientations of every edge. Zero-weight cases satisfy this automatically. -/
def DominatedByFractional (σ : SkewMatching G γ) (μ : FractionalMatching G) : Prop :=
  ∀ u v, σ.endpointWeight u v ≤ μ.weight u v

theorem DominatedByFractional.load_le {σ : SkewMatching G γ} {μ : FractionalMatching G}
    (h : σ.DominatedByFractional μ) (u : V) : σ.load u ≤ μ.load u := by
  rw [← σ.sum_endpointWeight]
  exact Finset.sum_le_sum fun v _ ↦ h u v

theorem DominatedByFractional.total_le {σ : SkewMatching G γ} {μ : FractionalMatching G}
    (h : σ.DominatedByFractional μ) : σ.total ≤ 2 * μ.total := by
  rw [← σ.sum_load, ← μ.sum_load]
  exact Finset.sum_le_sum fun u _ ↦ h.load_le u

theorem DominatedByFractional.load_eq_of_total_eq {σ : SkewMatching G γ}
    {μ : FractionalMatching G} (h : σ.DominatedByFractional μ)
    (htotal : σ.total = 2 * μ.total) (u : V) : σ.load u = μ.load u := by
  have hsum : (∑ v, (μ.load v - σ.load v)) = 0 := by
    rw [Finset.sum_sub_distrib, μ.sum_load, σ.sum_load, htotal, sub_self]
  have hnonneg : ∀ v ∈ (Finset.univ : Finset V), 0 ≤ μ.load v - σ.load v :=
    fun v _ ↦ sub_nonneg.mpr (h.load_le v)
  have hu := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum u (Finset.mem_univ u)
  linarith

end SkewMatching

namespace FractionalMatching

def DominatedBySkew (μ : FractionalMatching G) (σ : SkewMatching G γ) : Prop :=
  ∀ u v, μ.weight u v ≤ σ.endpointWeight u v

theorem DominatedBySkew.load_le {μ : FractionalMatching G} {σ : SkewMatching G γ}
    (h : μ.DominatedBySkew σ) (u : V) : μ.load u ≤ σ.load u := by
  rw [← σ.sum_endpointWeight]
  exact Finset.sum_le_sum fun v _ ↦ h u v

theorem dominatedBySkew_toFractional_of_suballocation (σ : SkewMatching G 1)
    (τ : SkewMatching G γ) (h : σ.IsSuballocation τ) : σ.toFractional.DominatedBySkew τ := by
  intro u v
  have heq : σ.toFractional.weight u v = σ.endpointWeight u v := by
    norm_num [SkewMatching.toFractional, SkewMatching.endpointWeight]
  rw [heq]
  exact h.endpoint_le u v

end FractionalMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.SkewMatching.DominatedByFractional.load_eq_of_total_eq
#print axioms Erdos547.DPRS.FractionalMatching.dominatedBySkew_toFractional_of_suballocation
