import ErdosProblems.Erdos547.SkewMatching
import Mathlib.Combinatorics.SimpleGraph.Matching

/-!
# Integral matchings as fractional matchings
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

open scoped Classical in
theorem matching_indicator_sum (M : G.Subgraph) (hM : M.IsMatching) (u : V) :
    (∑ v, if M.Adj u v then (1 : ℝ) else 0) = if u ∈ M.verts then 1 else 0 := by
  classical
  by_cases hu : u ∈ M.verts
  · obtain ⟨v, huv, huniq⟩ := hM hu
    rw [if_pos hu]
    have hsum : (∑ w, if M.Adj u w then (1 : ℝ) else 0) =
        if M.Adj u v then 1 else 0 := by
      apply Finset.sum_eq_single v
      · intro w _ hwv
        have hnot : ¬ M.Adj u w := fun h ↦ hwv (huniq w h)
        simp [hnot]
      · intro h
        exact (h (Finset.mem_univ v)).elim
    simpa only [if_pos huv] using hsum
  · rw [if_neg hu]
    apply Finset.sum_eq_zero
    intro v _
    have hnot : ¬ M.Adj u v := fun h ↦ hu h.fst_mem
    simp [hnot]

namespace FractionalMatching

open scoped Classical in
def ofMatching (M : G.Subgraph) (hM : M.IsMatching) : FractionalMatching G where
  weight u v := if M.Adj u v then 1 else 0
  symmetric u v := by simp only [M.adj_comm]
  nonnegative u v := by split_ifs <;> norm_num
  supported u v h := by
    have hnot : ¬ M.Adj u v := fun hM ↦ h (M.adj_sub hM)
    simp [hnot]
  capacity u := by
    rw [matching_indicator_sum M hM u]
    split_ifs <;> norm_num

open scoped Classical in
theorem ofMatching_load (M : G.Subgraph) (hM : M.IsMatching) (u : V) :
    (ofMatching M hM).load u = if u ∈ M.verts then 1 else 0 := by
  exact matching_indicator_sum M hM u

/-- A symmetric fractional matching is an oriented allocation of any
nonnegative skew, with unchanged total vertex loads. -/
def toSkew (μ : FractionalMatching G) (γ : ℝ) (hγ : 0 ≤ γ) : SkewMatching G γ where
  skew_nonneg := hγ
  weight := μ.weight
  nonnegative := μ.nonnegative
  supported := μ.supported
  capacity u := by
    have hcol : (∑ v, μ.weight v u) = ∑ v, μ.weight u v := by
      apply Finset.sum_congr rfl
      intro v _
      exact μ.symmetric v u
    rw [hcol]
    have hcap := μ.capacity u
    have hmul := mul_le_mul_of_nonneg_left hcap hγ
    linarith

theorem toSkew_load (μ : FractionalMatching G) (γ : ℝ) (hγ : 0 ≤ γ) (u : V) :
    (μ.toSkew γ hγ).load u = μ.load u := by
  have hcol : (∑ v, μ.weight v u) = ∑ v, μ.weight u v := by
    apply Finset.sum_congr rfl
    intro v _
    exact μ.symmetric v u
  simp only [SkewMatching.load, SkewMatching.outLoad, SkewMatching.inLoad, toSkew, hcol, load]
  have hden : 1 + γ ≠ 0 := by linarith
  field_simp [hden]

theorem toSkew_total (μ : FractionalMatching G) (γ : ℝ) (hγ : 0 ≤ γ) :
    (μ.toSkew γ hγ).total = 2 * μ.total := by
  simp only [SkewMatching.total, toSkew, total]
  ring

end FractionalMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.FractionalMatching.ofMatching_load
#print axioms Erdos547.DPRS.FractionalMatching.toSkew_load
