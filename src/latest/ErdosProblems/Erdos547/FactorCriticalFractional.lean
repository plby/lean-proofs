import ErdosProblems.Erdos547.FractionalFromMatching

/-!
# Perfect fractional matchings in factor-critical graphs

The proof averages one integral near-perfect matching for each missing vertex.
-/

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

/-- Every deletion of one vertex leaves a perfect matching, represented as
a matching in the original graph with exactly that vertex omitted. -/
def IsFactorCritical : Prop :=
  ∀ v, ∃ M : G.Subgraph, M.IsMatching ∧ M.verts = ({v}ᶜ : Set V)

theorem exists_perfect_fractional_of_factorCritical [Nontrivial V]
    (hG : IsFactorCritical G) : ∃ μ : FractionalMatching G, ∀ u, μ.load u = 1 := by
  classical
  choose M hM hverts using hG
  let μ (z : V) := FractionalMatching.ofMatching (M z) (hM z)
  have hload (z u : V) : (μ z).load u = if u = z then 0 else 1 := by
    change (FractionalMatching.ofMatching (M z) (hM z)).load u = _
    rw [FractionalMatching.ofMatching_load, hverts z]
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff, ite_not]
  have hcard : 1 < Fintype.card V := Fintype.one_lt_card
  have hden : 0 < (Fintype.card V : ℝ) - 1 := by
    have h : (1 : ℝ) < Fintype.card V := by exact_mod_cast hcard
    linarith
  let w (u v : V) := (∑ z, (μ z).weight u v) / ((Fintype.card V : ℝ) - 1)
  have hsum (u : V) : (∑ z : V, if u = z then (0 : ℝ) else 1) =
      (Fintype.card V : ℝ) - 1 := by
    have h : (∑ z : V, if u = z then (0 : ℝ) else 1) + 1 = (Fintype.card V : ℝ) := by
      calc
        _ = (∑ z : V, if u = z then (0 : ℝ) else 1) +
            ∑ z : V, if u = z then (1 : ℝ) else 0 := by simp
        _ = ∑ z : V, ((if u = z then (0 : ℝ) else 1) +
            (if u = z then (1 : ℝ) else 0)) := (Finset.sum_add_distrib).symm
        _ = ∑ _z : V, (1 : ℝ) := by
          apply Finset.sum_congr rfl
          intro z _
          split_ifs <;> norm_num
        _ = _ := by simp
    linarith
  have hrow (u : V) : (∑ v, w u v) = 1 := by
    simp only [w, ← Finset.sum_div]
    rw [Finset.sum_comm]
    change (∑ z, (μ z).load u) / ((Fintype.card V : ℝ) - 1) = 1
    simp_rw [hload]
    rw [hsum u, div_self hden.ne']
  let ν : FractionalMatching G := {
    weight := w
    symmetric := fun u v ↦ by
      dsimp [w]
      congr 1
      apply Finset.sum_congr rfl
      intro z _
      exact (μ z).symmetric u v
    nonnegative := fun u v ↦ div_nonneg
      (Finset.sum_nonneg fun z _ ↦ (μ z).nonnegative u v) hden.le
    supported := fun u v h ↦ by
      dsimp [w]
      have hzero : (∑ z, (μ z).weight u v) = 0 :=
        Finset.sum_eq_zero fun z _ ↦ (μ z).supported u v h
      rw [hzero, zero_div]
    capacity := fun u ↦ (hrow u).le }
  exact ⟨ν, hrow⟩

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_perfect_fractional_of_factorCritical
