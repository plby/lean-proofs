import Arxiv.Arxiv2411_18291.IntegralSpan
import Arxiv.Arxiv2411_18291.RepeatedCliqueRoots
import Arxiv.Arxiv2411_18291.DecompositionGluing

/-!
# Boundary degrees of indexed clique families

Repeated cliques are counted with their index multiplicity. The sum of their
edge indicators has coordinate equal to the indexed edge degree, and its
degree at an `(r-1)`-face is `(q-r+1)` times the indexed clique count there.
-/

open Finset
open scoped BigOperators

noncomputable section

namespace Arxiv2411_18291

variable {I V : Type*} [Fintype V] [DecidableEq V] {q r : ℕ}

theorem degree_sum {R : Type*} [AddCommMonoid R] (s : Finset I)
    (J : I → Block V q → R) (T : Finset V) :
    degree (∑ i ∈ s, J i) T = ∑ i ∈ s, degree (J i) T := by
  classical
  simp only [degree, Finset.sum_apply]
  rw [sum_comm]
  apply sum_congr rfl
  intro e _
  by_cases he : T ⊆ e.val
  · simp only [if_pos he]
  · simp only [if_neg he, sum_const_zero]

variable [Fintype I]

theorem sum_clique_indicators_apply (P : I → Block V q) (e : Block V r) :
    (∑ i, indicator (cliqueEdges r (P i))) e = (familyDegree P e.val : ℤ) := by
  simp only [Finset.sum_apply, indicator, mem_cliqueEdges, familyDegree, card_eq_sum_ones,
    sum_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

theorem degree_sum_singleton_indicators (P : I → Block V q) (T : Finset V) :
    degree (∑ i, indicator {P i}) T = (familyDegree P T : ℤ) := by
  rw [degree_sum]
  simp only [degree_indicator, familyDegree, card_eq_sum_ones, sum_filter, Nat.cast_sum,
    Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply sum_congr rfl
  intro i _
  by_cases h : T ⊆ (P i).val <;> simp [filter_singleton, h]

theorem degree_sum_clique_indicators (P : I → Block V q) (T : Block V r) :
    degree (∑ i, indicator (cliqueEdges (r + 1) (P i))) T.val =
      ((q - r : ℕ) : ℤ) * (familyDegree P T.val : ℤ) := by
  have hb : boundary (r + 1) (∑ i, indicator {P i}) =
      ∑ i, indicator (cliqueEdges (r + 1) (P i)) := by
    rw [boundary_sum]
    simp only [boundary_indicator_singleton]
  rw [← hb, degree_boundary _ T.val (by rw [T.property]; omega), degree_sum_singleton_indicators,
    T.property, Nat.add_sub_cancel_left, Nat.choose_one_right]

end Arxiv2411_18291
