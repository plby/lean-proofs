/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos546.Basic
import ErdosProblems.Erdos546.Numeric

/-!
# Erdős Problem 546: the bounded-scale clique bound

This file turns the elementary diagonal clique Ramsey estimate into a coarse
bound for the Ramsey number of an arbitrary graph.  It is used for the
bounded `sqrtScale m < 32` branch of Sudakov's argument.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos546

open SimpleGraph

/-- A diagonal clique Ramsey property implies the corresponding property for
every graph on the same number of vertices. -/
theorem graphRamseyProperty_of_diagonal {v N : ℕ}
    (G : SimpleGraph (Fin v)) (h : Ramsey.RamseyProperty v v N) :
    GraphRamseyProperty G N := by
  intro R
  have hGtop : G ⊑ completeGraph (Fin v) := IsContained.of_le le_top
  by_cases hR : R.CliqueFree v
  · right
    have hRc : ¬ Rᶜ.CliqueFree v := by
      intro hRc
      exact h R ⟨hR, by simpa [cliqueFree_compl] using hRc⟩
    exact hGtop.trans ((Rᶜ.not_cliqueFree_iff_top_isContained v).mp hRc)
  · left
    exact hGtop.trans ((R.not_cliqueFree_iff_top_isContained v).mp hR)

/-- The usual Erdős--Szekeres diagonal estimate, in a deliberately coarse
power-of-two form sufficient for the small-scale branch. -/
theorem graphRamseyProperty_two_pow_two_mul (G : SimpleGraph (Fin v)) :
    GraphRamseyProperty G (2 ^ (2 * v)) := by
  apply graphRamseyProperty_of_diagonal G
  apply Ramsey.ramseyProperty_of_ramseyNumber_le
  cases v with
  | zero => simp [Ramsey.ramseyNumber_zero_right]
  | succ u =>
      calc
        Ramsey.ramseyNumber (u + 1) (u + 1)
            ≤ Nat.choose (u + (u + 1) - 1) u :=
          Ramsey.ramseyNumber_le_choose u (u + 1)
        _ ≤ 2 ^ (u + (u + 1) - 1) := Nat.choose_le_two_pow _ _
        _ ≤ 2 ^ (2 * (u + 1)) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)

/-- In terms of the edge count, the elementary clique argument gives the
coarse bound `2^(4m)` for graphs without isolated vertices. -/
theorem graphRamseyProperty_two_pow_four_mul_edges {v m : ℕ}
    (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (hG : ∀ x, ¬ G.IsIsolated x) (hm : G.edgeFinset.card = m) :
    GraphRamseyProperty G (2 ^ (4 * m)) := by
  have hv : v ≤ 2 * m := by
    simpa [hm] using noIsolated_card_le_twice_edges G hG
  apply graphRamseyProperty_mono
    (Nat.pow_le_pow_right (by norm_num) (by omega : 2 * v ≤ 4 * m))
  exact graphRamseyProperty_two_pow_two_mul G

/-- The complete small-scale branch.  If `s = Nat.sqrt m + 1` is below `32`,
the universal host order `2^(32768s)` already follows from the elementary
clique Ramsey bound. -/
theorem smallScale_graphRamseyProperty {v m : ℕ}
    (G : SimpleGraph (Fin v)) [DecidableRel G.Adj]
    (hG : ∀ x, ¬ G.IsIsolated x) (hm : G.edgeFinset.card = m)
    (hsmall : sqrtScale m < 32) :
    GraphRamseyProperty G (2 ^ (32768 * sqrtScale m)) := by
  by_cases hmzero : m = 0
  · have hv : v = 0 :=
      card_eq_zero_of_noIsolated_of_edgeFinset_card_eq_zero G hG (hm.trans hmzero)
    subst v
    subst m
    apply graphRamseyProperty_mono (N := 2 ^ (2 * 0))
      (by
        simpa only [mul_zero, pow_zero] using
          (Nat.one_le_pow (32768 * sqrtScale 0) 2 (by norm_num)))
    exact graphRamseyProperty_two_pow_two_mul G
  · have hv : v ≤ 2 * m := by
      simpa [hm] using noIsolated_card_le_twice_edges G hG
    have hvs : v ≤ 2 * sqrtScale m ^ 2 :=
      hv.trans (Nat.mul_le_mul_left 2 (le_sqrtScale_sq m))
    have hsmallExponent : 2 * v ≤ 124 * sqrtScale m :=
      small_scale_exponent_bound hsmall hvs
    have hexponent : 2 * v ≤ 32768 * sqrtScale m :=
      hsmallExponent.trans (Nat.mul_le_mul_right (sqrtScale m) (by norm_num))
    apply graphRamseyProperty_mono
      (Nat.pow_le_pow_right (by norm_num) hexponent)
    exact graphRamseyProperty_two_pow_two_mul G

end Erdos546
