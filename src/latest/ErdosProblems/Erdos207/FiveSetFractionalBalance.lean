/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.FiveSetCorrection

/-! # Finite signed corrections equalize every edge's fractional degree -/

namespace Erdos207

open Finset

noncomputable section

def fiveSetFractionalWeight {V : Type*} [DecidableEq V]
    (E Js : Finset (Finset V)) (c : Finset V → ℝ) (T : Finset V) : ℝ :=
  1 / 4 + (1 / 4) * ∑ P ∈ E, c P *
    ∑ J ∈ Js.filter (P ⊆ ·), fiveSetEdgeCorrection P J T

theorem fiveSet_correction_sum_comm
    {V : Type*} [DecidableEq V] (E Js : Finset (Finset V))
    (c : Finset V → ℝ) (T : Finset V) :
    (∑ P ∈ E, c P * ∑ J ∈ Js.filter (P ⊆ ·), fiveSetEdgeCorrection P J T) =
      ∑ J ∈ Js, ∑ P ∈ E.filter (· ⊆ J), c P * fiveSetEdgeCorrection P J T := by
  simp only [mul_sum, sum_filter]
  rw [sum_comm]
  apply sum_congr rfl
  intro J hJ
  apply sum_congr rfl
  intro P hP
  split_ifs <;> simp

theorem fiveSet_fractional_edge_sum
    {V : Type*} [DecidableEq V] (A E Js : Finset (Finset V))
    (c : Finset V → ℝ) (Q : Finset V) (hQE : Q ∈ E)
    (hA : ∀ T ∈ A, T.card = 3) (hE : ∀ P ∈ E, P.card = 2)
    (hJ : ∀ J ∈ Js, J.card = 5 ∧ J.powersetCard 3 ⊆ A) :
    (∑ T ∈ A.filter (Q ⊆ ·), fiveSetFractionalWeight E Js c T) =
      (A.filter (Q ⊆ ·)).card / 4 + c Q * (Js.filter (Q ⊆ ·)).card / 4 := by
  unfold fiveSetFractionalWeight
  rw [sum_add_distrib, ← mul_sum]
  have hcorr : (∑ T ∈ A.filter (Q ⊆ ·),
      ∑ P ∈ E, c P * ∑ J ∈ Js.filter (P ⊆ ·), fiveSetEdgeCorrection P J T) =
      c Q * (Js.filter (Q ⊆ ·)).card := by
    rw [sum_comm]
    calc
      _ = ∑ P ∈ E, c P * ∑ J ∈ Js.filter (P ⊆ ·),
          if P = Q then (1 : ℝ) else 0 := by
        apply sum_congr rfl
        intro P hP
        rw [← mul_sum, sum_comm]
        congr 1
        apply sum_congr rfl
        intro J hJs
        have hm := mem_filter.mp hJs
        exact fiveSetEdgeCorrection_delta A J P Q hA (hJ J hm.1).1
          (hJ J hm.1).2 (hE P hP) (hE Q hQE) hm.2
      _ = _ := by simp [hQE]
  rw [hcorr]
  simp only [sum_const, nsmul_eq_mul]
  ring

def fiveSetBalancingCoefficient {V : Type*} [DecidableEq V]
    (A Js : Finset (Finset V)) (D : ℝ) (P : Finset V) : ℝ :=
  (D - (A.filter (P ⊆ ·)).card) / (Js.filter (P ⊆ ·)).card

theorem fiveSet_balanced_edge_sum
    {V : Type*} [DecidableEq V] (A E Js : Finset (Finset V))
    (D : ℝ) (Q : Finset V) (hQE : Q ∈ E)
    (hA : ∀ T ∈ A, T.card = 3) (hE : ∀ P ∈ E, P.card = 2)
    (hJ : ∀ J ∈ Js, J.card = 5 ∧ J.powersetCard 3 ⊆ A)
    (hpos : 0 < (Js.filter (Q ⊆ ·)).card) :
    (∑ T ∈ A.filter (Q ⊆ ·),
      fiveSetFractionalWeight E Js (fiveSetBalancingCoefficient A Js D) T) = D / 4 := by
  rw [fiveSet_fractional_edge_sum A E Js _ Q hQE hA hE hJ]
  have hnz : ((Js.filter (Q ⊆ ·)).card : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  unfold fiveSetBalancingCoefficient
  rw [div_mul_cancel₀ _ hnz]
  ring

end

end Erdos207
