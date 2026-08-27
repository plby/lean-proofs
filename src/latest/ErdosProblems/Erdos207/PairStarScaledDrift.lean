/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PairStarDriftError
import ErdosProblems.Erdos207.GlobalPairTrajectory
import ErdosProblems.Erdos207.CoupledDenominatorBudget
import ErdosProblems.Erdos207.CoupledDriftBudgetArithmetic

/-! # The pair drift on the source's error-over-residual-edge scale -/

namespace Erdos207

open Finset

noncomputable section

theorem pairStar_selector_denominator_budget
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (P : Finset V) (L x e : ℝ)
    (hL : 24 ≤ L) (hx : 0 < x) (he : e ≤ x / 4)
    (hpair : |((availableTrianglesContainingPair S P).card : ℝ) - x| ≤ e)
    (havailable : |(S.available.card : ℝ) - L * x / 3| ≤ L * e / 3)
    (hxe : x ≤ L * e) :
    let R := S.available \ availableTrianglesContainingPair S P
    L * x / 6 ≤ (R.card : ℝ) ∧ |(R.card : ℝ) - L * x / 3| ≤ (7 / 3) * L * e := by
  dsimp only
  have hs : availableTrianglesContainingPair S P ⊆ S.available := by
    intro T hT
    exact (mem_availableTrianglesContainingPair_iff.mp hT).1
  rw [card_sdiff_of_subset hs, Nat.cast_sub (card_le_card hs)]
  exact coupled_pair_denominator_budget hL hx he (Nat.cast_nonneg _) hpair havailable hxe

theorem pairStar_selectors_nonempty_of_trajectory
    {V : Type*} [Fintype V] [DecidableEq V]
    (S : GreedyStateOn V) (P : Finset V) (L x e : ℝ)
    (hL : 24 ≤ L) (hx : 0 < x) (he : e ≤ x / 4)
    (hpair : |((availableTrianglesContainingPair S P).card : ℝ) - x| ≤ e)
    (havailable : |(S.available.card : ℝ) - L * x / 3| ≤ L * e / 3)
    (hxe : x ≤ L * e) :
    (S.available \ availableTrianglesContainingPair S P).Nonempty := by
  have hb := (pairStar_selector_denominator_budget S P L x e hL hx he hpair havailable hxe).1
  have hLpos : 0 < L := by linarith
  have hp : (0 : ℝ) < (S.available \ availableTrianglesContainingPair S P).card :=
    lt_of_lt_of_le (by positivity) hb
  exact card_pos.mp (by exact_mod_cast hp)

theorem restrictedGreedyKernel_pairStar_drift_source_scale
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {P : Finset V}
    (hS : GreedyInvariant F S) (hP : P.card = 2)
    (hR : (S.available \ availableTrianglesContainingPair S P).Nonempty)
    (L x e H k C : ℝ) (hL : 24 ≤ L) (hx : 0 < x) (he : e ≤ x / 4)
    (hk : 0 ≤ k) (hC : 0 ≤ C) (hH : |H| ≤ C * x)
    (hpair : |((availableTrianglesContainingPair S P).card : ℝ) - x| ≤ e)
    (havailable : |(S.available.card : ℝ) - L * x / 3| ≤ L * e / 3)
    (hxe : x ≤ L * e)
    (hthreat : ∀ U ∈ availableTrianglesContainingPair S P,
      |((greedyClosedThreats F S U).card : ℝ) - H| ≤ k * e) :
    let Q := availableTrianglesContainingPair S P
    let R := S.available \ Q
    |(restrictedGreedyKernel F S R hR).expectationReal
        (fun S' ↦ greedyAvailableCountReal Q S' - greedyAvailableCountReal Q S) +
      3 * (H - x) / L| ≤ (12 * k + 48 * C + 60) * e / L := by
  dsimp only
  let Q := availableTrianglesContainingPair S P
  let R := S.available \ Q
  have hLpos : 0 < L := by linarith
  have he0 : 0 ≤ e := (abs_nonneg _).trans hpair
  have hu : (Q.card : ℝ) ≤ 2 * x := by
    have hh := (abs_le.mp hpair).2
    change (Q.card : ℝ) - x ≤ e at hh
    linarith
  have hbudget := pairStar_selector_denominator_budget S P L x e hL hx he hpair havailable hxe
  have hraw := restrictedGreedyKernel_pairStar_drift_trajectory_error hS hP hR
    H (k * e) x e (L * x / 3) ((7 / 3) * L * e) (by positivity)
    hthreat hpair hbudget.2
  have hscaled := pair_drift_error_coupled_scale hLpos hx he0 (Nat.cast_nonneg Q.card) hu
    hbudget.1 hk hC (by norm_num : (0 : ℝ) ≤ 7 / 3) hH
  have h := hraw.trans hscaled
  have heq : x * (H - x) / (L * x / 3) = 3 * (H - x) / L := by
    field_simp
  rw [heq] at h
  have hcoef : 12 * k + 6 * (C + 3) + 18 * (7 / 3) * (C + 1) =
      12 * k + 48 * C + 60 := by ring
  simpa only [hcoef] using h

end

end Erdos207
