/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ClosedThreatCardinality
import ErdosProblems.Erdos207.DriftErrorArithmetic

/-! # Transferring pair and terminal trajectories to exact closed threats -/

namespace Erdos207

open Finset

noncomputable section

theorem abs_greedyClosedThreats_sub_trajectory_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {S : GreedyStateOn V} {T : TripleOn V} {q : ℕ}
    (hS : GreedyInvariant F S) (hT : T ∈ S.available)
    (hpack : ∀ E ∈ F, IsPackingOn E)
    (hcard : ∀ E ∈ F, 2 ≤ E.card → E.card + 2 ≤ q)
    (x ex Z : ℝ) (y ey : ℕ → ℝ)
    (hpair : ∀ P ∈ T.1.powersetCard 2,
      |((availableTrianglesContainingPair S P).card : ℝ) - x| ≤ ex)
    (hterminal : ∀ j ∈ Icc 4 q,
      |((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S T (j - 4)).card : ℝ) - y j| ≤ ey j)
    (hcommon : (selectedCount (fun w : CommonThreatWitness F F T T ↦ w.remainder)
      S.chosen : ℝ) ≤ Z) :
    |((greedyClosedThreats F S T).card : ℝ) - (3 * x + (∑ j ∈ Icc 4 q, y j) - 2)| ≤
      Z + 3 * ex + ∑ j ∈ Icc 4 q, ey j := by
  let A : ℝ := ∑ P ∈ T.1.powersetCard 2, ((availableTrianglesContainingPair S P).card : ℝ)
  let M : ℝ := ∑ j ∈ Icc 4 q,
    ((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S T (j - 4)).card : ℝ)
  have hp : |A - 3 * x| ≤ 3 * ex := by
    simpa only [card_powersetCard, T.2, show Nat.choose 3 2 = 3 from rfl,
      Nat.cast_ofNat, sum_const, nsmul_eq_mul] using
      abs_sum_sub_card_mul_le_sum_error (T.1.powersetCard 2)
        (fun P ↦ ((availableTrianglesContainingPair S P).card : ℝ)) (fun _ ↦ ex) x hpair
  have hm : |M - ∑ j ∈ Icc 4 q, y j| ≤ ∑ j ∈ Icc 4 q, ey j := by
    calc
      _ = |∑ j ∈ Icc 4 q,
          (((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S T (j - 4)).card : ℝ) - y j)| := by
        rw [sum_sub_distrib]
      _ ≤ ∑ j ∈ Icc 4 q,
          |((greedyConfigurationClass (forbiddenFamilyOfOrder F j) S T (j - 4)).card : ℝ) - y j| :=
        abs_sum_le_sum_abs _ _
      _ ≤ _ := sum_le_sum hterminal
  have hcount : |((greedyClosedThreats F S T).card : ℝ) - (A + M - 2)| ≤ Z :=
    (abs_closedThreats_sub_terminal_sum_le hS hT hpack hcard).trans hcommon
  calc
    _ = |(((greedyClosedThreats F S T).card : ℝ) - (A + M - 2)) +
        (A - 3 * x) + (M - ∑ j ∈ Icc 4 q, y j)| := by congr 1; ring
    _ ≤ |((greedyClosedThreats F S T).card : ℝ) - (A + M - 2)| +
        |A - 3 * x| + |M - ∑ j ∈ Icc 4 q, y j| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add hcount hp) hm

end

end Erdos207
