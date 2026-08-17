/-
Copyright (c) 2026.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex, Boris Alexeev
-/
import ErdosProblems.Erdos1027.DGKCounts
import ErdosProblems.Erdos1027.DGKFixedEdge
import ErdosProblems.Erdos1027.FiniteExposure

/-!
# Conditional and averaged fixed-edge fiber estimates

This file packages the exact product count in `DGKCounts` in the form used
after all coordinates outside a fixed edge have been exposed.  The caller
only has to prove that its actual final-edge event is contained in the
coordinatewise target-or-exceptional event.  The exceptional priority
density at a vertex may be bounded by an arbitrary nonnegative penalty.

If the sum of those penalties is at most `M`, the conditional probability is
at most

`2 ^ (-|edge|) * exp M * (sum of the penalties)`.

The last theorem averages this pointwise fiber estimate over the exposed
outside coordinates.  The module is deliberately independent of the
particular recolouring algorithm: `DGKPropertyB` supplies the deterministic
fiber inclusion and the threat-load estimates.
-/

namespace Erdos1027.DGKFiber

open scoped BigOperators
open Finset
open Erdos1027.FiniteExpect

/-- Conditional fixed-edge estimate on one exposed fiber.

`high v` is the set of exceptional priority labels at `v`.  The hypothesis
`hdensity` allows those exact rational densities to be enlarged to the real
penalties used by the analytic part of the DGK proof. -/
theorem conditional_indicator_le_exp_penalty
    {V : Type*} [DecidableEq V]
    (edge : Finset V) {N : ℕ} (hN : 0 < N) (target : Bool)
    (high : V → Finset (Fin N)) (penalty : V → ℝ) (M : ℝ)
    (event : Erdos1027.DGKCounts.EdgeLabels edge N → Prop)
    (hevent : ∀ assignment, event assignment →
      assignment ∈ Erdos1027.DGKCounts.conditionalThreatAssignments
        edge N target high)
    (hdensity : ∀ v : ↥edge,
      ((high v).card : ℝ) / N ≤ penalty v)
    (hpenalty : ∀ v : ↥edge, 0 ≤ penalty v)
    (hcap : ∑ v ∈ edge, penalty v ≤ M) :
    (((𝔼 assignment : Erdos1027.DGKCounts.EdgeLabels edge N,
        indicator (event assignment)) : ℚ) : ℝ) ≤
      Erdos1027.DGKFixedEdge.invTwoPow edge.card * Real.exp M *
        ∑ v ∈ edge, penalty v := by
  classical
  have hcountQ :=
    Erdos1027.DGKCounts.expect_indicator_event_le_conditionalThreat
      edge hN target high event hevent
  have hcountR :
      (((𝔼 assignment : Erdos1027.DGKCounts.EdgeLabels edge N,
          indicator (event assignment)) : ℚ) : ℝ) ≤
        (((((1 : ℚ) / 2) ^ edge.card) *
          ((∏ v : ↥edge,
              (1 + ((high v).card : ℚ) / N)) - 1) : ℚ) : ℝ) := by
    exact (Rat.cast_le (K := ℝ)).2 hcountQ
  have hcastProduct :
      (((((1 : ℚ) / 2) ^ edge.card) *
          ((∏ v : ↥edge,
              (1 + ((high v).card : ℚ) / N)) - 1) : ℚ) : ℝ) =
        Erdos1027.DGKFixedEdge.invTwoPow edge.card *
          ((∏ v : ↥edge,
              (1 + ((high v).card : ℝ) / N)) - 1) := by
    norm_num [Erdos1027.DGKFixedEdge.invTwoPow]
  rw [hcastProduct] at hcountR
  have hprod :
      (∏ v : ↥edge, (1 + ((high v).card : ℝ) / N)) ≤
        ∏ v : ↥edge, (1 + penalty v) := by
    apply Finset.prod_le_prod
    · intro v hv
      positivity
    · intro v hv
      simpa [add_comm] using add_le_add_left (hdensity v) 1
  have hproductBound :
      Erdos1027.DGKFixedEdge.invTwoPow edge.card *
          ((∏ v : ↥edge,
              (1 + ((high v).card : ℝ) / N)) - 1) ≤
        Erdos1027.DGKFixedEdge.invTwoPow edge.card *
          ((∏ v : ↥edge, (1 + penalty v)) - 1) := by
    exact mul_le_mul_of_nonneg_left (sub_le_sub_right hprod 1)
      (Erdos1027.DGKFixedEdge.invTwoPow_nonneg _)
  have hexponential :
      (∏ v : ↥edge, (1 + penalty v)) - 1 ≤
        Real.exp M * ∑ v ∈ edge, penalty v := by
    rw [Finset.prod_coe_sort edge (fun v ↦ 1 + penalty v)]
    exact Erdos1027.DGKFixedEdge.prod_one_add_sub_one_le_exp_cap_mul_sum
      edge penalty (fun v hv ↦ hpenalty ⟨v, hv⟩) hcap
  calc
    (((𝔼 assignment : Erdos1027.DGKCounts.EdgeLabels edge N,
        indicator (event assignment)) : ℚ) : ℝ) ≤
        Erdos1027.DGKFixedEdge.invTwoPow edge.card *
          ((∏ v : ↥edge,
              (1 + ((high v).card : ℝ) / N)) - 1) := hcountR
    _ ≤ Erdos1027.DGKFixedEdge.invTwoPow edge.card *
          ((∏ v : ↥edge, (1 + penalty v)) - 1) := hproductBound
    _ ≤ Erdos1027.DGKFixedEdge.invTwoPow edge.card *
          (Real.exp M * ∑ v ∈ edge, penalty v) :=
      mul_le_mul_of_nonneg_left hexponential
        (Erdos1027.DGKFixedEdge.invTwoPow_nonneg _)
    _ = Erdos1027.DGKFixedEdge.invTwoPow edge.card * Real.exp M *
          ∑ v ∈ edge, penalty v := by ring

/-- The conditional estimate stated for an actual global event after one
outside assignment has been exposed. -/
theorem exposed_fiber_indicator_le_exp_penalty
    {V : Type*} [Fintype V] [DecidableEq V]
    (edge : Finset V) {N : ℕ} (hN : 0 < N) (target : Bool)
    (outside : Erdos1027.FiniteExposure.OutsideAssignment
      (A := Bool × Fin N) edge)
    (high : V → Finset (Fin N)) (penalty : V → ℝ) (M : ℝ)
    (event : (V → Bool × Fin N) → Prop)
    (hevent : ∀ inside,
      event (Erdos1027.FiniteExposure.glue edge outside inside) →
        inside ∈ Erdos1027.DGKCounts.conditionalThreatAssignments
          edge N target high)
    (hdensity : ∀ v : ↥edge,
      ((high v).card : ℝ) / N ≤ penalty v)
    (hpenalty : ∀ v : ↥edge, 0 ≤ penalty v)
    (hcap : ∑ v ∈ edge, penalty v ≤ M) :
    (((𝔼 inside : Erdos1027.FiniteExposure.InsideAssignment
          (A := Bool × Fin N) edge,
        indicator (event
          (Erdos1027.FiniteExposure.glue edge outside inside))) : ℚ) : ℝ) ≤
      Erdos1027.DGKFixedEdge.invTwoPow edge.card * Real.exp M *
        ∑ v ∈ edge, penalty v := by
  classical
  exact conditional_indicator_le_exp_penalty edge hN target high penalty M
    (fun inside ↦ event
      (Erdos1027.FiniteExposure.glue edge outside inside))
    hevent hdensity hpenalty hcap

/-- Average a conditional fixed-edge estimate over all exposed outside
assignments.  This is the tower-property step needed after
`exposed_fiber_indicator_le_exp_penalty`.

The hypothesis `hfiber` may come directly from that theorem, while
`hexpectedPenalty` is the separate expected threat-load estimate. -/
theorem global_indicator_le_of_exposed_fiber_penalty
    {V : Type*} [Fintype V] [DecidableEq V]
    (edge : Finset V) {N : ℕ}
    (event : (V → Bool × Fin N) → Prop)
    (penaltySum : Erdos1027.FiniteExposure.OutsideAssignment
      (A := Bool × Fin N) edge → ℝ)
    (M expectedPenaltyBound : ℝ)
    (hfiber : ∀ outside,
      (((𝔼 inside : Erdos1027.FiniteExposure.InsideAssignment
            (A := Bool × Fin N) edge,
          indicator (event
            (Erdos1027.FiniteExposure.glue edge outside inside))) : ℚ) : ℝ) ≤
        Erdos1027.DGKFixedEdge.invTwoPow edge.card * Real.exp M *
          penaltySum outside)
    (hexpectedPenalty :
      (𝔼 outside : Erdos1027.FiniteExposure.OutsideAssignment
        (A := Bool × Fin N) edge, penaltySum outside) ≤
          expectedPenaltyBound) :
    (((𝔼 w : V → Bool × Fin N, indicator (event w)) : ℚ) : ℝ) ≤
      Erdos1027.DGKFixedEdge.invTwoPow edge.card * Real.exp M *
        expectedPenaltyBound := by
  classical
  let C : ℝ :=
    Erdos1027.DGKFixedEdge.invTwoPow edge.card * Real.exp M
  have hC : 0 ≤ C :=
    mul_nonneg (Erdos1027.DGKFixedEdge.invTwoPow_nonneg _)
      (Real.exp_pos _).le
  calc
    (((𝔼 w : V → Bool × Fin N, indicator (event w)) : ℚ) : ℝ) =
        𝔼 outside : Erdos1027.FiniteExposure.OutsideAssignment
            (A := Bool × Fin N) edge,
          (((𝔼 inside : Erdos1027.FiniteExposure.InsideAssignment
              (A := Bool × Fin N) edge,
            indicator (event
              (Erdos1027.FiniteExposure.glue edge outside inside))) : ℚ) : ℝ) := by
      simp only [indicator]
      rw [Erdos1027.FiniteExposure.expect_event_indicator_eq_expect_fiber]
      exact algebraMap.coe_expect
        (M := ℚ) (N := ℝ) Finset.univ
        (fun outside : Erdos1027.FiniteExposure.OutsideAssignment
            (A := Bool × Fin N) edge ↦
          (𝔼 inside : Erdos1027.FiniteExposure.InsideAssignment
              (A := Bool × Fin N) edge,
            (if event
              (Erdos1027.FiniteExposure.glue edge outside inside)
             then 1 else 0 : ℚ)))
    _ ≤ 𝔼 outside : Erdos1027.FiniteExposure.OutsideAssignment
            (A := Bool × Fin N) edge,
          C * penaltySum outside := by
      apply Finset.expect_le_expect
      intro outside _
      simpa [C, mul_assoc] using hfiber outside
    _ = C * (𝔼 outside : Erdos1027.FiniteExposure.OutsideAssignment
            (A := Bool × Fin N) edge, penaltySum outside) := by
      exact (Finset.mul_expect Finset.univ penaltySum C).symm
    _ ≤ C * expectedPenaltyBound :=
      mul_le_mul_of_nonneg_left hexpectedPenalty hC
    _ = Erdos1027.DGKFixedEdge.invTwoPow edge.card * Real.exp M *
          expectedPenaltyBound := by rfl

end Erdos1027.DGKFiber
