/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InitialErdosSymmetry
import ErdosProblems.Erdos207.BoundedSpanVertexRootCount

/-! # Normalizing the exact full-family rooted degree for initial trajectories -/

namespace Erdos207

open Finset

noncomputable section

def fullErdosRootDegree (V : Type*) [Fintype V] [DecidableEq V] (r : ℕ) : ℝ :=
  ((r - 2 : ℕ) : ℝ) * (fullPackingErdosFamily V r).card / Fintype.card (TripleOn V)

def initialErdosTrajectoryCoefficient (V : Type*) [Fintype V] [DecidableEq V] (A : ℝ) (d : ℕ) : ℝ :=
  fullErdosRootDegree V (d + 3) / A ^ d

theorem fullErdosRootDegree_eq_root_card
    {V : Type*} [Fintype V] [DecidableEq V] (r : ℕ) (T : TripleOn V) :
    fullErdosRootDegree V r = ((rootedFullPackingErdosFamily r T).card : ℝ) := by
  have hpos : 0 < Fintype.card (TripleOn V) := Fintype.card_pos_iff.mpr ⟨T⟩
  have hposR : (0 : ℝ) < Fintype.card (TripleOn V) := by exact_mod_cast hpos
  have hinc : (Fintype.card (TripleOn V) : ℝ) * (rootedFullPackingErdosFamily r T).card =
      ((r - 2 : ℕ) : ℝ) * (fullPackingErdosFamily V r).card := by
    exact_mod_cast fullPackingErdosFamily_root_incidence r T
  unfold fullErdosRootDegree
  apply (div_eq_iff hposR.ne').mpr
  linarith only [hinc]

theorem initialErdosTrajectoryCoefficient_nonneg
    (V : Type*) [Fintype V] [DecidableEq V] (A : ℝ) (hA : 0 ≤ A) (d : ℕ) :
    0 ≤ initialErdosTrajectoryCoefficient V A d := by
  unfold initialErdosTrajectoryCoefficient fullErdosRootDegree
  positivity

theorem initialErdosTrajectoryCoefficient_target
    {V : Type*} [Fintype V] [DecidableEq V] (A : ℝ) (hA : 0 < A) (j : ℕ) (hj : 3 ≤ j)
    (T : TripleOn V) :
    initialErdosTrajectoryCoefficient V A (j - 3) * A ^ (j - 3) =
      ((rootedFullPackingErdosFamily j T).card : ℝ) := by
  unfold initialErdosTrajectoryCoefficient
  rw [div_mul_cancel₀ _ (pow_ne_zero _ hA.ne'), Nat.sub_add_cancel hj]
  exact fullErdosRootDegree_eq_root_card j T

theorem card_rootedFullPackingErdosFamily_le_span_power
    {V : Type*} [Fintype V] [DecidableEq V] (j : ℕ) (T : TripleOn V) :
    (rootedFullPackingErdosFamily j T).card ≤
      (2 ^ (j ^ 3) * (j + 1)) * (Fintype.card V + 1) ^ (j - 3) := by
  have hbound := card_boundedSpan_family_with_vertex_root (rootedFullPackingErdosFamily j T) T.1 j
    (fun C hC x hx ↦ mem_biUnion.mpr ⟨T, ((mem_rootedFullPackingErdosFamily j T C).mp hC).2.2, hx⟩)
    (fun C hC ↦ ((mem_rootedFullPackingErdosFamily j T C).mp hC).1.1.2)
  simpa only [T.2] using hbound

end

end Erdos207
