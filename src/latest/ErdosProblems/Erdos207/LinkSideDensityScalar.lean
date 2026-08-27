/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RobustHallSamplingScalarGood

/-!
# Link-side lower bounds and the candidate-density scalar
-/

namespace Erdos207

open Finset

noncomputable section

/-- A positive balanced link carrying minimum relation degree `d` has at
least `d` vertices on each side. -/
lemma HasLinkDegreeCodegreeBounds.d_le_right_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {available : TripleSystemOn V} {K : BipartiteLink V}
    {d D codegree : ℕ}
    (htyp : HasLinkDegreeCodegreeBounds available K d D codegree)
    (hbalanced : K.left.card = K.right.card)
    (hpositive : 0 < K.right.card) : d ≤ K.right.card := by
  have hleft : K.left.Nonempty := by
    apply card_pos.mp
    simpa only [hbalanced] using hpositive
  obtain ⟨a, ha⟩ := hleft
  let a' : ↥K.left := ⟨a, ha⟩
  have hmin := (htyp.1 a').1
  exact hmin.trans <| by
    calc
      (relationNeighborsIn (linkAvailableRelation K available) univ a').card ≤
          (univ : Finset ↥K.right).card :=
        card_le_card (filter_subset _ _)
      _ = K.right.card := by simp

/-- If a positive link has minimum degree at least two, the factor `3`
absorbs the floor in `M / 2`. -/
lemma HasLinkDegreeCodegreeBounds.candidate_density_scalar_of_three
    {V : Type*} [Fintype V] [DecidableEq V]
    {available : TripleSystemOn V} {K : BipartiteLink V}
    {d D codegree candidate density : ℕ}
    (htyp : HasLinkDegreeCodegreeBounds available K d D codegree)
    (hbalanced : K.left.card = K.right.card)
    (hpositive : 0 < K.right.card) (hd : 2 ≤ d)
    (hscalar : 3 * candidate ≤ density) :
    K.right.card * candidate ≤ density * (K.right.card / 2) := by
  have hM2 : 2 ≤ K.right.card :=
    hd.trans (htyp.d_le_right_card hbalanced hpositive)
  have hfloor : K.right.card ≤ 3 * (K.right.card / 2) := by omega
  calc
    K.right.card * candidate ≤
        (3 * (K.right.card / 2)) * candidate :=
      Nat.mul_le_mul_right candidate hfloor
    _ = (3 * candidate) * (K.right.card / 2) := by ring
    _ ≤ density * (K.right.card / 2) :=
      Nat.mul_le_mul_right (K.right.card / 2) hscalar

end

end Erdos207
