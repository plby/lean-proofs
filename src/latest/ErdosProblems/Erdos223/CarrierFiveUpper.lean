/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos223.Space
import ErdosProblems.Erdos223.LocalSphere
import ErdosProblems.Erdos223.CarrierFiveCross
import ErdosProblems.Erdos223.CarrierFiveCoreCompletion
import ErdosProblems.Erdos223.FiveWeakOptimization

/-!
# Unconditional local upper bounds for five-dimensional carriers

This module connects Vázsonyi's now-formalized three-dimensional theorem to
the rank-three spheres of a faithful shifted five-dimensional weak carrier.
-/

open scoped EuclideanGeometry RealInnerProductSpace

namespace Erdos223

noncomputable section

/-- Vázsonyi's additive bound transported to a nonempty rank-three spherical
block which inherits the diameter-at-most-one condition from a larger set. -/
theorem diameterPairCount_add_two_le_of_mem_sphere_in_finrank_three
    {d : ℕ} {A : Finset (Point d)} {c : Point d} {r : ℝ}
    (U : Submodule ℝ (Point d)) (hfin : Module.finrank ℝ U = 3)
    (hU : ∀ x ∈ A, x - c ∈ U)
    (hsphere : LocalSphere.IsOnSphere A c r)
    (hne : A.Nonempty)
    (hdist : ∀ x ∈ A, ∀ y ∈ A, dist x y ≤ 1) :
    diameterPairCount A + 2 ≤ 2 * A.card := by
  by_cases hz : diameterPairCount A = 0
  · rw [hz, zero_add]
    have hcard : 1 ≤ A.card := Finset.one_le_card.mpr hne
    omega
  · obtain ⟨B, hcard, _hsphereB, hcount, hdiam⟩ :=
      LocalSphere.exists_pointThree_model_of_mem_sphere_in_finrank_three
        U hfin hU hsphere
    have hA : IsDiameterOne A :=
      LocalSphere.isDiameterOne_of_diameterPairCount_pos_of_dist_le hdist
        (Nat.pos_of_ne_zero hz)
    have hB : IsDiameterOne B := hdiam.mpr hA
    have hv := diameterPairCount_add_two_le B hB
    omega

namespace FiveWeakCarrier.Carrier

variable (C : FiveWeakCarrier.Carrier)

private theorem secondPlane_orthogonal_finrank_upper :
    Module.finrank ℝ C.secondPlane.directionᗮ = 3 := by
  have h := C.secondPlane.direction.finrank_add_finrank_orthogonal
  rw [C.second_finrank] at h
  have hambient : Module.finrank ℝ (Point 5) = 5 := by simp
  rw [hambient] at h
  omega

private theorem firstPlane_orthogonal_finrank_upper :
    Module.finrank ℝ C.firstPlane.directionᗮ = 3 := by
  have h := C.firstPlane.direction.finrank_add_finrank_orthogonal
  rw [C.first_finrank] at h
  have hambient : Module.finrank ℝ (Point 5) = 5 := by simp
  rw [hambient] at h
  omega

/-- Unconditional additive Vázsonyi bound on a nonempty first crossed-sphere
block. -/
theorem firstSphere_add_two_le
    {S : Finset (Point 5)} (hS : ∀ x ∈ S, x ∈ C.firstSphere)
    (hne : S.Nonempty)
    (hdist : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1) :
    diameterPairCount S + 2 ≤ 2 * S.card := by
  apply diameterPairCount_add_two_le_of_mem_sphere_in_finrank_three
    C.secondPlane.directionᗮ C.secondPlane_orthogonal_finrank_upper
  · intro x hx
    exact (C.mem_firstSphere.mp (hS x hx)).1
  · intro x hx
    exact (C.mem_firstSphere.mp (hS x hx)).2
  · exact hne
  · exact hdist

/-- Symmetric additive bound on a nonempty second crossed-sphere block. -/
theorem secondSphere_add_two_le
    {S : Finset (Point 5)} (hS : ∀ x ∈ S, x ∈ C.secondSphere)
    (hne : S.Nonempty)
    (hdist : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1) :
    diameterPairCount S + 2 ≤ 2 * S.card := by
  apply diameterPairCount_add_two_le_of_mem_sphere_in_finrank_three
    C.firstPlane.directionᗮ C.firstPlane_orthogonal_finrank_upper
  · intro x hx
    exact (C.mem_secondSphere.mp (hS x hx)).1
  · intro x hx
    exact (C.mem_secondSphere.mp (hS x hx)).2
  · exact hne
  · exact hdist

/-- The first-sphere/second-circle strong orientation satisfies the exact
dimension-five upper bound. -/
theorem firstSphere_secondCircle_upper
    {S T : Finset (Point 5)}
    (hS : ∀ x ∈ S, x ∈ C.firstSphere)
    (hT : ∀ y ∈ T, y ∈ C.secondCircle)
    (hSne : S.Nonempty)
    (hdistS : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1)
    (hdistT : ∀ x ∈ T, ∀ y ∈ T, dist x y ≤ 1) :
    S.card * T.card + diameterPairCount S + diameterPairCount T ≤
      turanNumber 2 (S.card + T.card) + (S.card + T.card) := by
  apply LocalSphere.fiveWeakCarrier_firstSphere_secondCircle_upper C
    hS hT hdistS hdistT
  intro _hr
  exact C.firstSphere_add_two_le hS hSne hdistS

/-- Finset-union form of the first strong orientation bound. -/
theorem diameterPairCount_union_firstSphere_secondCircle_le
    {S T : Finset (Point 5)} (hdisj : Disjoint S T)
    (hS : ∀ x ∈ S, x ∈ C.firstSphere)
    (hT : ∀ y ∈ T, y ∈ C.secondCircle)
    (hSne : S.Nonempty)
    (hdistS : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1)
    (hdistT : ∀ x ∈ T, ∀ y ∈ T, dist x y ≤ 1) :
    diameterPairCount (S ∪ T) ≤
      turanNumber 2 (S ∪ T).card + (S ∪ T).card := by
  rw [diameterPairCount_union_of_disjoint S T hdisj,
    Finset.card_union_of_disjoint hdisj]
  have hcross :
      ((S.product T).filter fun e => dist e.1 e.2 = 1).card =
        S.card * T.card := by
    rw [← Finset.card_product]
    congr 1
    ext e
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨he, _⟩
      exact he
    · intro he
      have he' := Finset.mem_product.mp he
      exact ⟨he, C.dist_eq_one_of_mem_firstSphere_mem_secondCircle
        (hS e.1 he'.1) (hT e.2 he'.2)⟩
  rw [hcross]
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    C.firstSphere_secondCircle_upper hS hT hSne hdistS hdistT

/-- Symmetric strong orientation endpoint. -/
theorem firstCircle_secondSphere_upper
    {T S : Finset (Point 5)}
    (hT : ∀ x ∈ T, x ∈ C.firstCircle)
    (hS : ∀ y ∈ S, y ∈ C.secondSphere)
    (hSne : S.Nonempty)
    (hdistT : ∀ x ∈ T, ∀ y ∈ T, dist x y ≤ 1)
    (hdistS : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1) :
    T.card * S.card + diameterPairCount T + diameterPairCount S ≤
      turanNumber 2 (T.card + S.card) + (T.card + S.card) := by
  apply LocalSphere.fiveWeakCarrier_firstCircle_secondSphere_upper C
    hT hS hdistT hdistS
  intro _hr
  exact C.secondSphere_add_two_le hS hSne hdistS

/-- Finset-union form of the symmetric strong orientation bound. -/
theorem diameterPairCount_union_firstCircle_secondSphere_le
    {T S : Finset (Point 5)} (hdisj : Disjoint T S)
    (hT : ∀ x ∈ T, x ∈ C.firstCircle)
    (hS : ∀ y ∈ S, y ∈ C.secondSphere)
    (hSne : S.Nonempty)
    (hdistT : ∀ x ∈ T, ∀ y ∈ T, dist x y ≤ 1)
    (hdistS : ∀ x ∈ S, ∀ y ∈ S, dist x y ≤ 1) :
    diameterPairCount (T ∪ S) ≤
      turanNumber 2 (T ∪ S).card + (T ∪ S).card := by
  rw [diameterPairCount_union_of_disjoint T S hdisj,
    Finset.card_union_of_disjoint hdisj]
  have hcross :
      ((T.product S).filter fun e => dist e.1 e.2 = 1).card =
        T.card * S.card := by
    rw [← Finset.card_product]
    congr 1
    ext e
    rw [Finset.mem_filter]
    constructor
    · rintro ⟨he, _⟩
      exact he
    · intro he
      have he' := Finset.mem_product.mp he
      exact ⟨he, C.dist_eq_one_of_mem_firstCircle_mem_secondSphere
        (hT e.1 he'.1) (hS e.2 he'.2)⟩
  rw [hcross]
  simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
    C.firstCircle_secondSphere_upper hT hS hSne hdistT hdistS

end FiveWeakCarrier.Carrier

end

end Erdos223
