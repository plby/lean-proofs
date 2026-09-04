/-
Copyright (c) 2026 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Mathlib

/-!
# Unit-distance counting

The unit-distance pair count for finite planar sets, the ordered variant
for subsets of `ℂ`, and transport along the isometry `ℂ ≃ ℝ²`.
-/

open scoped Classical

namespace Erdos

/-! ## Unit-distance counting -/

/-- For a finite planar set `P ⊆ ℝ²`, `unitDist P` is the number of
unordered pairs `{x, y} ⊆ P` at Euclidean distance exactly `1`.
(Identical to the definition in the lean-eval problem
`erdos_unit_distance_conjecture_false`.) -/
noncomputable def unitDist (P : Finset (EuclideanSpace ℝ (Fin 2))) : ℕ :=
  (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card / 2

/-- The number of *ordered* pairs of distinct points of `P ⊆ ℂ` at
distance exactly `1`.  The geometric core produces planar sets inside `ℂ`;
`exists_euclidean_copy` transports the count to `EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def unitPairsC (P : Finset ℂ) : ℕ :=
  (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card

/-- [easy] The unit-distance pair count is exactly half the ordered count:
the involution `(x, y) ↦ (y, x)` of `P.offDiag` preserves the distance-one
filter and has no fixed points, so the filtered set has even cardinality.
Sketch: `Finset.card_div_two_eq...`; or directly exhibit the filtered set as
a disjoint union over the swap involution. -/
theorem two_mul_unitDist (P : Finset (EuclideanSpace ℝ (Fin 2))) :
    2 * unitDist P = (P.offDiag.filter (fun pq => dist pq.1 pq.2 = 1)).card := by
  rw [ unitDist, Nat.mul_div_cancel' ];
  -- Since `unitPairsC P` counts the number of ordered pairs `(x, y)` with `x ≠ y` and `dist x y = 1`, we can pair each such pair with `(y, x)`.
  have h_pair : ∃ S : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)), {pq ∈ P.offDiag | dist pq.1 pq.2 = 1} = S ∪ S.image Prod.swap ∧ Disjoint S (S.image Prod.swap) := by
    refine' ⟨ Finset.filter ( fun pq => pq.1 0 < pq.2 0 ∨ pq.1 0 = pq.2 0 ∧ pq.1 1 < pq.2 1 ) ( Finset.filter ( fun pq => dist pq.1 pq.2 = 1 ) ( P.offDiag ) ), _, _ ⟩;
    · ext ⟨ x, y ⟩ ; simp +decide [ dist_comm ] ;
      cases lt_trichotomy ( x 0 ) ( y 0 ) <;> cases lt_trichotomy ( x 1 ) ( y 1 ) <;> simp_all +decide [ dist_eq_norm, EuclideanSpace.norm_eq ];
      · aesop;
      · aesop;
      · grind +revert;
      · grind;
    · norm_num [ Finset.disjoint_right ];
      grind;
  obtain ⟨ S, hS₁, hS₂ ⟩ := h_pair; rw [ hS₁, Finset.card_union_of_disjoint hS₂, Finset.card_image_of_injective _ Prod.swap_injective ] ; simp +decide [ ← two_mul ] ;

/-- The standard real-linear isometry `ℂ ≃ EuclideanSpace ℝ (Fin 2)`. -/
noncomputable def complexToPlane : ℂ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  Complex.orthonormalBasisOneI.repr

/-- [easy] Transport a finite point set from `ℂ` to the Euclidean plane,
preserving cardinality and the (ordered) unit-distance count.
Sketch: take `Q = P.image complexToPlane`; the image is injective and
`complexToPlane` preserves distances, so the two filtered sets biject;
conclude with `two_mul_unitDist`. -/
theorem exists_euclidean_copy (P : Finset ℂ) :
    ∃ Q : Finset (EuclideanSpace ℝ (Fin 2)),
      Q.card = P.card ∧ 2 * unitDist Q = unitPairsC P := by
  let Q := Finset.image (fun z => complexToPlane z) P
  refine ⟨Q, Finset.card_image_of_injective _ complexToPlane.injective, ?_⟩
  rw [two_mul_unitDist]
  unfold unitPairsC
  apply Finset.card_bij
      (fun pq _ => (complexToPlane.symm pq.1, complexToPlane.symm pq.2))
  · rintro ⟨a, b⟩ hab
    simp only [Finset.mem_filter, Finset.mem_offDiag, Q, Finset.mem_image] at hab ⊢
    rcases hab with ⟨⟨⟨x, hx, rfl⟩, ⟨y, hy, rfl⟩, hxy⟩, hdist⟩
    have hne : x ≠ y := fun h => hxy (congrArg complexToPlane h)
    simpa using (show (x ∈ P ∧ y ∈ P ∧ x ≠ y) ∧ dist x y = 1 from
      ⟨⟨hx, hy, hne⟩, by simpa using hdist⟩)
  · rintro ⟨a, b⟩ hab ⟨c, d⟩ hcd h
    simp only [Prod.mk.injEq] at h ⊢
    exact ⟨complexToPlane.symm.injective h.1, complexToPlane.symm.injective h.2⟩
  · rintro ⟨x, y⟩ hxy
    refine ⟨(complexToPlane x, complexToPlane y), ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_offDiag, Q, Finset.mem_image] at hxy ⊢
      exact ⟨⟨⟨x, hxy.1.1, rfl⟩, ⟨y, hxy.1.2.1, rfl⟩,
        fun h => hxy.1.2.2 (complexToPlane.injective h)⟩, by simpa using hxy.2⟩
    · simp

end Erdos
