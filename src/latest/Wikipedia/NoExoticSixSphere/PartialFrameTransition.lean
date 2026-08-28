import Wikipedia.NoExoticSixSphere.AntipodalColumnTransition

/-!
# Actual changes of partial-frame coordinates

These are the changes between the two proved column-bundle charts. Their
inverse identities and continuity on the overlap are proved directly. On
the equator the reconstructed transition has the explicit ambient reflection
formula on vectors orthogonal to the distinguished source column.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.ColumnBundle

open GLOrthonormalization Set

variable {n r : ℕ} (v : UnitSphere (Vector (r + 1)))
  (c d : UnitSphere (Vector (n + 1)))

def transition (x : UnitSphere (Vector (n + 1))) (q : Space n r) : Space n r :=
  (toCoordinates v c (fromCoordinates v d (x, q))).2

theorem fromCoordinates_transition (x : UnitSphere (Vector (n + 1))) (q : Space n r) :
    fromCoordinates v c (x, transition v c d x q) = fromCoordinates v d (x, q) := by
  have h : (x, transition v c d x q) = toCoordinates v c (fromCoordinates v d (x, q)) := by
    apply Prod.ext
    · exact (column_fromCoordinates v d (x, q)).symm
    · rfl
  rw [h, fromCoordinates_toCoordinates]

theorem transition_inverse (x : UnitSphere (Vector (n + 1))) (q : Space n r) :
    transition v d c x (transition v c d x q) = q := by
  change (toCoordinates v d (fromCoordinates v c (x, transition v c d x q))).2 = q
  rw [fromCoordinates_transition, toCoordinates_fromCoordinates]

theorem transition_self (x : UnitSphere (Vector (n + 1))) (q : Space n r) :
    transition v c c x q = q := by
  change (toCoordinates v c (fromCoordinates v c (x, q))).2 = q
  rw [toCoordinates_fromCoordinates]

theorem reconstruct_transition (x : UnitSphere (Vector (n + 1))) (q : Space n r) :
    ColumnFiber.reconstruct v c (transition v c d x q) =
      corrected v c (fromCoordinates v d (x, q)) :=
  ColumnFiber.reconstruct_residual v c _ (corrected_column v c (fromCoordinates v d (x, q)))

variable {X : Type*} [TopologicalSpace X]

theorem continuous_transition (p : X → UnitSphere (Vector (n + 1)) × Space n r)
    (hp : Continuous p) (hcol : ∀ y, (p y).1 ∈ baseSet c ∩ baseSet d) :
    Continuous (fun y ↦ transition v c d (p y).1 (p y).2) := by
  have hfrom := continuous_fromCoordinates v d p hp (fun y ↦ (hcol y).2)
  have hto := continuous_toCoordinates v c (fun y ↦ fromCoordinates v d (p y)) hfrom
    (fun y ↦ by rw [column_fromCoordinates]; exact (hcol y).1)
  exact hto.snd

def transitionHomeomorph (x : UnitSphere (Vector (n + 1)))
    (hx : x ∈ baseSet c ∩ baseSet d) : Space n r ≃ₜ Space n r where
  toFun := transition v c d x
  invFun := transition v d c x
  left_inv := transition_inverse v c d x
  right_inv := transition_inverse v d c x
  continuous_toFun := continuous_transition v c d (fun q ↦ (x, q))
    (continuous_const.prodMk continuous_id) (fun _ ↦ hx)
  continuous_invFun := continuous_transition v d c (fun q ↦ (x, q))
    (continuous_const.prodMk continuous_id) (fun _ ↦ ⟨hx.2, hx.1⟩)

theorem equatorial_reconstruct_transition (x : UnitSphere (Vector (n + 1)))
    (hcx : inner ℝ c.val x.val = 0) (q : Space n r) (z : Vector (r + 1))
    (hvz : inner ℝ v.val z = 0) :
    (ColumnFiber.reconstruct v c (transition v c (antipode c) x q)).val z =
      (ColumnFiber.reconstruct v (antipode c) q).val z -
        (2 * inner ℝ x.val ((ColumnFiber.reconstruct v (antipode c) q).val z)) • x.val := by
  rw [reconstruct_transition, corrected, column_fromCoordinates, fromCoordinates,
    action_apply, action_apply]
  apply AntipodalColumnTransition.operator_transition c x hcx
  have h := (toIsometry (ColumnFiber.reconstruct v (antipode c) q)).inner_map_map v.val z
  change inner ℝ ((ColumnFiber.reconstruct v (antipode c) q).val v.val)
    ((ColumnFiber.reconstruct v (antipode c) q).val z) = inner ℝ v.val z at h
  rw [ColumnFiber.reconstruct_column] at h
  change inner ℝ (-c.val) ((ColumnFiber.reconstruct v (antipode c) q).val z) =
    inner ℝ v.val z at h
  rw [inner_neg_left, hvz] at h
  exact neg_eq_zero.mp h

end NoExoticSixSphere.Stiefel.ColumnBundle
