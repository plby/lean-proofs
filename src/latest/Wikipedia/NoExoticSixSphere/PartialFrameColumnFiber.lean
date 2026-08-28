import Wikipedia.NoExoticSixSphere.PartialFrames
import Wikipedia.NoExoticSixSphere.RectangularColumnBlock
import Wikipedia.NoExoticSixSphere.ColumnFiber

/-!
# The actual fiber of a partial-frame column projection

Splitting the source and target along the specified unit vectors identifies
frames carrying one to the other with partial frames in the two orthogonal
complements. Extraction and reinsertion are continuous inverse operator maps.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.ColumnFiber

open GLOrthonormalization ColumnCoordinates FixedColumnBlock

variable {n r : ℕ}

local instance sourceDimension : Fact (Module.finrank ℝ (Vector (r + 1)) = r + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance targetDimension : Fact (Module.finrank ℝ (Vector (n + 1)) = n + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable (v : UnitSphere (Vector (r + 1))) (c : UnitSphere (Vector (n + 1)))

def adapted (a : Stiefel.Space (n + 1) (r + 1)) :
    FixedColumnBlock.Space (Vector r) →ₗᵢ[ℝ] FixedColumnBlock.Space (Vector n) :=
  (split c).toLinearIsometry.comp ((toIsometry a).comp (split v).symm.toLinearIsometry)

theorem adapted_apply (a : Stiefel.Space (n + 1) (r + 1)) (z : FixedColumnBlock.Space (Vector r)) :
    adapted v c a z = split c (a.val ((split v).symm z)) := rfl

theorem adapted_operator (a : Stiefel.Space (n + 1) (r + 1)) :
    (adapted v c a).toContinuousLinearMap =
      (split c).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (a.val.comp (split v).symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro z
  rfl

theorem adapted_fixes (a : Stiefel.Space (n + 1) (r + 1))
    (ha : a.val v.val = c.val) : adapted v c a firstVector = firstVector := by
  rw [adapted_apply, NoExoticSixSphere.ColumnFiber.split_symm_firstVector, ha]
  exact split_self c

def residual (a : Stiefel.Space (n + 1) (r + 1)) (ha : a.val v.val = c.val) :
    Stiefel.Space n r :=
  ofIsometry (RectangularColumnBlock.tailIsometry (adapted v c a) (adapted_fixes v c a ha))

theorem residual_operator (a : Stiefel.Space (n + 1) (r + 1)) (ha : a.val v.val = c.val) :
    (residual v c a ha).val = RectangularColumnBlock.tailMap (adapted v c a) := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

def reconstruct (q : Stiefel.Space n r) : Stiefel.Space (n + 1) (r + 1) :=
  ofIsometry ((split c).symm.toLinearIsometry.comp
    ((RectangularColumnBlock.block (toIsometry q)).comp (split v).toLinearIsometry))

theorem reconstruct_apply (q : Stiefel.Space n r) (x : Vector (r + 1)) :
    (reconstruct v c q).val x =
      (split c).symm (RectangularColumnBlock.block (toIsometry q) (split v x)) := rfl

theorem reconstruct_operator (q : Stiefel.Space n r) :
    (reconstruct v c q).val =
      (split c).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((RectangularColumnBlock.block (toIsometry q)).toContinuousLinearMap.comp
          (split v).toContinuousLinearEquiv.toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

theorem reconstruct_column (q : Stiefel.Space n r) :
    (reconstruct v c q).val v.val = c.val := by
  rw [reconstruct_apply, split_self]
  change (split c).symm (RectangularColumnBlock.block (toIsometry q) firstVector) = c.val
  rw [RectangularColumnBlock.block_firstVector,
    NoExoticSixSphere.ColumnFiber.split_symm_firstVector]

theorem toIsometry_residual (a : Stiefel.Space (n + 1) (r + 1)) (ha : a.val v.val = c.val) :
    toIsometry (residual v c a ha) =
      RectangularColumnBlock.tailIsometry (adapted v c a) (adapted_fixes v c a ha) := by
  apply LinearIsometry.ext
  intro x
  rfl

theorem reconstruct_residual (a : Stiefel.Space (n + 1) (r + 1)) (ha : a.val v.val = c.val) :
    reconstruct v c (residual v c a ha) = a := by
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro x
  rw [reconstruct_apply, toIsometry_residual,
    ← RectangularColumnBlock.isometry_eq_block (adapted v c a) (adapted_fixes v c a ha),
    adapted_apply, LinearIsometryEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply]

theorem adapted_reconstruct (q : Stiefel.Space n r) :
    adapted v c (reconstruct v c q) = RectangularColumnBlock.block (toIsometry q) := by
  apply LinearIsometry.ext
  intro z
  rw [adapted_apply, reconstruct_apply, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply]

theorem residual_reconstruct (q : Stiefel.Space n r) :
    residual v c (reconstruct v c q) (reconstruct_column v c q) = q := by
  apply Subtype.ext
  rw [residual_operator, adapted_reconstruct, RectangularColumnBlock.tailMap_block]
  rfl

variable {X : Type*} [TopologicalSpace X]

theorem continuous_adapted (a : X → Stiefel.Space (n + 1) (r + 1)) (ha : Continuous a) :
    Continuous (fun x ↦ (adapted v c (a x)).toContinuousLinearMap) := by
  simp_rw [adapted_operator]
  exact continuous_const.clm_comp ((continuous_subtype_val.comp ha).clm_comp continuous_const)

theorem continuous_residual (a : X → Stiefel.Space (n + 1) (r + 1)) (ha : Continuous a)
    (hcol : ∀ x, (a x).val v.val = c.val) :
    Continuous (fun x ↦ residual v c (a x) (hcol x)) := by
  have htail := RectangularColumnBlock.continuous_tailMap (fun x ↦ adapted v c (a x))
    (continuous_adapted v c a ha)
  exact htail.subtype_mk _

theorem continuous_reconstruct (a : X → Stiefel.Space n r) (ha : Continuous a) :
    Continuous (fun x ↦ reconstruct v c (a x)) := by
  have hblock := RectangularColumnBlock.continuous_block (fun x ↦ toIsometry (a x))
    (show Continuous (fun x ↦ (toIsometry (a x)).toContinuousLinearMap) from
      continuous_subtype_val.comp ha)
  have hr : Continuous (fun x ↦ (reconstruct v c (a x)).val) := by
    simp_rw [reconstruct_operator]
    exact continuous_const.clm_comp (hblock.clm_comp continuous_const)
  exact hr.subtype_mk _

def reconstructionMap : C(Stiefel.Space n r, Stiefel.Space (n + 1) (r + 1)) :=
  ⟨reconstruct v c, continuous_reconstruct v c id continuous_id⟩

abbrev Fiber := {a : Stiefel.Space (n + 1) (r + 1) // a.val v.val = c.val}

def homeomorph : Fiber v c ≃ₜ Stiefel.Space n r where
  toFun a := residual v c a.val a.property
  invFun q := ⟨reconstruct v c q, reconstruct_column v c q⟩
  left_inv a := Subtype.ext (reconstruct_residual v c a.val a.property)
  right_inv := residual_reconstruct v c
  continuous_toFun := continuous_residual v c Subtype.val continuous_subtype_val Subtype.property
  continuous_invFun := (continuous_reconstruct v c id continuous_id).subtype_mk _

end NoExoticSixSphere.Stiefel.ColumnFiber
