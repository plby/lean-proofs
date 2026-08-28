import Wikipedia.NoExoticSixSphere.FixedColumnBlock
import Wikipedia.NoExoticSixSphere.OrthogonalPaths

/-!
# The actual fiber of an orthogonal column

For two fixed unit vectors `v` and `c`, orthogonal operators carrying `v` to
`c` are identified with orthogonal operators on a space of one lower dimension.
The constructions use actual orthogonal coordinates and mutually inverse
operator maps; continuity is for the operator-norm subspace topology.
-/

namespace NoExoticSixSphere

open GLOrthonormalization

namespace OrthogonalPaths

variable {n : ℕ}

/-- Recover the linear isometry equivalence underlying an orthogonal operator. -/
noncomputable def toEquiv (a : OrthogonalOperators n) : Vector n ≃ₗᵢ[ℝ] Vector n where
  toLinearEquiv := (invertibleOperatorEquiv a.1.1 a.1.2).toLinearEquiv
  norm_map' := a.2

theorem toEquiv_apply (a : OrthogonalOperators n) (w : Vector n) :
    toEquiv a w = a.1.1 w := rfl

theorem toEquiv_operator (a : OrthogonalOperators n) :
    (toEquiv a).toContinuousLinearEquiv.toContinuousLinearMap = a.1.1 := by
  apply ContinuousLinearMap.ext
  intro w
  rfl

theorem ofEquiv_toEquiv (a : OrthogonalOperators n) : ofEquiv (toEquiv a) = a := by
  apply Subtype.ext
  apply Subtype.ext
  exact toEquiv_operator a

end OrthogonalPaths

namespace ColumnFiber

open OrthogonalPaths ColumnCoordinates FixedColumnBlock

variable {r : ℕ}

local instance dimensionFact : Fact (Module.finrank ℝ (Vector (r + 1)) = r + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable (v c : UnitSphere (Vector (r + 1)))

theorem split_symm_firstVector :
    (split (r := r) v).symm (firstVector : Space (Vector r)) = (v : Vector (r + 1)) := by
  apply (split (r := r) v).injective
  rw [LinearIsometryEquiv.apply_symm_apply]
  exact (split_self v).symm

/-- Express the source and target in coordinates adapted to the two columns. -/
noncomputable def adapted (a : OrthogonalOperators (r + 1)) :
    Space (Vector r) ≃ₗᵢ[ℝ] Space (Vector r) :=
  ((split v).symm.trans (toEquiv a)).trans (split c)

theorem adapted_apply (a : OrthogonalOperators (r + 1)) (z : Space (Vector r)) :
    adapted v c a z = split c (a.1.1 ((split v).symm z)) := rfl

theorem adapted_operator (a : OrthogonalOperators (r + 1)) :
    (adapted v c a).toContinuousLinearEquiv.toContinuousLinearMap =
      (split c).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (a.1.1.comp (split v).symm.toContinuousLinearEquiv.toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro z
  rfl

theorem adapted_fixes (a : OrthogonalOperators (r + 1))
    (ha : a.1.1 (v : Vector (r + 1)) = (c : Vector (r + 1))) :
    adapted v c a firstVector = firstVector := by
  rw [adapted_apply, split_symm_firstVector, ha]
  exact split_self c

/-- The residual orthogonal operator on the complements of the fixed columns. -/
noncomputable def residual (a : OrthogonalOperators (r + 1))
    (ha : a.1.1 (v : Vector (r + 1)) = (c : Vector (r + 1))) : OrthogonalOperators r :=
  ofEquiv (tailEquiv (adapted v c a) (adapted_fixes v c a ha))

theorem residual_operator (a : OrthogonalOperators (r + 1))
    (ha : a.1.1 (v : Vector (r + 1)) = (c : Vector (r + 1))) :
    (residual v c a ha).1.1 = tailMap (adapted v c a) := by
  apply ContinuousLinearMap.ext
  intro w
  rfl

/-- Reinsert an orthogonal complement operator and return to ambient coordinates. -/
noncomputable def reconstruct (q : OrthogonalOperators r) : OrthogonalOperators (r + 1) :=
  ofEquiv (((split v).trans (block (toEquiv q))).trans (split c).symm)

theorem reconstruct_apply (q : OrthogonalOperators r) (w : Vector (r + 1)) :
    (reconstruct v c q).1.1 w = (split c).symm (block (toEquiv q) (split v w)) := rfl

theorem reconstruct_operator (q : OrthogonalOperators r) :
    (reconstruct v c q).1.1 =
      (split c).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((block (toEquiv q)).toContinuousLinearEquiv.toContinuousLinearMap.comp
          (split v).toContinuousLinearEquiv.toContinuousLinearMap) := by
  apply ContinuousLinearMap.ext
  intro w
  rfl

theorem reconstruct_column (q : OrthogonalOperators r) :
    (reconstruct v c q).1.1 (v : Vector (r + 1)) = (c : Vector (r + 1)) := by
  rw [reconstruct_apply, split_self]
  change (split c).symm (block (toEquiv q) firstVector) = _
  rw [block_firstVector, split_symm_firstVector]

theorem toEquiv_residual (a : OrthogonalOperators (r + 1))
    (ha : a.1.1 (v : Vector (r + 1)) = (c : Vector (r + 1))) :
    toEquiv (residual v c a ha) = tailEquiv (adapted v c a) (adapted_fixes v c a ha) := by
  apply LinearIsometryEquiv.ext
  intro w
  rfl

theorem reconstruct_residual (a : OrthogonalOperators (r + 1))
    (ha : a.1.1 (v : Vector (r + 1)) = (c : Vector (r + 1))) :
    reconstruct v c (residual v c a ha) = a := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro w
  rw [reconstruct_apply, toEquiv_residual, ← equiv_eq_block]
  rw [adapted_apply, LinearIsometryEquiv.symm_apply_apply,
    LinearIsometryEquiv.symm_apply_apply]

theorem adapted_reconstruct (q : OrthogonalOperators r) :
    adapted v c (reconstruct v c q) = block (toEquiv q) := by
  apply LinearIsometryEquiv.ext
  intro z
  rw [adapted_apply, reconstruct_apply, LinearIsometryEquiv.apply_symm_apply,
    LinearIsometryEquiv.apply_symm_apply]

theorem residual_reconstruct (q : OrthogonalOperators r) :
    residual v c (reconstruct v c q) (reconstruct_column v c q) = q := by
  apply Subtype.ext
  apply Subtype.ext
  rw [residual_operator, adapted_reconstruct, tailMap_block, toEquiv_operator]

variable {X : Type*} [TopologicalSpace X]

theorem continuous_adapted (a : X → OrthogonalOperators (r + 1)) (ha : Continuous a) :
    Continuous (fun x ↦ (adapted v c (a x)).toContinuousLinearEquiv.toContinuousLinearMap) := by
  simp_rw [adapted_operator]
  have hA := continuous_subtype_val.comp (continuous_subtype_val.comp ha)
  exact continuous_const.clm_comp (hA.clm_comp continuous_const)

theorem continuous_residual (a : X → OrthogonalOperators (r + 1)) (ha : Continuous a)
    (hcol : ∀ x, (a x).1.1 (v : Vector (r + 1)) = (c : Vector (r + 1))) :
    Continuous (fun x ↦ residual v c (a x) (hcol x)) := by
  have htail := continuous_tailMap (adapted v c ∘ a) (continuous_adapted v c a ha)
  exact (htail.subtype_mk _).subtype_mk _

theorem continuous_reconstruct (a : X → OrthogonalOperators r) (ha : Continuous a) :
    Continuous (fun x ↦ reconstruct v c (a x)) := by
  have hA : Continuous (fun x ↦ (toEquiv (a x)).toContinuousLinearEquiv.toContinuousLinearMap) := by
    simp_rw [toEquiv_operator]
    exact continuous_subtype_val.comp (continuous_subtype_val.comp ha)
  have hblock := continuous_block (fun x ↦ toEquiv (a x)) hA
  have hrec : Continuous (fun x ↦ (reconstruct v c (a x)).1.1) := by
    simp_rw [reconstruct_operator]
    exact continuous_const.clm_comp (hblock.clm_comp continuous_const)
  exact (hrec.subtype_mk _).subtype_mk _

/-- The column fiber with its actual subspace topology. -/
abbrev Fiber := {a : OrthogonalOperators (r + 1) //
  a.1.1 (v : Vector (r + 1)) = (c : Vector (r + 1))}

/-- The genuine orthogonal column fiber is homeomorphic to the smaller orthogonal space. -/
noncomputable def homeomorph : Fiber v c ≃ₜ OrthogonalOperators r where
  toFun a := residual v c a.1 a.2
  invFun q := ⟨reconstruct v c q, reconstruct_column v c q⟩
  left_inv a := Subtype.ext (reconstruct_residual v c a.1 a.2)
  right_inv := residual_reconstruct v c
  continuous_toFun := continuous_residual v c Subtype.val continuous_subtype_val Subtype.property
  continuous_invFun := (continuous_reconstruct v c id continuous_id).subtype_mk _

end ColumnFiber

end NoExoticSixSphere
