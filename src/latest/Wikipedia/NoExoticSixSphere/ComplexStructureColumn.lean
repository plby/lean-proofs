import Wikipedia.NoExoticSixSphere.ComplexStructureConjugation
import Wikipedia.NoExoticSixSphere.OrthogonalStabilization

/-!
# The sphere-valued column of an orthogonal complex structure

For a fixed unit vector `v`, the vector `J v` is unit and perpendicular to `v`.
Coordinates on that perpendicular space give the actual sphere-valued column
map. Conjugation by an orthogonal operator fixing `v` acts on this column by
its lower-rank orthogonal block.
-/

namespace NoExoticSixSphere.OrthogonalComplexStructures

open GLOrthonormalization OrthogonalPaths CayleyTransform ColumnCoordinates

variable {n : ℕ}

local instance dimensionFact : Fact (Module.finrank ℝ (Vector (n + 2)) = (n + 1) + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

theorem apply_mem_complement (J : Space (n + 2)) (v : UnitSphere (Vector (n + 2))) :
    J.1.1 (v : Vector (n + 2)) ∈ (ℝ ∙ (v : Vector (n + 2)))ᗮ :=
  Submodule.mem_orthogonal_singleton_iff_inner_right.mpr (inner_skew_self J.1 v)

noncomputable def column (v : UnitSphere (Vector (n + 2)))
    (J : Space (n + 2)) : Sphere n :=
  ⟨complement (r := n + 1) v ⟨J.1.1 v, apply_mem_complement J v⟩, by
    rw [Metric.mem_sphere, dist_zero_right, LinearIsometryEquiv.norm_map]
    exact (norm_apply J v).trans (ClosedHemisphere.unit_norm v)⟩

theorem split_column (v : UnitSphere (Vector (n + 2))) (J : Space (n + 2)) :
    split (r := n + 1) v (J.1.1 v) =
      WithLp.toLp 2 ((0 : ℝ), (column v J : Vector (n + 1))) := by
  apply (split (r := n + 1) v).symm.injective
  rw [LinearIsometryEquiv.symm_apply_apply, split_symm_apply]
  change J.1.1 v = (0 : ℝ) • (v : Vector (n + 2)) +
    ((complement v).symm (complement v ⟨J.1.1 v, apply_mem_complement J v⟩) : Vector (n + 2))
  rw [LinearIsometryEquiv.symm_apply_apply, zero_smul, zero_add]

theorem column_conjugate (v : UnitSphere (Vector (n + 2)))
    (q : OrthogonalOperators (n + 1)) (J : Space (n + 2)) :
    (column v (conjugate (ColumnFiber.reconstruct v v q) J) : Vector (n + 1)) =
      q.1.1 (column v J : Vector (n + 1)) := by
  have h : split (r := n + 1) v ((conjugate (ColumnFiber.reconstruct v v q) J).1.1 v) =
      FixedColumnBlock.block (toEquiv q) (split (r := n + 1) v (J.1.1 v)) := by
    rw [conjugate_column _ _ _ (ColumnFiber.reconstruct_column v v q),
      ColumnFiber.reconstruct_apply, LinearIsometryEquiv.apply_symm_apply]
  rw [split_column, split_column] at h
  exact congrArg (fun z : WithLp 2 (ℝ × Vector (n + 1)) ↦ z.snd) h

theorem continuous_column (v : UnitSphere (Vector (n + 2))) :
    Continuous (column v) := by
  have hJ : Continuous (fun J : Space (n + 2) ↦ J.1.1 (v : Vector (n + 2))) :=
    (continuous_subtype_val.comp continuous_subtype_val).clm_apply continuous_const
  exact ((complement v).continuous.comp (hJ.subtype_mk _)).subtype_mk _

noncomputable def columnMap (v : UnitSphere (Vector (n + 2))) :
    C(Space (n + 2), Sphere n) := ⟨column v, continuous_column v⟩

end NoExoticSixSphere.OrthogonalComplexStructures
