import Wikipedia.NoExoticSixSphere.OrthogonalGroupOperations
import Wikipedia.NoExoticSixSphere.OrthogonalColumnHomotopy
import Mathlib.Topology.FiberBundle.Trivialization

/-!
# Local trivializations of the orthogonal column projection

The column projection from actual rank-`r + 1` orthogonal operators to the
unit sphere has native local trivializations with fiber the rank-`r`
orthogonal operator space. A continuous local rotation first moves the column
to the center of the chart, where the exact column-fiber calculation applies.
Only continuity on the stated open chart is asserted.
-/

namespace NoExoticSixSphere.OrthogonalColumnBundle

open GLOrthonormalization OrthogonalPaths ColumnFiber Set Bundle

variable {r : ℕ}
variable (v c : UnitSphere (Vector (r + 1)))

/-- The genuine unit-vector column of an orthogonal operator. -/
noncomputable def projection : C(OrthogonalOperators (r + 1), UnitSphere (Vector (r + 1))) :=
  column v (ContinuousMap.id _)

theorem projection_apply (a : OrthogonalOperators (r + 1)) :
    (projection v a : Vector (r + 1)) = a.1.1 (v : Vector (r + 1)) := rfl

/-- A chosen rotation between the chart center and a column, continuous on the chart. -/
noncomputable def rotation (x : UnitSphere (Vector (r + 1))) : OrthogonalOperators (r + 1) :=
  ofEquiv (localRotationEquiv (c : Vector (r + 1)) (x : Vector (r + 1)))

theorem rotation_apply (x : UnitSphere (Vector (r + 1))) :
    (rotation c x).1.1 (c : Vector (r + 1)) = (x : Vector (r + 1)) :=
  localRotationEquiv_apply c x

theorem continuousOn_rotation : ContinuousOn (rotation c) (Metric.ball c 1) := by
  apply continuousOn_iff_continuous_domRestrict.mpr
  have hcol : Continuous (fun x : ↥(Metric.ball c 1) ↦ (x.1 : Vector (r + 1))) :=
    continuous_subtype_val.comp continuous_subtype_val
  have hc := continuous_localRotationOperator
    (fun _ : ↥(Metric.ball c 1) ↦ (c : Vector (r + 1)))
    (fun x : ↥(Metric.ball c 1) ↦ (x.1 : Vector (r + 1))) continuous_const hcol
    (fun x ↦ ne_zero_of_mem_unit_sphere x.1)
    (fun x ↦ nearby_sum_ne_zero c (x.1 : Vector (r + 1)) x.2)
  exact (hc.subtype_mk _).subtype_mk _

/-- Move a varying column back to the chart center. -/
noncomputable def corrected (a : OrthogonalOperators (r + 1)) : OrthogonalOperators (r + 1) :=
  mul (inverse (rotation c (projection v a))) a

theorem corrected_column (a : OrthogonalOperators (r + 1)) :
    (corrected v c a).1.1 (v : Vector (r + 1)) = (c : Vector (r + 1)) := by
  change (inverse (rotation c (projection v a))).1.1 (projection v a : Vector (r + 1)) = _
  rw [← rotation_apply c (projection v a)]
  exact inverse_apply_self _ _

/-- Forward local coordinates; values outside the chart are not claimed to be continuous. -/
noncomputable def toCoordinates (a : OrthogonalOperators (r + 1)) :
    UnitSphere (Vector (r + 1)) × OrthogonalOperators r :=
  (projection v a, residual v c (corrected v c a) (corrected_column v c a))

/-- Inverse local coordinates, formed using the same chart-center rotation. -/
noncomputable def fromCoordinates
    (p : UnitSphere (Vector (r + 1)) × OrthogonalOperators r) : OrthogonalOperators (r + 1) :=
  mul (rotation c p.1) (reconstruct v c p.2)

theorem projection_fromCoordinates (p : UnitSphere (Vector (r + 1)) × OrthogonalOperators r) :
    projection v (fromCoordinates v c p) = p.1 := by
  apply Subtype.ext
  rw [projection_apply]
  change (mul (rotation c p.1) (reconstruct v c p.2)).1.1 (v : Vector (r + 1)) = _
  rw [mul_apply, reconstruct_column, rotation_apply]

theorem corrected_fromCoordinates (p : UnitSphere (Vector (r + 1)) × OrthogonalOperators r) :
    corrected v c (fromCoordinates v c p) = reconstruct v c p.2 := by
  rw [corrected, projection_fromCoordinates, fromCoordinates, ← OrthogonalPaths.mul_assoc,
    inverse_mul, identity_mul]

theorem fromCoordinates_toCoordinates (a : OrthogonalOperators (r + 1)) :
    fromCoordinates v c (toCoordinates v c a) = a := by
  change mul (rotation c (projection v a))
    (reconstruct v c (residual v c (corrected v c a) (corrected_column v c a))) = a
  rw [reconstruct_residual, corrected, ← OrthogonalPaths.mul_assoc, mul_inverse, identity_mul]

theorem toCoordinates_fromCoordinates (p : UnitSphere (Vector (r + 1)) × OrthogonalOperators r) :
    toCoordinates v c (fromCoordinates v c p) = p := by
  apply Prod.ext
  · exact projection_fromCoordinates v c p
  · change residual v c (corrected v c (fromCoordinates v c p))
      (corrected_column v c (fromCoordinates v c p)) = p.2
    simp only [corrected_fromCoordinates, residual_reconstruct]

variable {X : Type*} [TopologicalSpace X]

theorem continuous_corrected (a : X → OrthogonalOperators (r + 1)) (ha : Continuous a)
    (hcol : ∀ x, projection v (a x) ∈ Metric.ball c 1) :
    Continuous (fun x ↦ corrected v c (a x)) := by
  have hrot := (continuousOn_rotation c).comp_continuous ((projection v).continuous.comp ha) hcol
  exact continuous_mul _ _ (continuous_inverse _ hrot) ha

theorem continuous_toCoordinates (a : X → OrthogonalOperators (r + 1)) (ha : Continuous a)
    (hcol : ∀ x, projection v (a x) ∈ Metric.ball c 1) :
    Continuous (fun x ↦ toCoordinates v c (a x)) :=
  ((projection v).continuous.comp ha).prodMk
    (continuous_residual v c (fun x ↦ corrected v c (a x))
      (continuous_corrected v c a ha hcol) (fun x ↦ corrected_column v c (a x)))

theorem continuous_fromCoordinates
    (p : X → UnitSphere (Vector (r + 1)) × OrthogonalOperators r) (hp : Continuous p)
    (hcol : ∀ x, (p x).1 ∈ Metric.ball c 1) :
    Continuous (fun x ↦ fromCoordinates v c (p x)) :=
  continuous_mul _ _ ((continuousOn_rotation c).comp_continuous hp.fst hcol)
    (continuous_reconstruct v c (fun x ↦ (p x).2) hp.snd)

/-- The native local trivialization has the original orthogonal space as its total space. -/
noncomputable def trivialization : Trivialization (OrthogonalOperators r) (projection v) where
  toFun := toCoordinates v c
  invFun := fromCoordinates v c
  source := (projection v) ⁻¹' Metric.ball c 1
  target := Metric.ball c 1 ×ˢ univ
  map_source' a ha := ⟨ha, mem_univ _⟩
  map_target' p hp := by
    change projection v (fromCoordinates v c p) ∈ Metric.ball c 1
    rw [projection_fromCoordinates]
    exact hp.1
  left_inv' a _ := fromCoordinates_toCoordinates v c a
  right_inv' p _ := toCoordinates_fromCoordinates v c p
  open_source := Metric.isOpen_ball.preimage (projection v).continuous
  open_target := Metric.isOpen_ball.prod isOpen_univ
  continuousOn_toFun := continuousOn_iff_continuous_domRestrict.mpr
    (continuous_toCoordinates v c Subtype.val continuous_subtype_val Subtype.property)
  continuousOn_invFun := continuousOn_iff_continuous_domRestrict.mpr
    (continuous_fromCoordinates v c Subtype.val continuous_subtype_val (fun p ↦ p.2.1))
  baseSet := Metric.ball c 1
  open_baseSet := Metric.isOpen_ball
  source_eq := rfl
  target_eq := rfl
  proj_toFun _ _ := rfl

theorem center_mem_baseSet : c ∈ (trivialization v c).baseSet :=
  Metric.mem_ball_self (by norm_num)

end NoExoticSixSphere.OrthogonalColumnBundle
