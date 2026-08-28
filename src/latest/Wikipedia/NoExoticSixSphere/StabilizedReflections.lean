import Wikipedia.NoExoticSixSphere.OrthogonalStabilization

/-!
# Nullhomotopies of stabilized reflection families

A continuously chosen unit normal gives a hyperplane-reflection family. After
adding one identity coordinate, that family is nullhomotopic: embed its normals
in the new equator, contract them through the closed hemisphere, and reflect in
their perpendicular hyperplanes. These are actual operator homotopies. No claim
that arbitrary sphere-valued orthogonal families are products of such families
is made here.
-/

namespace NoExoticSixSphere

open GLOrthonormalization OrthogonalPaths ColumnCoordinates ColumnFiber FixedColumnBlock

namespace OrthogonalPaths

variable {n : ℕ}

/-- Hyperplane reflection packaged as an orthogonal operator. -/
noncomputable def reflection (w : Vector n) : OrthogonalOperators n :=
  ofEquiv ((ℝ ∙ w)ᗮ.reflection)

theorem reflection_operator (w : Vector n) : (reflection w).1.1 =
    hyperplaneReflectionOperator w := rfl

/-- Reflection in unit normals is a continuous map to the actual orthogonal operator space. -/
noncomputable def reflectionMap : C(UnitSphere (Vector n), OrthogonalOperators n) :=
  ⟨fun w ↦ reflection w,
    ((continuous_hyperplaneReflectionOperator Subtype.val continuous_subtype_val
      (fun w ↦ ne_zero_of_mem_unit_sphere w)).subtype_mk _).subtype_mk _⟩

end OrthogonalPaths

namespace OrthogonalStabilization

variable {r : ℕ}

local instance reflectionDimensionFact : Fact (Module.finrank ℝ (Vector (r + 1)) = r + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable (v : UnitSphere (Vector (r + 1)))

/-- Embed the lower-rank space as the actual orthogonal complement of the new coordinate. -/
noncomputable def embed (w : Vector r) : Vector (r + 1) :=
  (split (r := r) v).symm (tailInclusion w)

theorem split_embed (w : Vector r) : split (r := r) v (embed v w) = tailInclusion w :=
  LinearIsometryEquiv.apply_symm_apply _ _

theorem norm_embed (w : Vector r) : ‖embed v w‖ = ‖w‖ := by
  rw [embed, LinearIsometryEquiv.norm_map, norm_tailInclusion]

theorem continuous_embed : Continuous (embed v) :=
  (split (r := r) v).symm.continuous.comp tailInclusion.continuous

theorem inner_embed (w : Vector r) (z : Vector (r + 1)) :
    inner ℝ (embed v w) z = inner ℝ w (split (r := r) v z).snd := by
  have h := (split (r := r) v).inner_map_map (embed v w) z
  rw [split_embed] at h
  simpa [tailInclusion, WithLp.prod_inner_apply] using h.symm

theorem inner_embed_self (w : Vector r) : inner ℝ (v : Vector (r + 1)) (embed v w) = 0 := by
  rw [← split_fst (r := r) v, split_embed]
  rfl

/-- The unit normal embedded on the equator. -/
noncomputable def embedUnit (w : UnitSphere (Vector r)) : UnitSphere (Vector (r + 1)) :=
  ⟨embed v w, by
    rw [Metric.mem_sphere, dist_zero_right, norm_embed]
    exact ClosedHemisphere.unit_norm w⟩

theorem continuous_embedUnit : Continuous (embedUnit v) :=
  ((continuous_embed v).comp continuous_subtype_val).subtype_mk _

/-- The embedded normal lies in the closed hemisphere centered on the new coordinate. -/
noncomputable def embedHemisphere (w : UnitSphere (Vector r)) : ClosedHemisphere v :=
  ⟨embedUnit v w, by
    change 0 ≤ inner ℝ (v : Vector (r + 1)) (embed v w)
    rw [inner_embed_self]⟩

theorem continuous_embedHemisphere : Continuous (embedHemisphere v) :=
  (continuous_embedUnit v).subtype_mk _

/-- The equatorial inclusion as a continuous sphere map. -/
noncomputable def embedUnitMap : C(UnitSphere (Vector r), UnitSphere (Vector (r + 1))) :=
  ⟨embedUnit v, continuous_embedUnit v⟩

open unitInterval

/-- Contract the embedded normals through actual unit normals. -/
noncomputable def embedUnitHomotopy :
    (embedUnitMap v).Homotopy (ContinuousMap.const _ v) := by
  let inclusion : C(ClosedHemisphere v, UnitSphere (Vector (r + 1))) :=
    ⟨Subtype.val, continuous_subtype_val⟩
  let intoHemisphere : C(UnitSphere (Vector r), ClosedHemisphere v) :=
    ⟨embedHemisphere v, continuous_embedHemisphere v⟩
  let H := (ContinuousMap.Homotopy.refl inclusion).comp
    ((ClosedHemisphere.contraction v).compContinuousMap intoHemisphere)
  exact H.cast (by apply ContinuousMap.ext; intro w; rfl)
    (by apply ContinuousMap.ext; intro w; rfl)

/-- Stabilizing a reflection is exactly reflection in its embedded normal. -/
theorem stabilize_reflection (w : Vector r) :
    stabilize v (reflection w) = reflection (embed v w) := by
  apply Subtype.ext
  apply Subtype.ext
  apply ContinuousLinearMap.ext
  intro z
  apply (split (r := r) v).injective
  rw [stabilize_apply, LinearIsometryEquiv.apply_symm_apply, reflection_operator,
    hyperplaneReflectionOperator_apply, map_sub, map_smul, norm_embed, inner_embed, split_embed]
  rw [block_apply, toEquiv_apply, reflection_operator, hyperplaneReflectionOperator_apply]
  apply WithLp.ofLp_injective 2
  apply Prod.ext <;> simp [tailInclusion]

/-- The universal unit-normal reflection family becomes nullhomotopic after one stabilization. -/
theorem stabilized_reflectionMap_nullhomotopic :
    (stabilizeMap v (reflectionMap (n := r))).Homotopic
      (ContinuousMap.const _ (reflection (v : Vector (r + 1)))) := by
  have h := (ContinuousMap.Homotopic.refl (reflectionMap (n := r + 1))).comp
    (show (embedUnitMap v).Homotopic (ContinuousMap.const _ v) from ⟨embedUnitHomotopy v⟩)
  have hstart : (reflectionMap (n := r + 1)).comp (embedUnitMap v) =
      stabilizeMap v (reflectionMap (n := r)) := by
    apply ContinuousMap.ext
    intro w
    exact (stabilize_reflection v w).symm
  rw [hstart] at h
  exact h

variable {X : Type*} [TopologicalSpace X]

/-- Every continuous unit-normal reflection family, on any base, has the same stable contraction. -/
theorem stabilized_reflectionFamily_nullhomotopic (f : C(X, UnitSphere (Vector r))) :
    (stabilizeMap v (reflectionMap.comp f)).Homotopic
      (ContinuousMap.const _ (reflection (v : Vector (r + 1)))) :=
  (stabilized_reflectionMap_nullhomotopic v).comp (ContinuousMap.Homotopic.refl f)

end OrthogonalStabilization

end NoExoticSixSphere
