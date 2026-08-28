import Wikipedia.NoExoticSixSphere.CircleCylinderFold

/-!
# Positive halves of the genuine double's components are path connected

For a basepoint of nonnegative time, the literal fold fixes the basepoint
and preserves its connected component. Restricting the fold gives a
surjective continuous retraction onto that component's positive half.
The source component is path connected in the native regular-fiber atlas,
so the positive half is path connected as well. In particular, this applies
to either original endpoint without assuming connectivity of the full double.
-/

noncomputable section

open Function Set
open scoped Manifold

namespace NoExoticSixSphere.CircleCylinder

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem fiberFold_mem_component (p : Fiber d) (hp : 0 ≤ time d p)
    {q : Fiber d} (hq : q ∈ connectedComponent p) :
    fiberFold d q ∈ connectedComponent p := by
  have h := (fiberFold d).continuous.mapsTo_connectedComponent p hq
  rwa [fiberFold_eq_self d p hp] at h

abbrev ComponentPositiveHalf (p : Fiber d) :=
  {q : Fiber d // q ∈ connectedComponent p ∧ 0 ≤ time d q}

def componentPositiveRetraction (p : Fiber d) (hp : 0 ≤ time d p) :
    C(connectedComponent p, ComponentPositiveHalf d p) where
  toFun q := ⟨fiberFold d q.val, fiberFold_mem_component d p hp q.property,
    (time_fiberFold d q.val).symm ▸ abs_nonneg (time d q.val)⟩
  continuous_toFun := ((fiberFold d).continuous.comp continuous_subtype_val).subtype_mk _

theorem componentPositiveRetraction_val (p : Fiber d) (hp : 0 ≤ time d p)
    (q : connectedComponent p) :
    (componentPositiveRetraction d p hp q).val = fiberFold d q.val := rfl

theorem componentPositiveRetraction_retract (p : Fiber d) (hp : 0 ≤ time d p)
    (q : ComponentPositiveHalf d p) :
    componentPositiveRetraction d p hp ⟨q.val, q.property.1⟩ = q :=
  Subtype.ext (fiberFold_eq_self d q.val q.property.2)

theorem componentPositiveRetraction_surjective (p : Fiber d) (hp : 0 ≤ time d p) :
    Surjective (componentPositiveRetraction d p hp) :=
  fun q ↦ ⟨⟨q.val, q.property.1⟩, componentPositiveRetraction_retract d p hp q⟩

theorem fiberFold_image_component (p : Fiber d) (hp : 0 ≤ time d p) :
    fiberFold d '' connectedComponent p = connectedComponent p ∩ {q | 0 ≤ time d q} := by
  apply Subset.antisymm
  · rintro q ⟨r, hr, rfl⟩
    refine ⟨fiberFold_mem_component d p hp hr, ?_⟩
    change 0 ≤ time d (fiberFold d r)
    rw [time_fiberFold]
    exact abs_nonneg _
  · intro q hq
    exact ⟨q, hq.1, fiberFold_eq_self d q hq.2⟩

theorem isPathConnected_component (k : ℕ) (hd : m = n + k) (p : Fiber d) :
    IsPathConnected (connectedComponent p) := by
  let := fiberAtlas d k hd
  let : LocallyPathConnectedSpace (Fiber d) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin (k + 1))) (Fiber d)
  rw [← pathComponent_eq_connectedComponent]
  exact isPathConnected_pathComponent

theorem isClopen_component (k : ℕ) (hd : m = n + k) (p : Fiber d) :
    IsClopen (connectedComponent p) := by
  let := fiberAtlas d k hd
  let : LocallyPathConnectedSpace (Fiber d) :=
    ChartedSpace.locallyPathConnectedSpace (EuclideanSpace ℝ (Fin (k + 1))) (Fiber d)
  rw [← pathComponent_eq_connectedComponent]
  exact IsClopen.pathComponent p

theorem pathConnectedSpace_componentPositiveHalf (k : ℕ) (hd : m = n + k)
    (p : Fiber d) (hp : 0 ≤ time d p) : PathConnectedSpace (ComponentPositiveHalf d p) := by
  let : PathConnectedSpace (connectedComponent p) :=
    isPathConnected_iff_pathConnectedSpace.mp (isPathConnected_component d k hd p)
  exact (componentPositiveRetraction_surjective d p hp).pathConnectedSpace
    (componentPositiveRetraction d p hp).continuous

theorem isPathConnected_component_positive (k : ℕ) (hd : m = n + k)
    (p : Fiber d) (hp : 0 ≤ time d p) :
    IsPathConnected (connectedComponent p ∩ {q | 0 ≤ time d q}) :=
  isPathConnected_iff_pathConnectedSpace.mpr
    (pathConnectedSpace_componentPositiveHalf d k hd p hp)

end NoExoticSixSphere.CircleCylinder
