import Wikipedia.NoExoticSixSphere.OrthogonalHomotopyLift

/-!
# Based versions of the sphere nullhomotopies

An unbased sphere nullhomotopy can be made stationary at any prescribed source
point. Lift the path traced by that point to orthogonal operators and apply
their inverses to the entire homotopy. In particular, the lower-to-higher sphere
nullhomotopy theorem holds relative to a chosen base point.
-/

open Set unitInterval

namespace NoExoticSixSphere

open GLOrthonormalization OrthogonalPaths

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

/-- Turn a sphere nullhomotopy into a native homotopy relative to a chosen source point. -/
theorem sphere_nullhomotopicRel_point_of_nullhomotopic
    (f : C(X, UnitSphere (Vector n))) (p : X) (c : UnitSphere (Vector n))
    (H : f.Homotopy (ContinuousMap.const X c)) :
    Nonempty (f.HomotopyRel (ContinuousMap.const X (f p)) {p}) := by
  let pathFamily : C(I × Unit, UnitSphere (Vector n)) :=
    H.toContinuousMap.comp ⟨fun q ↦ (q.1, p), continuous_fst.prodMk continuous_const⟩
  have hstart : ∀ x : Unit, ((ContinuousMap.const Unit (identity n)) x).1.1
      (f p : Vector n) = (pathFamily (0, x) : Vector n) := by
    intro x
    change (f p : Vector n) = (H (0, p) : Vector n)
    rw [H.apply_zero]
  obtain ⟨A, hA0, hAcol, -⟩ := exists_exactColumnLift pathFamily (f p)
    (ContinuousMap.const Unit (identity n)) hstart
  let family : C(I × X, OrthogonalOperators n) :=
    A.comp ⟨fun q ↦ (q.1, ()), continuous_fst.prodMk continuous_const⟩
  have hfamily : ∀ t, (family (t, p)).1.1 (f p : Vector n) = (H (t, p) : Vector n) :=
    fun t ↦ hAcol t ()
  let k : I × X → Vector n := fun q ↦ (inverse (family q)).1.1 (H q : Vector n)
  have hk : Continuous k :=
    (continuous_subtype_val.comp
      (continuous_subtype_val.comp (continuous_inverse family family.continuous))).clm_apply
        (continuous_subtype_val.comp H.continuous)
  have hunit : ∀ q, k q ∈ UnitSphere (Vector n) := by
    intro q
    rw [Metric.mem_sphere, dist_zero_right]
    exact ((inverse (family q)).2 (H q : Vector n)).trans (ClosedHemisphere.unit_norm (H q))
  let K : C(I × X, UnitSphere (Vector n)) := ⟨fun q ↦ ⟨k q, hunit q⟩, hk.subtype_mk hunit⟩
  have hzero : ∀ x, K (0, x) = f x := by
    intro x
    apply Subtype.ext
    change (inverse (A (0, ()))).1.1 (H (0, x) : Vector n) = (f x : Vector n)
    rw [hA0, H.apply_zero]
    exact inverse_apply_self (identity n) (f x : Vector n)
  have hfixed : ∀ t, K (t, p) = f p := by
    intro t
    apply Subtype.ext
    change (inverse (family (t, p))).1.1 (H (t, p) : Vector n) = (f p : Vector n)
    rw [← hfamily]
    exact inverse_apply_self _ _
  have hone : ∀ x, K (1, x) = f p := by
    intro x
    apply Subtype.ext
    change (inverse (A (1, ()))).1.1 (H (1, x) : Vector n) = (f p : Vector n)
    have hpoint := congrArg Subtype.val (hfixed 1)
    change (inverse (A (1, ()))).1.1 (H (1, p) : Vector n) = (f p : Vector n) at hpoint
    rw [H.apply_one] at hpoint ⊢
    exact hpoint
  refine ⟨{ toContinuousMap := K
            map_zero_left := hzero
            map_one_left := hone
            prop' := ?_ }⟩
  intro t x hx
  rcases mem_singleton_iff.mp hx with rfl
  exact hfixed t

/-- Every continuous map from a lower-dimensional sphere is nullhomotopic relative to a point. -/
theorem sphere_sphere_nullhomotopicRel_point {m r : ℕ} (hmr : m < r)
    (f : C(Sphere m, Sphere r)) (p : Sphere m) :
    Nonempty (f.HomotopyRel (ContinuousMap.const _ (f p)) {p}) := by
  obtain ⟨c, ⟨H⟩⟩ := sphere_sphere_nullhomotopic hmr f
  exact sphere_nullhomotopicRel_point_of_nullhomotopic f p c H

end NoExoticSixSphere
