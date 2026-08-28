import Wikipedia.NoExoticSixSphere.ComplexStructureColumn
import Wikipedia.NoExoticSixSphere.BasedSphereConnectivity

/-!
# Exact relative homotopy lifting for complex-structure columns

Transport the sphere-valued column in the orthogonal complement of a fixed
unit vector, extend the transport by the identity on that vector, and conjugate
the original complex structure. All stationary parameters remain fixed.
-/

open Set unitInterval

namespace NoExoticSixSphere.OrthogonalComplexStructures

open GLOrthonormalization OrthogonalPaths

variable {n : ℕ} {X : Type*} [TopologicalSpace X] [CompactSpace X]

theorem exists_exactColumnHomotopyRel (v : UnitSphere (Vector (n + 2)))
    (f : C(X, Space (n + 2))) {g : C(X, Sphere n)} {S : Set X}
    (H : ((columnMap v).comp f).HomotopyRel g S) :
    ∃ q : C(X, Space (n + 2)), ∃ K : f.HomotopyRel q S,
      ∀ t x, column v (K (t, x)) = H (t, x) := by
  obtain ⟨T, hT0, hTcol, hTfix⟩ :=
    exists_columnTransport H.toHomotopy.toContinuousMap
  let A : C(I × X, OrthogonalOperators (n + 2)) :=
    ⟨fun z ↦ ColumnFiber.reconstruct v v (T z),
      ColumnFiber.continuous_reconstruct v v T T.continuous⟩
  let F : C(I × X, Space (n + 2)) :=
    ⟨fun z ↦ conjugate (A z) (f z.2),
      continuous_conjugate A (fun z ↦ f z.2) A.continuous
        (f.continuous.comp continuous_snd)⟩
  have hA0 : ∀ x, A (0, x) = identity (n + 2) := by
    intro x
    change ColumnFiber.reconstruct v v (T (0, x)) = _
    rw [hT0]
    exact OrthogonalStabilization.stabilize_identity v
  have hF0 : ∀ x, F (0, x) = f x := by
    intro x
    change conjugate (A (0, x)) (f x) = f x
    rw [hA0, conjugate_identity]
  have hFfix : ∀ t x, x ∈ S → F (t, x) = f x := by
    intro t x hx
    have ht : T (t, x) = identity (n + 1) :=
      hTfix x (fun u ↦ (H.eq_fst u hx).trans (H.eq_fst 0 hx).symm) t
    change conjugate (ColumnFiber.reconstruct v v (T (t, x))) (f x) = f x
    rw [ht]
    change conjugate (OrthogonalStabilization.stabilize v (identity (n + 1))) (f x) = f x
    rw [OrthogonalStabilization.stabilize_identity, conjugate_identity]
  let q : C(X, Space (n + 2)) :=
    F.comp ⟨fun x ↦ (1, x), continuous_const.prodMk continuous_id⟩
  let K : f.HomotopyRel q S :=
    { toContinuousMap := F
      map_zero_left := hF0
      map_one_left := fun _ ↦ rfl
      prop' := hFfix }
  refine ⟨q, K, ?_⟩
  intro t x
  apply Subtype.ext
  change (column v (conjugate (ColumnFiber.reconstruct v v (T (t, x))) (f x)) :
    Vector (n + 1)) = (H (t, x) : Vector (n + 1))
  rw [column_conjugate]
  have h := hTcol t x
  change (T (t, x)).1.1 (H (0, x) : Vector (n + 1)) = (H (t, x) : Vector (n + 1)) at h
  rw [H.apply_zero] at h
  exact h

/-- A lower-dimensional sphere family can be homotoped, relative to a base
point, to a family with one constant complex-structure column. -/
theorem exists_based_constant_column {m : ℕ} (hmn : m < n)
    (v : UnitSphere (Vector (n + 2))) (f : C(Sphere m, Space (n + 2)))
    (p : Sphere m) :
    ∃ q : C(Sphere m, Space (n + 2)), q p = f p ∧
      Nonempty (f.HomotopyRel q {p}) ∧
      ∀ x, column v (q x) = column v (f p) := by
  obtain ⟨H⟩ := sphere_sphere_nullhomotopicRel_point hmn ((columnMap v).comp f) p
  obtain ⟨q, K, hcol⟩ := exists_exactColumnHomotopyRel v f H
  refine ⟨q, (K.fst_eq_snd (by simp)).symm, ⟨K⟩, ?_⟩
  intro x
  have h := hcol 1 x
  rw [K.apply_one, H.apply_one] at h
  exact h

end NoExoticSixSphere.OrthogonalComplexStructures
