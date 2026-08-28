import Wikipedia.NoExoticSixSphere.OrthogonalPaths
import Wikipedia.NoExoticSixSphere.SphereConnectivity
import Wikipedia.NoExoticSixSphere.CompactParameter

/-!
# Changing an orthogonal column along a sphere homotopy

Local orthogonal paths make the set of attainable endpoint columns open and
closed in a connected parameter space. On a compact base this gives a genuine
homotopy of orthogonal families with the prescribed endpoint column. It is an
endpoint-transport theorem, not a claim that the path follows every intermediate
slice of the supplied sphere homotopy.
-/

open scoped Topology
open Set Filter

namespace NoExoticSixSphere.OrthogonalPaths

open GLOrthonormalization

variable {n : ℕ} {X T : Type*}

/-- A uniform neighborhood of a column family in a continuous parameter family. -/
def columnNeighborDomain (H : T → X → UnitSphere (Vector n)) (s : T) : Set T :=
  {t | ∀ x, dist (H t x : Vector n) (H s x : Vector n) < 1}

/-- A column family belongs to its own uniform neighborhood. -/
theorem mem_columnNeighborDomain (H : T → X → UnitSphere (Vector n)) (s : T) :
    s ∈ columnNeighborDomain H s := by
  intro x
  simp only [dist_self, zero_lt_one]

variable [TopologicalSpace X] [CompactSpace X] [TopologicalSpace T]
  (H : T → X → UnitSphere (Vector n))
  (hc : Continuous (fun p : T × X ↦ H p.1 p.2))

include hc in
/-- Compactness makes the uniform column-neighborhood condition open. -/
theorem isOpen_columnNeighborDomain (s : T) : IsOpen (columnNeighborDomain H s) := by
  have h₁ : Continuous (fun p : T × X ↦ (H p.1 p.2 : Vector n)) :=
    continuous_subtype_val.comp hc
  have h₂ : Continuous (fun p : T × X ↦ (H s p.2 : Vector n)) :=
    continuous_subtype_val.comp (hc.comp (continuous_const.prodMk continuous_snd))
  exact isOpen_forall_compact (isOpen_lt (h₁.dist h₂) continuous_const)

/-- A continuous slice of the column family. -/
def columnSlice (s : T) : C(X, UnitSphere (Vector n)) :=
  ⟨H s, hc.comp (continuous_const.prodMk continuous_id)⟩

variable (v : UnitSphere (Vector n)) (a : C(X, OrthogonalOperators n))

/-- Endpoint columns obtainable by a homotopy of the original orthogonal family. -/
def columnReachable (t : T) : Prop :=
  ∃ b : C(X, OrthogonalOperators n), a.Homotopic b ∧
    ∀ x, (b x).1.1 (v : Vector n) = (H t x : Vector n)

include hc in
/-- Local rotations make the attainable endpoint columns an open set. -/
theorem isOpen_columnReachable : IsOpen {t | columnReachable H v a t} := by
  rw [isOpen_iff_mem_nhds]
  rintro t ⟨b, hab, hb⟩
  refine mem_of_superset ((isOpen_columnNeighborDomain H hc t).mem_nhds
    (mem_columnNeighborDomain H t)) ?_
  intro u hu
  obtain ⟨c, hbc, hc'⟩ := exists_nearbyColumnHomotopy v b
    (columnSlice H hc t) (columnSlice H hc u) hb hu
  exact ⟨c, hab.trans hbc, hc'⟩

include hc in
/-- The complement is open as well, because nearby column changes can be reversed. -/
theorem isOpen_compl_columnReachable : IsOpen {t | ¬ columnReachable H v a t} := by
  rw [isOpen_iff_mem_nhds]
  intro t ht
  refine mem_of_superset ((isOpen_columnNeighborDomain H hc t).mem_nhds
    (mem_columnNeighborDomain H t)) ?_
  rintro u hu ⟨b, hab, hb⟩
  have hnear : ∀ x, dist (H t x : Vector n) (H u x : Vector n) < 1 := by
    intro x
    rw [dist_comm]
    exact hu x
  obtain ⟨c, hbc, hc'⟩ := exists_nearbyColumnHomotopy v b
    (columnSlice H hc u) (columnSlice H hc t) hb hnear
  exact ht ⟨c, hab.trans hbc, hc'⟩

include hc in
/-- A connected sphere-column family can be transported between any two endpoint slices. -/
theorem exists_columnEndpointHomotopy [PreconnectedSpace T] (s t : T)
    (ha : ∀ x, (a x).1.1 (v : Vector n) = (H s x : Vector n)) :
    ∃ b : C(X, OrthogonalOperators n), a.Homotopic b ∧
      ∀ x, (b x).1.1 (v : Vector n) = (H t x : Vector n) := by
  let C : Set T := {u | columnReachable H v a u}
  have hclosed : IsClosed C := by
    simpa only [C, compl_ofPred, not_not] using
      (isOpen_compl_columnReachable H hc v a).isClosed_compl
  have hcl : IsClopen C := ⟨hclosed, isOpen_columnReachable H hc v a⟩
  have hall : C = univ := hcl.eq_univ ⟨s, ⟨a, ⟨ContinuousMap.Homotopy.refl a⟩, ha⟩⟩
  have ht : t ∈ C := by rw [hall]; exact mem_univ t
  exact ht

end OrthogonalPaths

namespace OrthogonalPaths

open GLOrthonormalization

variable {n : ℕ} {X : Type*} [TopologicalSpace X]

/-- The unit-vector column obtained by applying an orthogonal family to a fixed unit vector. -/
noncomputable def column (v : UnitSphere (Vector n)) (a : C(X, OrthogonalOperators n)) :
    C(X, UnitSphere (Vector n)) := by
  let f : X → Vector n := fun x ↦ (a x).1.1 (v : Vector n)
  have hf : Continuous f :=
    (continuous_subtype_val.comp (continuous_subtype_val.comp a.continuous)).clm_apply
      continuous_const
  have hn : ∀ x, f x ∈ UnitSphere (Vector n) := by
    intro x
    rw [Metric.mem_sphere, dist_zero_right]
    exact ((a x).2 (v : Vector n)).trans (ClosedHemisphere.unit_norm v)
  exact ⟨fun x ↦ ⟨f x, hn x⟩, hf.subtype_mk hn⟩

/-- Above the sphere's dimension, an orthogonal-valued map can be homotoped to have a constant
column. This uses the proved sphere nullhomotopy, not a homotopy-group assumption. -/
theorem exists_constantColumn_sphere {m r : ℕ} (hmr : m < r)
    (v : UnitSphere (Vector (r + 1))) (a : C(Sphere m, OrthogonalOperators (r + 1))) :
    ∃ c : UnitSphere (Vector (r + 1)), ∃ b : C(Sphere m, OrthogonalOperators (r + 1)),
      a.Homotopic b ∧ ∀ x, (b x).1.1 (v : Vector (r + 1)) = (c : Vector (r + 1)) := by
  let f := column v a
  obtain ⟨c, ⟨H⟩⟩ := sphere_sphere_nullhomotopic hmr f
  have hstart : ∀ x, (a x).1.1 (v : Vector (r + 1)) = (H (0, x) : Vector (r + 1)) := by
    intro x
    rw [H.apply_zero]
    rfl
  obtain ⟨b, hab, hb⟩ := exists_columnEndpointHomotopy
    (fun t x ↦ H (t, x)) H.continuous v a 0 1 hstart
  refine ⟨c, b, hab, ?_⟩
  intro x
  exact (hb x).trans (congrArg Subtype.val (H.apply_one x))

end OrthogonalPaths

end NoExoticSixSphere
