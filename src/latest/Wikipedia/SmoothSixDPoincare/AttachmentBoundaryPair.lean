import Wikipedia.SmoothSixDPoincare.SurgeryComplementPieces

/-!
# Closed surgery pieces on the frontier of an embedded handle attachment

The exterior is the actual intersection of the lower level and the attachment
frontier. Closedness of the handle proves both covers. The two coordinate-face
identities then give the exact common-boundary incidences.
-/

noncomputable section

open Set Filter Metric Topology
open scoped Topology

namespace Wikipedia.SmoothSixDPoincare

open PuncturedHandle

/-- Local face information for an actual embedded handle, together with regularity
of the lower sublevel frontier. No surgery presentation is assumed. -/
structure AttachmentBoundaryData (N P M : Type*)
    [NormedAddCommGroup N] [NormedAddCommGroup P] [TopologicalSpace M]
    (f : M → ℝ) (a : ℝ) where
  handle : UnitBall N × UnitBall P → M
  handle_closed : IsClosedEmbedding handle
  height_continuous : Continuous f
  lower_frontier : frontier {x | f x ≤ a} = {x | f x = a}
  lower_face : ∀ z, f (handle z) = a ↔ ‖(z.1 : N)‖ = 1
  upper_face : ∀ z, handle z ∈ frontier ({x | f x ≤ a} ∪ range handle) ↔
    ‖(z.2 : P)‖ = 1

namespace AttachmentBoundaryData

variable {N P M : Type*} [NormedAddCommGroup N] [NormedAddCommGroup P]
  [TopologicalSpace M] {f : M → ℝ} {a : ℝ} (d : AttachmentBoundaryData N P M f a)

abbrev Level (_ : AttachmentBoundaryData N P M f a) := {x : M // f x = a}
abbrev region : Set M := {x | f x ≤ a} ∪ range d.handle
abbrev Boundary := frontier d.region
abbrev Exterior := {x : M // f x = a ∧ x ∈ d.Boundary}

def oldExterior : d.Exterior → d.Level := fun x => ⟨x, x.property.1⟩
def newExterior : d.Exterior → d.Boundary := fun x => ⟨x, x.property.2⟩

def oldPiece (z : UnitSphere N × UnitBall P) : d.Level :=
  ⟨d.handle (sphereToBall z.1, z.2),
    (d.lower_face _).mpr (mem_sphere_zero_iff_norm.mp z.1.property)⟩

def newPiece (z : UnitBall N × UnitSphere P) : d.Boundary :=
  ⟨d.handle (z.1, sphereToBall z.2),
    (d.upper_face _).mpr (mem_sphere_zero_iff_norm.mp z.2.property)⟩

def boundary (q : UnitSphere N × UnitSphere P) : d.Exterior :=
  ⟨d.handle (sphereToBall q.1, sphereToBall q.2),
    (d.lower_face _).mpr (mem_sphere_zero_iff_norm.mp q.1.property),
    (d.upper_face _).mpr (mem_sphere_zero_iff_norm.mp q.2.property)⟩

theorem oldExterior_closed : IsClosedEmbedding d.oldExterior :=
  ClosedCover.isClosedEmbedding_codRestrict
    ((isClosed_eq d.height_continuous continuous_const).inter
      isClosed_frontier).isClosedEmbedding_subtypeVal (fun x => x.property.1)

theorem newExterior_closed : IsClosedEmbedding d.newExterior :=
  ClosedCover.isClosedEmbedding_codRestrict
    ((isClosed_eq d.height_continuous continuous_const).inter
      isClosed_frontier).isClosedEmbedding_subtypeVal (fun x => x.property.2)

theorem sphereToBall_closed : IsClosedEmbedding (sphereToBall (E := N)) :=
  ClosedCover.isClosedEmbedding_codRestrict isClosed_sphere.isClosedEmbedding_subtypeVal
    (fun u => (mem_sphere_zero_iff_norm.mp u.property).le)

theorem oldPiece_closed : IsClosedEmbedding d.oldPiece := by
  exact ClosedCover.isClosedEmbedding_codRestrict
    (d.handle_closed.comp (sphereToBall_closed.prodMap IsClosedEmbedding.id))
    (fun z => (d.lower_face _).mpr (mem_sphere_zero_iff_norm.mp z.1.property))

theorem newPiece_closed : IsClosedEmbedding d.newPiece := by
  apply ClosedCover.isClosedEmbedding_codRestrict
  exact d.handle_closed.comp (IsClosedEmbedding.id.prodMap sphereToBall_closed)

theorem old_cover : range d.oldExterior ∪ range d.oldPiece = univ := by
  apply eq_univ_of_forall
  intro x
  by_cases hx : (x : M) ∈ range d.handle
  · obtain ⟨z, hz⟩ := hx
    have hnorm : ‖(z.1 : N)‖ = 1 := (d.lower_face z).mp (hz ▸ x.property)
    refine Or.inr ⟨(⟨z.1, mem_sphere_zero_iff_norm.mpr hnorm⟩, z.2), ?_⟩
    exact Subtype.ext hz
  · have hfront : (x : M) ∈ d.Boundary := by
      have hlow : (x : M) ∈ frontier {y | f y ≤ a} := by
        rw [d.lower_frontier]
        exact x.property
      change (x : M) ∈ frontier d.region
      rw [frontier] at hlow ⊢
      refine ⟨closure_mono subset_union_left hlow.1, ?_⟩
      intro hi
      apply hlow.2
      apply mem_interior_iff_mem_nhds.mpr
      have hnear := mem_interior_iff_mem_nhds.mp hi
      have hout := d.handle_closed.isClosed_range.isOpen_compl.mem_nhds hx
      apply mem_of_superset (inter_mem hnear hout)
      intro y hy
      exact hy.1.resolve_right hy.2
    exact Or.inl ⟨⟨x, x.property, hfront⟩, rfl⟩

theorem new_cover : range d.newExterior ∪ range d.newPiece = univ := by
  apply eq_univ_of_forall
  intro x
  have hclosed : IsClosed d.region :=
    (isClosed_le d.height_continuous continuous_const).union d.handle_closed.isClosed_range
  have hx : (x : M) ∈ d.region := by
    have hc := frontier_subset_closure x.property
    rwa [hclosed.closure_eq] at hc
  rcases hx with hx | ⟨z, hz⟩
  · have heq : f x = a := by
      apply le_antisymm hx
      by_contra hn
      have hlt : f x < a := lt_of_not_ge hn
      have hi : (x : M) ∈ interior d.region :=
        interior_maximal (fun y (hy : f y < a) => Or.inl hy.le)
          (isOpen_lt d.height_continuous continuous_const) hlt
      exact x.property.2 hi
    exact Or.inl ⟨⟨x, heq, x.property⟩, rfl⟩
  · have hnorm : ‖(z.2 : P)‖ = 1 := (d.upper_face z).mp (hz ▸ x.property)
    refine Or.inr ⟨(z.1, ⟨z.2, mem_sphere_zero_iff_norm.mpr hnorm⟩), ?_⟩
    exact Subtype.ext hz

theorem old_overlap (r : d.Exterior) (z : UnitSphere N × UnitBall P) :
    d.oldExterior r = d.oldPiece z ↔
      ∃ q, r = d.boundary q ∧ z = oldBoundary q := by
  constructor
  · intro h
    have hr : (r : M) = d.handle (sphereToBall z.1, z.2) := congrArg Subtype.val h
    have hnorm : ‖(z.2 : P)‖ = 1 := (d.upper_face _).mp (hr ▸ r.property.2)
    refine ⟨(z.1, ⟨z.2, mem_sphere_zero_iff_norm.mpr hnorm⟩), Subtype.ext hr, rfl⟩
  · rintro ⟨q, rfl, rfl⟩
    rfl

theorem new_overlap (r : d.Exterior) (z : UnitBall N × UnitSphere P) :
    d.newExterior r = d.newPiece z ↔
      ∃ q, r = d.boundary q ∧ z = newBoundary q := by
  constructor
  · intro h
    have hr : (r : M) = d.handle (z.1, sphereToBall z.2) := congrArg Subtype.val h
    have hnorm : ‖(z.1 : N)‖ = 1 := (d.lower_face _).mp (hr ▸ r.property.1)
    refine ⟨(⟨z.1, mem_sphere_zero_iff_norm.mpr hnorm⟩, z.2), Subtype.ext hr, rfl⟩
  · rintro ⟨q, rfl, rfl⟩
    rfl

/-- The exact closed-piece surgery presentation of the original level and attachment frontier. -/
def surgeryBoundaryPair : SurgeryBoundaryPair N P d.Exterior d.Level d.Boundary where
  oldExterior := d.oldExterior
  newExterior := d.newExterior
  oldPiece := d.oldPiece
  newPiece := d.newPiece
  oldExterior_closed := d.oldExterior_closed
  newExterior_closed := d.newExterior_closed
  oldPiece_closed := d.oldPiece_closed
  newPiece_closed := d.newPiece_closed
  old_cover := d.old_cover
  new_cover := d.new_cover
  boundary := d.boundary
  old_overlap := d.old_overlap
  new_overlap := d.new_overlap

end AttachmentBoundaryData

end Wikipedia.SmoothSixDPoincare
