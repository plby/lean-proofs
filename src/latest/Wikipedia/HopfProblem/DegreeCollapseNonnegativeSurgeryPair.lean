import Wikipedia.SmoothSixDPoincare.SurgeryBoundaryPair

/-!
# Restrict an actual closed surgery presentation to its nonnegative halves

The entire old and new handles stay in their respective halves. On the
common exterior the two nonnegativity conditions agree. Restricting the
actual maps preserves closed embeddings, exhaustive covers, and exact
corner incidences, without introducing a comparison homeomorphism premise.
-/

noncomputable section

open Function Set Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.NonnegativeSurgeryPair

open Wikipedia.SmoothSixDPoincare PuncturedHandle

variable {E F R X Y : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]
  [TopologicalSpace R] [TopologicalSpace X] [TopologicalSpace Y]
  (d : SurgeryBoundaryPair E F R X Y) (tx : X → ℝ) (ty : Y → ℝ)
  (hx : Continuous tx)
  (hold : ∀ p, 0 ≤ tx (d.oldPiece p)) (hnew : ∀ p, 0 ≤ ty (d.newPiece p))
  (hext : ∀ r, 0 ≤ tx (d.oldExterior r) ↔ 0 ≤ ty (d.newExterior r))

abbrev Exterior := {r : R // 0 ≤ tx (d.oldExterior r)}

def oldExterior (r : Exterior d tx) : {x : X // 0 ≤ tx x} := ⟨d.oldExterior r.val, r.property⟩

def newExterior (r : Exterior d tx) : {y : Y // 0 ≤ ty y} :=
  ⟨d.newExterior r.val, (hext r.val).mp r.property⟩

def oldPiece (p : UnitSphere E × UnitBall F) : {x : X // 0 ≤ tx x} := ⟨d.oldPiece p, hold p⟩

def newPiece (p : UnitBall E × UnitSphere F) : {y : Y // 0 ≤ ty y} := ⟨d.newPiece p, hnew p⟩

def boundary (p : UnitSphere E × UnitSphere F) : Exterior d tx :=
  ⟨d.boundary p, by
    have he := (d.old_overlap (d.boundary p) (oldBoundary p)).mpr ⟨p, rfl, rfl⟩
    rw [he]
    exact hold (oldBoundary p)⟩

include hx in
theorem oldExterior_closed : IsClosedEmbedding (oldExterior d tx) := by
  have hc : IsClosed {r : R | 0 ≤ tx (d.oldExterior r)} :=
    isClosed_le continuous_const (hx.comp d.oldExterior_closed.continuous)
  exact IsClosedEmbedding.of_comp IsEmbedding.subtypeVal
    (d.oldExterior_closed.comp hc.isClosedEmbedding_subtypeVal)

include hx in
theorem newExterior_closed : IsClosedEmbedding (newExterior d tx ty hext) := by
  have hc : IsClosed {r : R | 0 ≤ tx (d.oldExterior r)} :=
    isClosed_le continuous_const (hx.comp d.oldExterior_closed.continuous)
  exact IsClosedEmbedding.of_comp IsEmbedding.subtypeVal
    (d.newExterior_closed.comp hc.isClosedEmbedding_subtypeVal)

def pair : SurgeryBoundaryPair E F (Exterior d tx) {x : X // 0 ≤ tx x} {y : Y // 0 ≤ ty y} where
  oldExterior := oldExterior d tx
  newExterior := newExterior d tx ty hext
  oldPiece := oldPiece d tx hold
  newPiece := newPiece d ty hnew
  oldExterior_closed := oldExterior_closed d tx hx
  newExterior_closed := newExterior_closed d tx ty hx hext
  oldPiece_closed := IsClosedEmbedding.of_comp IsEmbedding.subtypeVal d.oldPiece_closed
  newPiece_closed := IsClosedEmbedding.of_comp IsEmbedding.subtypeVal d.newPiece_closed
  old_cover := by
    apply eq_univ_of_forall
    intro x
    have h : x.val ∈ range d.oldExterior ∪ range d.oldPiece := by rw [d.old_cover]; trivial
    rcases h with ⟨r, hr⟩ | ⟨p, hp⟩
    · exact Or.inl ⟨⟨r, by rw [hr]; exact x.property⟩, Subtype.ext hr⟩
    · exact Or.inr ⟨p, Subtype.ext hp⟩
  new_cover := by
    apply eq_univ_of_forall
    intro y
    have h : y.val ∈ range d.newExterior ∪ range d.newPiece := by rw [d.new_cover]; trivial
    rcases h with ⟨r, hr⟩ | ⟨p, hp⟩
    · refine Or.inl ⟨⟨r, (hext r).mpr ?_⟩, Subtype.ext hr⟩
      rw [hr]
      exact y.property
    · exact Or.inr ⟨p, Subtype.ext hp⟩
  boundary := boundary d tx hold
  old_overlap := by
    intro r p
    constructor
    · intro h
      obtain ⟨q, hr, hp⟩ := (d.old_overlap r.val p).mp
        (congrArg (fun x : {x : X // 0 ≤ tx x} ↦ x.val) h)
      exact ⟨q, Subtype.ext hr, hp⟩
    · rintro ⟨q, rfl, rfl⟩
      exact Subtype.ext ((d.old_overlap _ _).mpr ⟨q, rfl, rfl⟩)
  new_overlap := by
    intro r p
    constructor
    · intro h
      obtain ⟨q, hr, hp⟩ := (d.new_overlap r.val p).mp
        (congrArg (fun y : {y : Y // 0 ≤ ty y} ↦ y.val) h)
      exact ⟨q, Subtype.ext hr, hp⟩
    · rintro ⟨q, rfl, rfl⟩
      exact Subtype.ext ((d.new_overlap _ _).mpr ⟨q, rfl, rfl⟩)

theorem pair_attachingSphere (p : UnitSphere E) :
    ((pair d tx ty hx hold hnew hext).attachingSphere p).val = d.attachingSphere p := rfl

theorem pair_beltSphere (p : UnitSphere F) :
    ((pair d tx ty hx hold hnew hext).beltSphere p).val = d.beltSphere p := rfl

end Wikipedia.HopfProblem.DegreeCollapse.NonnegativeSurgeryPair
