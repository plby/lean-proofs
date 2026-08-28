import Wikipedia.HopfProblem.DegreeCollapseDiskBoundaryGluing

/-!
# Homotopy extension for the literal boundary of a finite-dimensional disk

Compatible bottom and side data extend by the proved cylinder retraction.
The target space is arbitrary. Boundary values remain exact throughout,
which is the data needed to attach successive cellwise lifting homotopies.
-/

noncomputable section

open Set Metric
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem retraction_bottom (u : Disk (E := E)) : retraction (0, u) = bottomMap u :=
  Subtype.ext (retraction_fixed (0, u) (Or.inl rfl))

theorem retraction_side (p : I × Sphere (E := E)) :
    retraction (p.1, boundaryToDisk p.2) = sideMap p :=
  Subtype.ext (retraction_fixed (p.1, boundaryToDisk p.2)
    (Or.inr (mem_sphere_zero_iff_norm.mp p.2.property)))

variable [FiniteDimensional ℝ E] {X : Type*} [TopologicalSpace X]
  (f : C(Disk (E := E), X)) (G : C(I × Sphere (E := E), X))
  (h0 : ∀ u, G (0, u) = f (boundaryToDisk u))

/-- A jointly continuous extension on the whole original disk cylinder. -/
def extend : C(I × Disk (E := E), X) := (gluedBottomSide f G h0).comp retraction

@[simp] theorem extend_bottom (u : Disk (E := E)) : extend f G h0 (0, u) = f u := by
  change gluedBottomSide f G h0 (retraction (0, u)) = f u
  rw [retraction_bottom, gluedBottomSide_bottom]

@[simp] theorem extend_side (t : I) (u : Sphere (E := E)) :
    extend f G h0 (t, boundaryToDisk u) = G (t, u) := by
  change gluedBottomSide f G h0 (retraction (t, boundaryToDisk u)) = G (t, u)
  rw [retraction_side (t, u), gluedBottomSide_side]

def extensionEndpoint : C(Disk (E := E), X) :=
  (extend f G h0).comp ⟨fun u => (1, u), continuous_const.prodMk continuous_id⟩

/-- The native homotopy with its original bottom map and the constructed endpoint. -/
def extensionHomotopy : f.Homotopy (extensionEndpoint f G h0) where
  toContinuousMap := extend f G h0
  map_zero_left := extend_bottom f G h0
  map_one_left _ := rfl

@[simp] theorem extensionEndpoint_boundary (u : Sphere (E := E)) :
    extensionEndpoint f G h0 (boundaryToDisk u) = G (1, u) := extend_side f G h0 1 u

include h0 in
/-- Every prescribed boundary path is retained at every time, not just up to homotopy. -/
theorem exists_disk_homotopy_extension :
    ∃ H : C(I × Disk (E := E), X),
      (∀ u, H (0, u) = f u) ∧ ∀ t u, H (t, boundaryToDisk u) = G (t, u) :=
  ⟨extend f G h0, extend_bottom f G h0, extend_side f G h0⟩

end Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder
