import Wikipedia.SmoothSixDPoincare.ShrunkMorseSurgery

/-!
# Exact common-face coordinates for the smaller surgery presentation

The radial face change is fixed on its sphere. Thus shrinking carries the
common face to the original belt coordinates with normal vector `s • u`.
The exhaustive cover then identifies maps meeting the tube only on this
face as maps into the actual common exterior.
-/

noncomputable section

open Set Metric Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.ShrunkSurgeryRealization

open PuncturedHandle

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] {f : M → ℝ} {p : M}
  {d : MorseSurgeryData E f p} {s : ℝ} (R : d.ShrunkSurgeryRealization s)

/-- Only the new boundary is moved; the old exterior and attaching map are unchanged. -/
abbrev surgery := d.surgery.changeNewBoundary R.boundaryHomeomorph

open Classical in
/-- The refined exterior is exactly the image of the original exterior point
under this same whole-attachment homeomorphism. -/
theorem attachmentHomeomorph_exterior (r) :
    (R.attachmentHomeomorph ⟨(R.surgery.oldExterior r : M),
      Or.inl (R.surgery.oldExterior r).property.le⟩).val = (R.surgery.newExterior r : M) := by
  have harg : (⟨(R.surgery.oldExterior r : M),
      Or.inl (R.surgery.oldExterior r).property.le⟩ :
        ↥({x : M | f x ≤ f p - d.radius ^ 2} ∪
          range (d.chart.attachingHandleMap d.radius d.radius_pos d.block))) =
      ⟨r.val, Or.inl r.property.1.le⟩ := Subtype.ext (d.oldExterior_eq r)
  rw [harg]
  exact (R.newExterior_eq r).symm

open Classical in
/-- Any lower thickening transported through the actual common exterior
retains its point map under the original whole-sublevel realization. -/
theorem attachmentHomeomorph_lowerExteriorMap {Z : Type*}
    (L : Z → d.LowerLevel) (g : Z → d.UpperLevel)
    (hlinks : ∀ z, ∃ r, R.surgery.newExterior r = g z ∧ R.surgery.oldExterior r = L z)
    (z : Z) :
    (R.attachmentHomeomorph ⟨(L z : M), Or.inl (L z).property.le⟩).val = (g z : M) := by
  obtain ⟨r, hr, hL⟩ := hlinks z
  have harg : (⟨(L z : M), Or.inl (L z).property.le⟩ :
      ↥({x : M | f x ≤ f p - d.radius ^ 2} ∪
        range (d.chart.attachingHandleMap d.radius d.radius_pos d.block))) =
      ⟨(R.surgery.oldExterior r : M), Or.inl (R.surgery.oldExterior r).property.le⟩ :=
    Subtype.ext (congrArg (fun x : d.LowerLevel => (x : M)) hL).symm
  rw [harg]
  exact (R.attachmentHomeomorph_exterior r).trans
    (congrArg (fun x : d.UpperLevel => (x : M)) hr)

open Classical in
theorem newPiece_boundary_coe
    (u : UnitSphere d.chart.NegativeCoordinates) (v : UnitSphere d.chart.PositiveCoordinates) :
    (R.surgery.newPiece (sphereToBall u, v) : M) =
      d.chart.splitChart.symm (d.chart.beltRawCoordinates d.radius (v, s • u.val)) := by
  have hfix : d.beltFaceCoordinates (sphereToBall u) = sphereToBall u :=
    d.beltFaceCoordinates_boundary _ (mem_sphere_zero_iff_norm.mp u.property)
  have hpoint := d.newPiece_beltFaceCoordinates (sphereToBall u) v
  rw [hfix] at hpoint
  change (R.boundaryHomeomorph (d.surgery.newPiece (sphereToBall u, v)) : M) = _
  rw [hpoint]
  exact R.scales_disk (sphereToBall u) v

open Classical in
/-- The same point is parametrized by the actual new-exterior boundary map. -/
theorem newExterior_boundary_coe
    (u : UnitSphere d.chart.NegativeCoordinates) (v : UnitSphere d.chart.PositiveCoordinates) :
    (R.surgery.newExterior (R.surgery.boundary (u, v)) : M) =
      d.chart.splitChart.symm (d.chart.beltRawCoordinates d.radius (v, s • u.val)) := by
  have hpoint : R.surgery.newExterior (R.surgery.boundary (u, v)) =
      R.surgery.newPiece (newBoundary (u, v)) :=
    (R.surgery.new_overlap _ _).mpr ⟨(u, v), rfl, rfl⟩
  exact (congrArg (fun y : d.UpperLevel => (y : M)) hpoint).trans
    (R.newPiece_boundary_coe u v)

open Classical in
theorem oldExterior_boundary
    (u : UnitSphere d.chart.NegativeCoordinates) (v : UnitSphere d.chart.PositiveCoordinates) :
    R.surgery.oldExterior (R.surgery.boundary (u, v)) =
      d.surgery.oldPiece (oldBoundary (u, v)) :=
  (d.surgery.old_overlap _ _).mpr ⟨(u, v), rfl, rfl⟩

open Classical in
/-- A point whose possible tube contact is on the prescribed common face
belongs to the actual new exterior. -/
theorem mem_newExterior_of_tube_boundary {y : d.UpperLevel}
    (hcontact : y ∈ d.closedBeltTube s →
      ∃ (u : UnitSphere d.chart.NegativeCoordinates) (v : UnitSphere d.chart.PositiveCoordinates),
        (y : M) = d.chart.splitChart.symm
          (d.chart.beltRawCoordinates d.radius (v, s • u.val))) :
    y ∈ range R.surgery.newExterior := by
  have hcover : y ∈ range R.surgery.newExterior ∪ range R.surgery.newPiece := by
    rw [R.surgery.new_cover]
    exact mem_univ y
  rcases hcover with h | h
  · exact h
  · have htube : y ∈ d.closedBeltTube s := R.newPiece_range ▸ h
    obtain ⟨u, v, huv⟩ := hcontact htube
    exact ⟨R.surgery.boundary (u, v),
      Subtype.ext ((R.newExterior_boundary_coe u v).trans huv.symm)⟩

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.MorseSurgeryData.ShrunkSurgeryRealization
