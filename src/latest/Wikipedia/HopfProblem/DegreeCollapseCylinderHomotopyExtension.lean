import Wikipedia.HopfProblem.DegreeCollapseCylinderBall

/-!
# Homotopy extension on the full boundary of a disk cylinder

Transport the proved disk HEP through the actual cylinder-ball and boundary
homeomorphisms. This permits correcting a comparison homotopy's side family
while preserving its bottom and top whenever the prescribed correction does.
No connectivity premise or dimension bound is needed.
-/

noncomputable section

open Set Metric
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.CylinderHEP

open DiskCylinder CylinderBall

variable {V Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace Y]

/-- Any full boundary homotopy extends to a homotopy of the whole cylinder. -/
theorem exists_extension (f : C(I × Disk (E := V), Y))
    (J : C(I × boundary (V := V), Y)) (h0 : ∀ p, J (0, p) = f p.val) :
    ∃ K : C(I × (I × Disk (E := V)), Y),
      (∀ p, K (0, p) = f p) ∧
      ∀ (t : I) (p : boundary (V := V)), K (t, p.val) = J (t, p) := by
  let e := homeomorph (V := V)
  let b := boundaryHomeomorph (V := V)
  let f' : C(Disk (E := ℝ × V), Y) := f.comp (e.symm : C(_, _))
  let J' : C(I × Sphere (E := ℝ × V), Y) :=
    J.comp ((ContinuousMap.id I).prodMap (b.symm : C(_, _)))
  have h0' : ∀ s, J' (0, s) = f' (boundaryToDisk s) := fun s => h0 (b.symm s)
  let H := DiskCylinder.extend f' J' h0'
  let K : C(I × (I × Disk (E := V)), Y) :=
    H.comp ((ContinuousMap.id I).prodMap (e : C(_, _)))
  refine ⟨K, ?_, ?_⟩
  · intro p
    change H (0, e p) = f p
    exact (DiskCylinder.extend_bottom f' J' h0' (e p)).trans
      (congrArg f (e.symm_apply_apply p))
  · intro t p
    change H (t, boundaryToDisk (b p)) = J (t, p)
    exact (DiskCylinder.extend_side f' J' h0' t (b p)).trans
      (congrArg (fun p => J (t, p)) (b.symm_apply_apply p))

end Wikipedia.HopfProblem.DegreeCollapse.CylinderHEP
