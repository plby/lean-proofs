import Wikipedia.HopfProblem.DegreeCollapseCylinderBoundaryFamilies
import Wikipedia.HopfProblem.DegreeCollapseCylinderHomotopyExtension
import Wikipedia.HopfProblem.DegreeCollapseMappingPaths

/-!
# Restoring an exactly prescribed side homotopy

If a disk homotopy has a side path homotopic to the prescribed one in the
actual continuous-map space, the full cylinder HEP changes its side exactly,
while retaining both endpoints. The path homotopy keeps its endpoints fixed.
-/

noncomputable section

open Set Metric
open scoped unitInterval

namespace Wikipedia.HopfProblem.DegreeCollapse.SideRectification

open DiskCylinder CylinderBall MappingPaths

variable {V Y : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [TopologicalSpace Y]

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
theorem boundary_cases (p : boundary (V := V)) :
    (∃ z, p = CylinderBoundary.lower (bottomMap z)) ∨
    (∃ z, p = CylinderBoundary.top z) ∨
    ∃ t s, p = CylinderBoundary.lower (sideMap (t, s)) := by
  rcases p with ⟨⟨t, z⟩, ht | ht | hz⟩
  · change t = 0 at ht
    subst t
    exact Or.inl ⟨z, rfl⟩
  · change t = 1 at ht
    subst t
    exact Or.inr (Or.inl ⟨z, rfl⟩)
  · exact Or.inr (Or.inr ⟨t, ⟨z.val, mem_sphere_zero_iff_norm.mpr hz⟩, rfl⟩)

/-- A homotopy of side paths can be realized by changing the interior homotopy only. -/
theorem exists_rectification {f g : C(Disk (E := V), Y)} (P : Path f g)
    {a b : C(Sphere (E := V), Y)} (Q H : Path a b)
    (hP : Over (fun v : C(Disk (E := V), Y) => v.comp boundaryToDisk) P Q)
    (hQ : Q.Homotopic H) :
    ∃ G : C(I × Disk (E := V), Y),
      (∀ z, G (0, z) = f z) ∧ (∀ z, G (1, z) = g z) ∧
      ∀ t s, G (t, boundaryToDisk s) = H t s := by
  obtain ⟨K⟩ := hQ
  have hfa : f.comp boundaryToDisk = a := by simpa using hP 0
  have hgb : g.comp boundaryToDisk = b := by simpa using hP 1
  let side : C(I × (I × Sphere (E := V)), Y) :=
    K.toHomotopy.toContinuousMap.uncurry.comp
      ((Homeomorph.prodAssoc I I (Sphere (E := V))).symm : C(_, _))
  let fb : C(I × Disk (E := V), Y) := f.comp ContinuousMap.snd
  let gt : C(I × Disk (E := V), Y) := g.comp ContinuousMap.snd
  have hs0 : ∀ t s, side (t, 0, s) = fb (t, boundaryToDisk s) := by
    intro t s
    have he : K (t, 0) = a := (K.eq_fst t (by simp)).trans Q.source
    exact (congrArg (fun v => v s) he).trans (ContinuousMap.congr_fun hfa.symm s)
  have hs1 : ∀ t s, side (t, 1, s) = gt (t, boundaryToDisk s) := by
    intro t s
    have he : K (t, 1) = b := (K.eq_fst t (by simp)).trans Q.target
    exact (congrArg (fun v => v s) he).trans (ContinuousMap.congr_fun hgb.symm s)
  let J := CylinderBoundaryFamilies.glued fb gt side hs0 hs1
  have hJ0 : ∀ p : boundary (V := V), J (0, p) = toHomotopy P p.val := by
    intro p
    rcases boundary_cases p with ⟨z, rfl⟩ | ⟨z, rfl⟩ | ⟨t, s, rfl⟩
    · exact (CylinderBoundaryFamilies.glued_bottom fb gt side hs0 hs1 0 z).trans
        (ContinuousMap.congr_fun P.source z).symm
    · exact (CylinderBoundaryFamilies.glued_top fb gt side hs0 hs1 0 z).trans
        (ContinuousMap.congr_fun P.target z).symm
    · exact (CylinderBoundaryFamilies.glued_side fb gt side hs0 hs1 0 t s).trans
        ((congrArg (fun v => v s) (K.apply_zero t)).trans
          (ContinuousMap.congr_fun (hP t) s).symm)
  obtain ⟨W, _, hW⟩ := CylinderHEP.exists_extension (toHomotopy P).toContinuousMap J hJ0
  let G : C(I × Disk (E := V), Y) :=
    W.comp ⟨fun p => (1, p), continuous_const.prodMk continuous_id⟩
  refine ⟨G, ?_, ?_, ?_⟩
  · intro z
    exact (hW 1 (CylinderBoundary.lower (bottomMap z))).trans
      (CylinderBoundaryFamilies.glued_bottom fb gt side hs0 hs1 1 z)
  · intro z
    exact (hW 1 (CylinderBoundary.top z)).trans
      (CylinderBoundaryFamilies.glued_top fb gt side hs0 hs1 1 z)
  · intro t s
    exact (hW 1 (CylinderBoundary.lower (sideMap (t, s)))).trans
      ((CylinderBoundaryFamilies.glued_side fb gt side hs0 hs1 1 t s).trans
        (congrArg (fun v => v s) (K.apply_one t)))

end Wikipedia.HopfProblem.DegreeCollapse.SideRectification
