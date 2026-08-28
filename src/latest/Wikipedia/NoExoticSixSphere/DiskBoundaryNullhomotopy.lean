import Wikipedia.HopfProblem.DegreeCollapseDiskCone

/-!
# Exact disk extension and based boundary nullhomotopy

An extension contracts its boundary toward a selected boundary point along
straight segments inside the actual closed ball. The selected point stays
fixed. Conversely the genuine disk-cone quotient extends a nullhomotopy,
with exactly the prescribed sphere values.
-/

noncomputable section

open Set Metric
open scoped unitInterval

namespace NoExoticSixSphere.DiskBoundary

open Wikipedia.HopfProblem.DegreeCollapse
open DiskCylinder

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def segment (b : Disk (E := E)) : C(unitInterval × Disk (E := E), Disk (E := E)) where
  toFun z := ⟨(1 - (z.1 : ℝ)) • z.2.val + (z.1 : ℝ) • b.val,
    (convex_closedBall (0 : E) 1) z.2.property b.property
      (sub_nonneg.mpr z.1.property.2) z.1.property.1 (sub_add_cancel 1 (z.1 : ℝ))⟩
  continuous_toFun :=
    (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp continuous_snd)).add
        ((continuous_subtype_val.comp continuous_fst).smul continuous_const)).subtype_mk _

theorem segment_zero (b z : Disk (E := E)) : segment b (0, z) = z := by
  apply Subtype.ext
  change (1 - (0 : ℝ)) • z.val + (0 : ℝ) • b.val = z.val
  simp

theorem segment_one (b z : Disk (E := E)) : segment b (1, z) = b := by
  apply Subtype.ext
  change (1 - (1 : ℝ)) • z.val + (1 : ℝ) • b.val = b.val
  simp

theorem segment_fixed (b : Disk (E := E)) (t : unitInterval) : segment b (t, b) = b := by
  apply Subtype.ext
  change (1 - (t : ℝ)) • b.val + (t : ℝ) • b.val = b.val
  rw [← add_smul, sub_add_cancel, one_smul]

variable {X : Type*} [TopologicalSpace X]

def contraction (F : C(Disk (E := E), X)) (b : DiskCylinder.Sphere (E := E)) :
    (F.comp boundaryToDisk).HomotopyRel
      (ContinuousMap.const _ (F (boundaryToDisk b))) {b} where
  toFun z := F (segment (boundaryToDisk b) (z.1, boundaryToDisk z.2))
  continuous_toFun := F.continuous.comp ((segment (boundaryToDisk b)).continuous.comp
    (continuous_fst.prodMk (boundaryToDisk.continuous.comp continuous_snd)))
  map_zero_left z := by rw [segment_zero]; rfl
  map_one_left z := by rw [segment_one]; rfl
  prop' t z hz := by
    have hz' : z = b := hz
    subst z
    change F (segment (boundaryToDisk b) (t, boundaryToDisk b)) = F (boundaryToDisk b)
    rw [segment_fixed]

variable [FiniteDimensional ℝ E]

theorem exists_extension_of_homotopic {f g : C(DiskCylinder.Sphere (E := E), X)}
    (h : f.Homotopic g) (F : C(Disk (E := E), X))
    (hF : ∀ s, F (boundaryToDisk s) = f s) :
    ∃ G : C(Disk (E := E), X), ∀ s, G (boundaryToDisk s) = g s := by
  obtain ⟨H⟩ := h
  let Hc := H.toContinuousMap
  have hzero (s : DiskCylinder.Sphere (E := E)) : Hc (0, s) = F (boundaryToDisk s) :=
    (H.apply_zero s).trans (hF s).symm
  refine ⟨extensionEndpoint F Hc hzero, ?_⟩
  intro s
  exact (extensionEndpoint_boundary F Hc hzero s).trans (H.apply_one s)

theorem exists_extension_iff (b : DiskCylinder.Sphere (E := E))
    (f : C(DiskCylinder.Sphere (E := E), X)) :
    (∃ F : C(Disk (E := E), X), ∀ s, F (boundaryToDisk s) = f s) ↔
      f.HomotopicRel (ContinuousMap.const _ (f b)) {b} := by
  constructor
  · rintro ⟨F, hF⟩
    have he : F.comp boundaryToDisk = f := ContinuousMap.ext hF
    have hc : ContinuousMap.const (DiskCylinder.Sphere (E := E)) (F (boundaryToDisk b)) =
        ContinuousMap.const (DiskCylinder.Sphere (E := E)) (f b) := by rw [hF b]
    exact ⟨(contraction F b).cast he hc⟩
  · rintro ⟨H⟩
    let G := H.toHomotopy.symm.toContinuousMap
    have hzero (s : DiskCylinder.Sphere (E := E)) : G (0, s) = f b :=
      H.toHomotopy.symm.apply_zero s
    refine ⟨DiskCone.extension b G (f b) hzero, ?_⟩
    intro s
    exact (DiskCone.extension_boundary b G (f b) hzero s).trans
      (H.toHomotopy.symm.apply_one s)

end NoExoticSixSphere.DiskBoundary
