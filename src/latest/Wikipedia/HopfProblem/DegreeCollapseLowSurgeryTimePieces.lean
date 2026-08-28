import Wikipedia.HopfProblem.DegreeCollapseLowSurgeryTimeFunction

/-!

# Exact time formulas on the three original native boundary pieces

On the entire retained cylinder part the new time is the original profile,
including its overlap with the cap. On both handle and rounded collar
boundary pieces it is exactly one. These are formulas on the original
native open cover, which will establish smoothness in the existing atlas.
-/

noncomputable section

open Function Set Metric Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.NativeSurgery

open NoExoticSixSphere GLOrthonormalization RoundedTrace SurgeryPair

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [CompactSpace M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M} (A : FramedAttachingProduct e a f)
  (hR : A.radius = 2) (T : TimeData A)

include hR in
theorem oldProfile_of_cap_at_bottom (p : CapDomain d) (m : M)
    (h : capPoint A p = LowHeightCylinder.heightCylinder d e (m, 0)) :
    oldProfile A T m = 1 := by
  by_cases hp : ‖capDisk A p‖ ≤ cutRadius A
  · rw [capPoint_of_inner A p hp] at h
    exact (capInner_ne_bottom A hR p hp m h).elim
  · have hp' := (lt_of_not_ge hp).le
    rw [capPoint_of_outer A hR p hp'] at h
    have hc : (A.tube (capCollar A p).1, (capCollar A p).2) = (m, 0) :=
      (LowHeightCylinder.injective_heightCylinder d e) h
    have hm : A.tube (capCollar A p).1 = m := congrArg Prod.fst hc
    rw [← hm]
    exact oldProfile_tube A T (capCollar A p).1.1 (capCollar A p).1.2
      (ball_subset_closedBall (capCollar_mem A hR p hp').1)

variable [IsManifold (𝓡 7) ∞ M]

theorem timeFunction_nativeExterior (m : retainedExterior A) :
    timeFunction A hR T (exteriorNativeHomeomorph A m).val = oldProfile A T m.val := by
  let y := (exteriorNativeHomeomorph A m).val
  have hy : y ∈ range (newExterior A) ∪ range (nativeCapPoint A hR) := by
    rw [new_cover A hR]
    trivial
  rcases hy with ⟨r, hr⟩ | ⟨p, hp⟩
  · have ha := congrArg (fun z : otherBoundaryPart A ↦ z.val.val.val) hr
    change LowHeightCylinder.heightCylinder d e (r.val, 0) =
      LowHeightCylinder.heightCylinder d e (m.val, 0) at ha
    have hm : r.val = m.val :=
      congrArg Prod.fst ((LowHeightCylinder.injective_heightCylinder d e) ha)
    change timeFunction A hR T y = _
    rw [← hr, timeFunction_exterior, hm]
  · have ha := congrArg (fun z : otherBoundaryPart A ↦ z.val.val.val) hp
    rw [nativeCapPoint_ambient] at ha
    change capPoint A p = LowHeightCylinder.heightCylinder d e (m.val, 0) at ha
    change timeFunction A hR T y = _
    rw [← hp, timeFunction_cap]
    exact (oldProfile_of_cap_at_bottom A hR T p m.val ha).symm

theorem timeFunction_cylinder (p : bottomCylinderBoundaryPart A) :
    timeFunction A hR T (nativeExteriorReorder A p).val =
      oldProfile A T (cylinderBoundaryCoordinates A p.val).1 := by
  have h := timeFunction_nativeExterior A hR T
    ((exteriorNativeHomeomorph A).symm (nativeExteriorReorder A p))
  rw [Homeomorph.apply_symm_apply] at h
  exact h

theorem timeFunction_handle (y : otherBoundaryPart A)
    (hy : y.val ∈ boundaryPieceDomain A .handle) : timeFunction A hR T y = 1 := by
  obtain ⟨p, rfl⟩ := handle_new_cover A hR y hy
  exact timeFunction_cap A hR T p

theorem timeFunction_collar (y : otherBoundaryPart A)
    (hy : y.val ∈ boundaryPieceDomain A .collar) : timeFunction A hR T y = 1 := by
  let bp : boundaryPieceDomain A .collar := ⟨y.val, hy⟩
  let q : collarPart A := boundaryTracePoint A .collar bp
  let p : collarParameters A := (collarHomeomorph A).symm q
  have he : A.collarSheet p.val = y.val.val.val := collarHomeomorph_symm_ambient A q
  have hc : y ∈ range (newExterior A) ∪ range (nativeCapPoint A hR) := by
    rw [new_cover A hR]
    trivial
  rcases hc with ⟨r, hr⟩ | ⟨c, hc⟩
  · have ha : LowHeightCylinder.heightCylinder d e (A.tube p.val.1, p.val.2) =
        LowHeightCylinder.heightCylinder d e (r.val, 0) :=
      he.trans (congrArg (fun z : otherBoundaryPart A ↦ z.val.val.val) hr).symm
    have hm : A.tube p.val.1 = r.val :=
      congrArg Prod.fst ((LowHeightCylinder.injective_heightCylinder d e) ha)
    rw [← hr, timeFunction_exterior, ← hm]
    exact oldProfile_tube A T p.val.1.1 p.val.1.2 (ball_subset_closedBall p.property.1)
  · rw [← hc, timeFunction_cap]

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery.FramedAttachingProduct.NativeSurgery
