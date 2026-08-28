import Wikipedia.HopfProblem.DegreeCollapseSevenAttachingCollarSheet
import Wikipedia.HopfProblem.DegreeCollapseSevenUnroundedTraceSupport

/-!
# The exact concave-corner domain in the common smooth collar sheet

In a uniform band around height zero the actual compact attachment contains
a sheet point exactly when its height is nonnegative or its transverse
coordinate is in the half-radius handle. Compact separation excludes the
inner handle image; the original tube's injectivity controls the collar.
This identifies the domain that must be rounded, not a rounded boundary.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f)

theorem radialPoint_mem_collar (s : Sphere 3) {t : ℝ}
    (hlo : A.innerRadius ^ 2 - 1 ≤ t) (hti : t ≤ 0) :
    RadialHeightCoordinates.point (s, t) ∈ closedBall (0 : Vector 4) 1 ∧
      A.innerRadius ≤ ‖RadialHeightCoordinates.point (s, t)‖ := by
  have ht : -1 < t := by nlinarith [A.innerRadius_pos]
  have hsq : ‖RadialHeightCoordinates.point (s, t)‖ ^ 2 = 1 + t := by
    rw [RadialHeightCoordinates.norm_point, Real.sq_sqrt (by linarith)]
  have hn := norm_nonneg (RadialHeightCoordinates.point (s, t))
  constructor
  · rw [mem_closedBall, dist_zero_right]
    nlinarith
  · nlinarith [A.innerRadius_pos]

theorem radialPoint_norm_gt (s : Sphere 3) {t : ℝ}
    (hlo : A.innerRadius ^ 2 - 1 < t) :
    A.innerRadius < ‖RadialHeightCoordinates.point (s, t)‖ := by
  have ht : -1 < t := by nlinarith [A.innerRadius_pos]
  have hsq : ‖RadialHeightCoordinates.point (s, t)‖ ^ 2 = 1 + t := by
    rw [RadialHeightCoordinates.norm_point, Real.sq_sqrt (by linarith)]
  nlinarith [norm_nonneg (RadialHeightCoordinates.point (s, t)), A.innerRadius_pos]

theorem map_radialPoint_eq_sheet (s : Sphere 3) {v : Vector 4}
    (hv : v ∈ closedBall (0 : Vector 4) A.radius) {t : ℝ}
    (hlo : A.innerRadius ^ 2 - 1 ≤ t) (hti : t ≤ 0) :
    A.map (RadialHeightCoordinates.point (s, t), v) = A.collarSheet ((s, v), t) := by
  have ht : -1 < t := by nlinarith [A.innerRadius_pos]
  have hx := A.radialPoint_mem_collar s hlo hti
  rw [A.collar_map _ hx.1 hx.2 v hv, RadialHeightCoordinates.retract_point (pole 3) ht,
    RadialHeightCoordinates.definingFunction_point ht]
  rfl

theorem frame_radialPoint_eq_sheet (s : Sphere 3) {v : Vector 4}
    (hv : v ∈ closedBall (0 : Vector 4) A.radius) {t : ℝ}
    (hlo : A.innerRadius ^ 2 - 1 ≤ t) (hti : t ≤ 0) :
    A.normalFrame (RadialHeightCoordinates.point (s, t), v) =
      A.collarSheetFrame ((s, v), t) := by
  have ht : -1 < t := by nlinarith [A.innerRadius_pos]
  have hx := A.radialPoint_mem_collar s hlo hti
  rw [A.collar_frame _ hx.1 hx.2 v hv, RadialHeightCoordinates.retract_point (pole 3) ht]
  rfl

variable [CompactSpace M]

theorem exists_cornerHeightBand :
    ∃ δ : ℝ, 0 < δ ∧ δ < UnroundedTrace.height A ∧ δ < 1 - A.innerRadius ^ 2 ∧
      ∀ s : Sphere 3, ∀ v ∈ ball (0 : Vector 4) A.radius, ∀ t : ℝ, ‖t‖ ≤ δ →
        (A.collarSheet ((s, v), t) ∈ UnroundedTrace.ambientSet A ↔
          0 ≤ t ∨ v ∈ closedBall (0 : Vector 4) (UnroundedTrace.handleRadius A)) := by
  obtain ⟨ε, hε, havoid⟩ := A.exists_heightCylinder_avoids_inner
  have hgap : 0 < 1 - A.innerRadius ^ 2 := by
    nlinarith [A.innerRadius_pos, A.innerRadius_lt_one]
  let δ := min (ε / 2) (min (UnroundedTrace.height A / 2) ((1 - A.innerRadius ^ 2) / 2))
  have hδ : 0 < δ :=
    lt_min (half_pos hε) (lt_min (half_pos (UnroundedTrace.height_pos A)) (half_pos hgap))
  have hδε : δ ≤ ε := (min_le_left _ _).trans (half_le_self hε.le)
  have hδH : δ < UnroundedTrace.height A :=
    ((min_le_right _ _).trans (min_le_left _ _)).trans_lt
      (half_lt_self (UnroundedTrace.height_pos A))
  have hδgap : δ < 1 - A.innerRadius ^ 2 :=
    ((min_le_right _ _).trans (min_le_right _ _)).trans_lt (half_lt_self hgap)
  refine ⟨δ, hδ, hδH, hδgap, ?_⟩
  intro s v hv t ht
  have htδ : -δ ≤ t ∧ t ≤ δ := abs_le.mp (by simpa only [Real.norm_eq_abs] using ht)
  have hvA := ball_subset_closedBall hv
  constructor
  · rintro (⟨q, hq⟩ | ⟨p, hp⟩)
    · have he : (q.1, q.2.val) = (A.tube (s, v), t) := (HeightCylinder.injective_heightCylinder e) hq
      have htq : q.2.val = t := congrArg (Prod.snd : M × ℝ → ℝ) he
      exact Or.inl (htq ▸ q.2.property.1)
    · have hvp := UnroundedTrace.handle_vector_mem A p
      have hxr : A.innerRadius ≤ ‖p.1.val‖ := by
        by_contra hn
        have hxinner : p.1.val ∈ closedBall (0 : Vector 4) A.innerRadius := by
          simpa only [mem_closedBall, dist_zero_right] using (lt_of_not_ge hn).le
        exact havoid p.1.val hxinner p.2.val hvp (A.tube (s, v)) t (ht.trans hδε) hp
      have hec : (HeightCylinder.heightCylinder e) (A.collarCoordinates (p.1.val, p.2.val)) =
          (HeightCylinder.heightCylinder e) (A.tube (s, v), t) :=
        (A.map_eq_cylinder_collarCoordinates p.1.property hxr hvp).symm.trans hp
      have he := (HeightCylinder.injective_heightCylinder e) hec
      have hm : A.tube (SphereRadialRetraction.retract (pole 3) p.1.val, p.2.val) =
          A.tube (s, v) := congrArg (Prod.fst : M × ℝ → M) he
      have htube :
          (SphereRadialRetraction.retract (pole 3) p.1.val, ⟨p.2.val, hvp⟩) =
            (s, (⟨v, hvA⟩ : closedBall (0 : Vector 4) A.radius)) :=
        A.tube_embedded.injective hm
      have hvp' : p.2.val = v := congrArg
        (fun z : Sphere 3 × closedBall (0 : Vector 4) A.radius ↦ z.2.val) htube
      exact Or.inr (hvp' ▸ p.2.property)
  · intro hp
    by_cases hti : 0 ≤ t
    · exact Or.inl ⟨(A.tube (s, v), ⟨t, hti, htδ.2.trans hδH.le⟩), rfl⟩
    · have hvhalf := hp.resolve_left hti
      have hlo : A.innerRadius ^ 2 - 1 ≤ t := by linarith [htδ.1]
      have hx := A.radialPoint_mem_collar s hlo (le_of_not_ge hti)
      refine Or.inr ⟨(⟨RadialHeightCoordinates.point (s, t), hx.1⟩, ⟨v, hvhalf⟩), ?_⟩
      exact A.map_radialPoint_eq_sheet s hvA hlo (le_of_not_ge hti)

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct
