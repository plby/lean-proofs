import Wikipedia.NoExoticSixSphere.SmoothFramedCollapse

/-!
# Framed collapse data from an actual full-source smooth tube

A round-fiber formula is unnecessary here. The actual smooth partial
inverse, prescribed core, and normal derivative give smooth collapse
coordinates with the correct frame. The collapse map itself is retained.
-/

noncomputable section

open Set
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  (e : EuclideanEmbedding n M)
  (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel)
  (Φ : PartialDiffeomorph ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension)
    (M × e.NormalModel) (EuclideanSpace ℝ (Fin e.ambientDimension)) ∞)
  (hsource : Φ.source = univ) (hcore : ∀ x, Φ (x, 0) = e.toFun x)
  (hnormal : ∀ x, HasFDerivAt (fun v : e.NormalModel ↦ Φ (x, v)) (a.ambient x) 0)

include hsource hcore hnormal in
theorem fderiv_partialTubeCoordinate_comp_frame (x : M) :
    (fderiv ℝ (SmoothCollapseCoordinates.coordinate Φ) (e.toFun x)).comp (a.ambient x) =
      ContinuousLinearMap.id ℝ e.NormalModel := by
  have hy : Φ (x, 0) ∈ Φ.target := Φ.map_source' (by rw [hsource]; trivial)
  have hd := (SmoothCollapseCoordinates.contMDiffAt_coordinate Φ hy).contDiffAt
    |>.differentiableAt (by simp)
  have hc := hd.hasFDerivAt.comp (0 : e.NormalModel) (hnormal x)
  rw [hcore] at hc
  have he : (fun v : e.NormalModel ↦ SmoothCollapseCoordinates.coordinate Φ (Φ (x, v))) = id := by
    funext v
    exact SmoothCollapseCoordinates.coordinate_apply Φ (by rw [hsource]; trivial)
  change HasFDerivAt (fun v : e.NormalModel ↦ SmoothCollapseCoordinates.coordinate Φ (Φ (x, v)))
    ((fderiv ℝ (SmoothCollapseCoordinates.coordinate Φ) (e.toFun x)).comp (a.ambient x)) 0 at hc
  rw [he] at hc
  exact hc.unique (hasFDerivAt_id (0 : e.NormalModel))

variable [CompactSpace M]

def framedCollapseDataOfPartialTube : e.FramedCollapseData a := by
  have hΦ := Φ.toOpenPartialHomeomorph.isOpenEmbedding hsource
  refine {
    radius := 1
    radius_pos := zero_lt_one
    neighborhood := Φ.target
    open_neighborhood := Φ.open_target
    range_subset := ?_
    coordinates := SmoothCollapseCoordinates.coordinate Φ
    smooth_coordinates := (SmoothCollapseCoordinates.contMDiffOn_coordinate Φ).contDiffOn
    surjective_differential := ?_
    differential_frame := ?_
    map := ⟨OpenFiberCollapse.collapseOnePoint Φ,
      OpenFiberCollapse.continuous_collapseOnePoint Φ hΦ⟩
    map_infty := OpenFiberCollapse.collapseOnePoint_infty Φ
    zero_fiber := ?_
    local_formula := fun _ hy ↦
      SmoothCollapseCoordinates.collapseOnePoint_eq_coordinate Φ hsource hy }
  · rintro _ ⟨x, rfl⟩
    rw [← hcore x]
    exact Φ.map_source' (by rw [hsource]; trivial)
  · intro y hy
    have hd := (SmoothCollapseCoordinates.contMDiffAt_coordinate Φ hy).contDiffAt
      |>.differentiableAt (by simp)
    have hsurj := SmoothCollapseCoordinates.mfderiv_coordinate_surjective Φ hy
    rw [hd.hasFDerivAt.hasMFDerivAt.mfderiv] at hsurj
    exact hsurj
  · intro x v
    have h := congrArg (fun L : e.NormalModel →L[ℝ] e.NormalModel ↦ L v)
      (e.fderiv_partialTubeCoordinate_comp_frame a Φ hsource hcore hnormal x)
    simpa only [one_smul, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using h
  · intro y
    change OpenFiberCollapse.collapseOnePoint Φ y = (↑(0 : e.NormalModel)) ↔ _
    rw [OpenFiberCollapse.collapseOnePoint_eq_coe_iff Φ hΦ.injective]
    simp only [hcore]

theorem framedCollapseDataOfPartialTube_map
    (z : OnePoint (EuclideanSpace ℝ (Fin e.ambientDimension))) :
    (e.framedCollapseDataOfPartialTube a Φ hsource hcore hnormal).map z =
      OpenFiberCollapse.collapseOnePoint Φ z := rfl

end NoExoticSixSphere.EuclideanEmbedding
