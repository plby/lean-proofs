import Wikipedia.HopfProblem.DegreeCollapseLowCollarTransverseDerivative

/-!

# The actual vertical and transverse derivatives across the attaching collar

For the handle comparison the disk coordinate is fixed. Varying only the
transverse vector inside the proved radius gives a genuine open germ of the
collar identity. No extension of the closed-disk identity is assumed.
-/

noncomputable section

open Function Set Metric Filter
open scoped Manifold ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk LowRoundedHandleCorner

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)

theorem heightCylinderDerivative_vertical (p : M × ℝ) (t : ℝ) :
    (LowHeightCylinder.heightCylinderDerivative d e) p (0, t) =
      coordinates e.ambientDimension (d + 1) ((0, t), 0) := by
  rw [(LowHeightCylinder.heightCylinderDerivative_apply d e)]
  let D : Vector 7 →L[ℝ] Vector e.ambientDimension :=
    mfderiv (𝓡 7) (𝓡 e.ambientDimension) e.toFun p.1
  change coordinates e.ambientDimension (d + 1) ((D 0, t), 0) = _
  rw [map_zero]

namespace FramedAttachingProduct

variable {e} {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel}
  {f : NoExoticSixSphere.Sphere d → M}
  (A : FramedAttachingProduct e a f)

theorem collarSheetDerivative_vertical {p : Collar d (7 - d)}
    (hp : p ∈ A.tubeHeightCoordinates.source)
    (t : ℝ) :
    A.collarSheetDerivative p ((0, 0), t) = coordinates e.ambientDimension (d + 1) ((0, t), 0) := by
  let j : ℝ →L[ℝ] ((Vector d × Vector (7 - d)) × ℝ) :=
    (0 : ℝ →L[ℝ] (Vector d × Vector (7 - d))).prod (ContinuousLinearMap.id ℝ ℝ)
  let k : ℝ →L[ℝ] (Vector 7 × ℝ) :=
    (0 : ℝ →L[ℝ] Vector 7).prod (ContinuousLinearMap.id ℝ ℝ)
  have hg : HasMFDerivAt 𝓘(ℝ, ℝ) (collarModel d (7 - d)) (fun z : ℝ ↦ (p.1, z)) p.2 j :=
    (hasMFDerivAt_const p.1 p.2).prodMk (hasMFDerivAt_id p.2)
  have hk : HasMFDerivAt 𝓘(ℝ, ℝ) ((𝓡 7).prod 𝓘(ℝ, ℝ))
      (fun z : ℝ ↦ (A.tube p.1, z)) p.2 k :=
    (hasMFDerivAt_const (A.tube p.1) p.2).prodMk (hasMFDerivAt_id p.2)
  have hs := A.contMDiffOn_collarSheet.contMDiffAt
    (A.tubeHeightCoordinates.open_source.mem_nhds hp)
  have hd : (A.collarSheetDerivative p).comp j =
      ((LowHeightCylinder.heightCylinderDerivative d e) (A.tube p.1, p.2)).comp k := by
    have h₁ := ((hs.mdifferentiableAt (by simp)).hasMFDerivAt.comp p.2 hg).mfderiv
    have h₂ := (((LowHeightCylinder.contMDiff_heightCylinder d e).mdifferentiableAt
      (by simp)).hasMFDerivAt.comp p.2 hk).mfderiv
    exact h₁.symm.trans h₂
  have he := congrArg (fun L : ℝ →L[ℝ] Vector (e.ambientDimension + (1 + (1 + (d + 1)))) ↦ L t) hd
  exact he.trans ((LowSurgery.heightCylinderDerivative_vertical (d := d) e) (A.tube p.1, p.2) t)

theorem map_transverseDerivative_eq_sheet {x : Vector (d + 1)}
    (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) (hi : A.innerRadius ≤ ‖x‖)
    {v : Vector (7 - d)} (hv : v ∈ ball (0 : Vector (7 - d)) A.radius) (w : Vector (7 - d)) :
    fderiv ℝ A.map (x, v) (0, w) =
      A.collarSheetDerivative ((SphereRadialRetraction.retract (spherePole d) x, v), ‖x‖ ^ 2 - 1)
        ((0, w), 0) := by
  let s := SphereRadialRetraction.retract (spherePole d) x
  let t := ‖x‖ ^ 2 - 1
  let p : (Collar d (7 - d)) := ((s, v), t)
  have hp : p ∈ A.tubeHeightCoordinates.source :=
    (A.mem_tubeHeightCoordinates_source p).mpr hv
  let j : Vector (7 - d) →L[ℝ] (Vector (d + 1) × Vector (7 - d)) :=
    (0 : Vector (7 - d) →L[ℝ] Vector (d + 1)).prod (ContinuousLinearMap.id ℝ (Vector (7 - d)))
  let k : Vector (7 - d) →L[ℝ] ((Vector d × Vector (7 - d)) × ℝ) :=
    ((0 : Vector (7 - d) →L[ℝ] Vector d).prod (ContinuousLinearMap.id ℝ (Vector (7 - d)))).prod 0
  have hj : HasFDerivAt (fun z : Vector (7 - d) ↦ (x, z)) j v :=
    (hasFDerivAt_const x v).prodMk (hasFDerivAt_id v)
  have hk : HasMFDerivAt (𝓡 (7 - d)) (collarModel d (7 - d))
      (fun z : Vector (7 - d) ↦ ((s, z), t)) v k :=
    ((hasMFDerivAt_const s v).prodMk (hasMFDerivAt_id v)).prodMk (hasMFDerivAt_const t v)
  have hA := (A.smooth x hx v (ball_subset_closedBall hv)).differentiableAt (by simp)
  have hS := A.contMDiffOn_collarSheet.contMDiffAt
    (A.tubeHeightCoordinates.open_source.mem_nhds hp)
  have he : (fun z : Vector (7 - d) ↦ A.map (x, z)) =ᶠ[𝓝 v]
      (fun z : Vector (7 - d) ↦ A.collarSheet ((s, z), t)) := by
    filter_upwards [isOpen_ball.mem_nhds hv] with z hz
    exact A.collar_map x hx hi z (ball_subset_closedBall hz)
  have hd₁ : fderiv ℝ (fun z : Vector (7 - d) ↦ A.map (x, z)) v =
      (fderiv ℝ A.map (x, v)).comp j := (hA.hasFDerivAt.comp v hj).fderiv
  have hd₂ : fderiv ℝ (fun z : Vector (7 - d) ↦ A.collarSheet ((s, z), t)) v =
      (A.collarSheetDerivative p).comp k := by
    have h := ((hS.mdifferentiableAt (by simp)).hasMFDerivAt.comp v hk).mfderiv
    rw [mfderiv_eq_fderiv] at h
    exact h
  have hd : (fderiv ℝ A.map (x, v)).comp j = (A.collarSheetDerivative p).comp k :=
    hd₁.symm.trans (he.fderiv_eq.trans hd₂)
  exact congrArg (fun L : Vector (7 - d) →L[ℝ]
    Vector (e.ambientDimension + (1 + (1 + (d + 1)))) ↦ L w) hd

end FramedAttachingProduct
end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
