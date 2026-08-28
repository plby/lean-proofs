import Wikipedia.HopfProblem.DegreeCollapseLowBoundaryTransverse

/-!

# Constructed low-surgery products retain exact radial transverse collars

The actual boundary complement is the stabilized internal normal space.
Its radial pullback remains in the actual disk-and-frame complement on the
whole retained collar. Relative smoothing installs those exact columns and
rebuilds the embedded framed product without changing the disk or core frame.
The original native sphere supplies all disk and product data.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : NoExoticSixSphere.Sphere d → M) (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s))
  {b : NoExoticSixSphere.Sphere d}
  (D : CollaredFramedDisk b (e.toFun ∘ f) (fun s => a.orthonormal (f s)))
  (A : LowFramedProduct.FramedProduct (q := 7 - d) D.map D.frame)

include hf hd in
theorem range_transverseExtension_le_complement
    {x : Vector (d + 1)} (hxV : x ∈ D.collarSet) (hx : (1 / 2 : ℝ) < ‖x‖)
    (hTx : D.frame x = boundaryFrameOperator d
      (a.orthonormal (f (SphereRadialRetraction.retract b x))).val) :
    (A.transverseExtension b x).range ≤
      (OperatorSum.operator (D.frame x) (fderiv ℝ D.map x)).rangeᗮ := by
  let s := SphereRadialRetraction.retract b x
  have hW : sphereNormalSpace e f s = (a.orthonormal (f s)).val.rangeᗮ ⊓
      (mfderiv (𝓡 d) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).rangeᗮ := by
    rw [a.orthonormal_range, e.range_normalProjection]
    change sphereNormalSpace e f s = (e.tangentImage (f s))ᗮᗮ ⊓ _
    rw [Submodule.orthogonal_orthogonal]
    rfl
  rw [A.transverseExtension_eq_radial b hx,
    transverse_range_boundary e a f hf hd D.toFramedDisk A, hTx]
  change (sphereNormalSpace e f s).map _ ≤ _
  rw [hW]
  exact map_normal_le_combined_orthogonal_radial b (e.toFun ∘ f) (e.smooth.comp hf)
    D.collar_open D.collar_eq hxV hx (a.orthonormal (f s)).val

include hf hd in
theorem exists_radialTransverseProduct (hsmall : d ≤ 3) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      ∃ A' : LowFramedProduct.FramedProduct (q := 7 - d) D.map D.frame,
        (∀ s : NoExoticSixSphere.Sphere d, A'.transverse s.val = A.transverse s.val) ∧
        ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, r ≤ ‖x‖ →
          D.map x = collar b (e.toFun ∘ f) x ∧
          D.frame x = boundaryFrameOperator d
            (a.orthonormal (f (SphereRadialRetraction.retract b x))).val ∧
          A'.transverse x = A'.transverse (SphereRadialRetraction.retract b x).val := by
  let U := D.collarSet ∩ {x : Vector (d + 1) | max D.collarRadius (1 / 2) < ‖x‖}
  have hU : IsOpen U := D.collar_open.inter (isOpen_lt continuous_const continuous_norm)
  have hSU : sphere (0 : Vector (d + 1)) 1 ⊆ U := by
    intro x hx
    refine ⟨D.boundary_in_collar hx, ?_⟩
    have hn : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
    change max D.collarRadius (1 / 2) < ‖x‖
    rw [hn]
    exact max_lt D.collarRadius_lt_one (by norm_num)
  have hhalf (x : Vector (d + 1)) (hx : x ∈ U) : (1 / 2 : ℝ) < ‖x‖ :=
    lt_of_le_of_lt (le_max_right _ _) hx.2
  have hr₀x (x : Vector (d + 1)) (hx : x ∈ U) : D.collarRadius ≤ ‖x‖ :=
    (le_max_left _ _).trans hx.2.le
  have hFn (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1 ∩ U)
      (w : Vector (7 - d)) : ‖A.transverseExtension b x w‖ = ‖w‖ :=
    A.norm_transverseExtension b (hhalf x hx.2) w
  have hFr (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1 ∩ U) :
      (A.transverseExtension b x).range ≤
        (OperatorSum.operator (D.frame x) (fderiv ℝ D.map x)).rangeᗮ :=
    range_transverseExtension_le_complement e a f hf hd D A hx.2.1 (hhalf x hx.2)
      (D.frame_radial x hx.1 (hr₀x x hx.2))
  have hDi : InjOn D.map (closedBall (0 : Vector (d + 1)) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val
      (D.embedded.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hN : ((e.ambientDimension - 7) + (1 + (d + 1))) + (d + 1) + (7 - d) =
      e.ambientDimension + (1 + (1 + (d + 1))) := by
    have := e.dimension_le_ambient (f b)
    omega
  obtain ⟨r, hr, hr1, hrU, A', hAb, hAc⟩ := A.exists_framedProduct_collar
    (fun _ _ ↦ D.smooth.contDiffAt) D.immersive (A.transverseExtension b)
    (A.contDiff_transverseExtension b) (A.transverseExtension_coe b)
    hU hSU hFn hFr hDi hN
  refine ⟨r, hr, hr1, A', hAb, ?_⟩
  intro x hx hxr
  have hxU := hrU ⟨hx, hxr⟩
  refine ⟨D.collar_eq hxU.1, D.frame_radial x hx (hr₀x x hxU), ?_⟩
  exact (hAc x hx hxr).trans ((A.transverseExtension_eq_radial b (hhalf x hxU)).trans
    (hAb (SphereRadialRetraction.retract b x)).symm)

theorem exists_native_radialProduct {d : ℕ} (hdim : 0 < d) (hsmall : d ≤ 3)
    {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
    (e : EuclideanEmbedding 7 M)
    (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
    (f : NoExoticSixSphere.Sphere d → M)
    (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f) (hi : Injective f)
    (hdf : ∀ s, Injective (mfderiv (𝓡 d) (𝓡 7) f s)) :
    ∃ D : CollaredFramedDisk (spherePole d)
        (e.toFun ∘ f) (fun s => a.orthonormal (f s)),
      ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        ∃ A : LowFramedProduct.FramedProduct (q := 7 - d) D.map D.frame,
          ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, r ≤ ‖x‖ →
            D.map x = collar (spherePole d) (e.toFun ∘ f) x ∧
            D.frame x = boundaryFrameOperator d
              (a.orthonormal (f (SphereRadialRetraction.retract (spherePole d) x))).val ∧
            A.transverse x =
              A.transverse (SphereRadialRetraction.retract (spherePole d) x).val := by
  obtain ⟨D, ⟨A⟩⟩ := exists_native_eightDimensionalProduct hdim hsmall e a f hf hi hdf
  obtain ⟨r, hr, hr1, A', _, hA'⟩ :=
    exists_radialTransverseProduct e a f hf hdf D A hsmall
  exact ⟨D, r, hr, hr1, A', hA'⟩

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
