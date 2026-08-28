import Wikipedia.NoExoticSixSphere.ManifoldRadialComplement
import Wikipedia.NoExoticSixSphere.FramedProductCollarReplacement

/-!
# An exactly radial transverse frame on an original manifold's disk collar

Starting from the already collared partial normal frame, replace the transverse
frame and rebuild its embedded product. The boundary transverse frame stays
unchanged. The disk map and both frame families have their prescribed exact
radial values on a single closed inner annulus.
-/

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 6) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 6) f s))
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - 6) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : DiskThickening.FramedProduct D.toFun T)
  (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (e.normalFrameOnSphere a f s).val)

include hf hd hTb in
theorem exists_radialTransverseProduct (r₀ : ℝ) (hr₀ : r₀ < 1)
    (hTc : ∀ x ∈ closedBall (0 : Vector 4) 1, r₀ ≤ ‖x‖ → T x = boundaryFrameOperator
      (e.normalFrameOnSphere a f (SphereRadialRetraction.retract b x)).val) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∃ A' : DiskThickening.FramedProduct D.toFun T,
      (∀ s : Sphere 3, A'.transverse s.val = A.transverse s.val) ∧
      ∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
        D.toFun x = collar b (e.toFun ∘ f) x ∧
        T x = boundaryFrameOperator
          (e.normalFrameOnSphere a f (SphereRadialRetraction.retract b x)).val ∧
        A'.transverse x = A'.transverse (SphereRadialRetraction.retract b x).val := by
  obtain ⟨V, hV, hSV, hDV⟩ := D.collar_eq
  let U := V ∩ {x : Vector 4 | max r₀ (1 / 2) < ‖x‖}
  have hU : IsOpen U := hV.inter (isOpen_lt continuous_const continuous_norm)
  have hSU : sphere (0 : Vector 4) 1 ⊆ U := by
    intro x hx
    refine ⟨hSV hx, ?_⟩
    have hn : ‖x‖ = 1 := by simpa only [mem_sphere, dist_zero_right] using hx
    change max r₀ (1 / 2) < ‖x‖
    rw [hn]
    exact max_lt hr₀ (by norm_num)
  have hhalf (x : Vector 4) (hx : x ∈ U) : (1 / 2 : ℝ) < ‖x‖ :=
    lt_of_le_of_lt (le_max_right _ _) hx.2
  have hr₀x (x : Vector 4) (hx : x ∈ U) : r₀ ≤ ‖x‖ :=
    (le_max_left _ _).trans hx.2.le
  have hFn (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1 ∩ U)
      (w : Vector 3) : ‖A.transverseExtension b x w‖ = ‖w‖ :=
    A.norm_transverseExtension b (hhalf x hx.2) w
  have hFr (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1 ∩ U) :
      (A.transverseExtension b x).range ≤
        (OperatorSum.operator (T x) (fderiv ℝ D.toFun x)).rangeᗮ :=
    e.range_transverseExtension_le_complement a f hf hd D A hTb hV hDV hx.2.1
      (hhalf x hx.2) (hTc x hx.1 (hr₀x x hx.2))
  have hDi : InjOn D.toFun (closedBall (0 : Vector 4) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val
      (D.embedded.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hN : ((e.ambientDimension - 6) + 5) + 4 + 3 = e.ambientDimension + 6 := by
    have := e.dimension_le_ambient (f b)
    omega
  obtain ⟨r, hr, hr1, hrU, A', hAb, hAc⟩ := A.exists_framedProduct_collar
    (fun _ _ ↦ D.smooth.contDiffAt) D.immersive (A.transverseExtension b)
    (A.contDiff_transverseExtension b) (A.transverseExtension_coe b)
    hU hSU hFn hFr hDi hN
  refine ⟨r, hr, hr1, A', hAb, ?_⟩
  intro x hx hxr
  have hxU := hrU ⟨hx, hxr⟩
  refine ⟨hDV hxU.1, hTc x hx (hr₀x x hxU), ?_⟩
  exact (hAc x hx hxr).trans ((A.transverseExtension_eq_radial b (hhalf x hxU)).trans
    (hAb (SphereRadialRetraction.retract b x)).symm)

end NoExoticSixSphere.EuclideanEmbedding
