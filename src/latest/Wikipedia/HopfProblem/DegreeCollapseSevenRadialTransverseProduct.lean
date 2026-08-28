import Wikipedia.HopfProblem.DegreeCollapseSevenBoundaryTransverse
import Wikipedia.NoExoticSixSphere.SmoothSphereRadialCollar
import Wikipedia.NoExoticSixSphere.SmoothFullDiskCollarFrame
import Wikipedia.NoExoticSixSphere.SmoothOperatorComplement
import Wikipedia.NoExoticSixSphere.SpanningDiskRadialComplement

/-!
# SevenRadialTransverseProduct

Replace the transverse frame on a whole inner annulus by its exact radial boundary values in the actual complementary planes. The original disk and partial normal frame remain unchanged, and the framed product is rebuilt with a positive radius.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.EightDimensionalFramedProduct.FramedProduct

open NoExoticSixSphere GLOrthonormalization

variable {N k : ℕ} {D : Vector 4 → Vector (N + 6)}
  {T : Vector 4 → Vector k →L[ℝ] Vector (N + 6)} (A : FramedProduct D T) (b : Sphere 3)

def transverseExtension : C(Vector 4, Vector 4 →L[ℝ] Vector (N + 6)) :=
  ⟨SmoothSphereAmbient.extension b (fun s ↦ A.transverse s.val),
    (SmoothSphereAmbient.contDiff_extension b _ A.contMDiff_transverse_boundary).continuous⟩

theorem contDiff_transverseExtension : ContDiff ℝ ∞ (A.transverseExtension b) :=
  SmoothSphereAmbient.contDiff_extension b _ A.contMDiff_transverse_boundary

theorem transverseExtension_coe (s : Sphere 3) :
    A.transverseExtension b s.val = A.transverse s.val :=
  SmoothSphereAmbient.extension_coe b (fun s ↦ A.transverse s.val) s

theorem transverseExtension_eq_radial {x : Vector 4} (hx : (1 / 2 : ℝ) < ‖x‖) :
    A.transverseExtension b x = A.transverse (SphereRadialRetraction.retract b x).val :=
  SmoothSphereAmbient.extension_eq_radial_of_half_le b (fun s ↦ A.transverse s.val) hx.le

theorem norm_transverseExtension {x : Vector 4} (hx : (1 / 2 : ℝ) < ‖x‖)
    (w : Vector 4) : ‖A.transverseExtension b x w‖ = ‖w‖ := by
  rw [A.transverseExtension_eq_radial b hx]
  exact A.norm_transverse _ (Metric.sphere_subset_closedBall
    (SphereRadialRetraction.retract b x).property) w

end Wikipedia.HopfProblem.DegreeCollapse.EightDimensionalFramedProduct.FramedProduct

noncomputable section

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.EightDimensionalFramedProduct.FramedProduct

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {N k : ℕ} {D : Vector 4 → Vector N}
  {T : Vector 4 → Vector k →L[ℝ] Vector N} (A : FramedProduct D T)
  (hD : ∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ D x)
  (hiD : ∀ x ∈ closedBall (0 : Vector 4) 1, Injective (fderiv ℝ D x))
  (F : C(Vector 4, Vector 4 →L[ℝ] Vector N)) (hFs : ContDiff ℝ ∞ F)
  (hFC : ∀ s : Sphere 3, F s.val = A.transverse s.val)
  {V : Set (Vector 4)} (hV : IsOpen V) (hSV : sphere 0 1 ⊆ V)
  (hFn : ∀ x ∈ closedBall (0 : Vector 4) 1 ∩ V, ∀ w, ‖F x w‖ = ‖w‖)
  (hFr : ∀ x ∈ closedBall (0 : Vector 4) 1 ∩ V,
    (F x).range ≤ (OperatorSum.operator (T x) (fderiv ℝ D x)).rangeᗮ)

include A hD hiD hFs hFC hV hSV hFn hFr

theorem exists_transverseFrame_collar :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ closedBall (0 : Vector 4) 1 ∩ {x | r ≤ ‖x‖} ⊆ V ∧
      ∃ C : Vector 4 → Vector 4 →L[ℝ] Vector N,
        (∀ x ∈ closedBall (0 : Vector 4) 1, ContDiffAt ℝ ∞ C x) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1, ∀ w, ‖C x w‖ = ‖w‖) ∧
        (∀ x ∈ closedBall (0 : Vector 4) 1,
          (C x).range = (OperatorSum.operator (T x) (fderiv ℝ D x)).rangeᗮ) ∧
        ∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ → C x = F x := by
  let B : Vector 4 → Vector (k + 4) →L[ℝ] Vector N :=
    fun x ↦ OperatorSum.operator (T x) (fderiv ℝ D x)
  have hBi (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) : Injective (B x) :=
    OperatorSum.injective_operator _ _ (Stiefel.injective ⟨T x, A.norm_coreFrame x hx⟩)
      (hiD x hx) ((fderiv ℝ D x).range.orthogonal_disjoint.symm.mono_left
        (A.range_coreFrame x hx))
  have hBs (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      ContDiffAt ℝ ∞ B x :=
    OperatorSum.contDiffAt_operator (A.smooth_coreFrame x hx)
      ((hD x hx).fderiv_right (by simp))
  let P := OperatorComplement.projection B
  have hP (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      IsIdempotentElem (P x) := OperatorComplement.idempotent_projection B x (hBi x hx)
  have hPs (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      ContDiffAt ℝ ∞ P x :=
    OperatorComplement.contDiffAt_projection B x (hBs x hx) (hBi x hx)
  have hPr (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      (P x).range = (B x).rangeᗮ := OperatorComplement.range_projection B x (hBi x hx)
  have hCr (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1) :
      (A.transverse x).range = (P x).range := (A.range_transverse x hx).trans (hPr x hx).symm
  have hFr' (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1 ∩ V) :
      (F x).range ≤ (P x).range := by rw [hPr x hx.1]; exact hFr x hx
  obtain ⟨r, hr, hr1, hrV, C, hCs, hCn, hCr', hCF⟩ :=
    exists_smoothFullDiskFrame_collar P hP hPs A.transverse A.smooth_transverse
      A.norm_transverse hCr F hFs hFC hV hSV hFn hFr'
  exact ⟨r, hr, hr1, hrV, C, hCs, hCn,
    fun x hx ↦ (hCr' x hx).trans (hPr x hx), hCF⟩

theorem exists_framedProduct_collar (hinj : InjOn D (closedBall (0 : Vector 4) 1))
    (hN : k + 4 + 4 = N) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ closedBall (0 : Vector 4) 1 ∩ {x | r ≤ ‖x‖} ⊆ V ∧
      ∃ A' : FramedProduct D T,
        (∀ s : Sphere 3, A'.transverse s.val = A.transverse s.val) ∧
        ∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ → A'.transverse x = F x := by
  obtain ⟨r, hr, hr1, hrV, C, hCs, hCn, hCr, hCF⟩ :=
    A.exists_transverseFrame_collar hD hiD F hFs hFC hV hSV hFn hFr
  obtain ⟨A', hAC⟩ := exists_framedProduct_of_transverse D T hD hinj hiD
    A.smooth_coreFrame A.norm_coreFrame A.range_coreFrame hN C hCs hCn hCr
  refine ⟨r, hr, hr1, hrV, A', ?_, ?_⟩
  · intro s
    rw [hAC]
    have hrs : r ≤ ‖s.val‖ := by rw [ClosedHemisphere.unit_norm]; exact hr1.le
    exact (hCF s.val (sphere_subset_closedBall s.property) hrs).trans (hFC s)
  · intro x hx hxr
    rw [hAC]
    exact hCF x hx hxr

end Wikipedia.HopfProblem.DegreeCollapse.EightDimensionalFramedProduct.FramedProduct

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : EightDimensionalFramedProduct.FramedProduct D.toFun T)
  (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (SevenSurgery.normalFrameOnSphere e a f s).val)

include hf hd hTb in
theorem range_transverseExtension_le_complement
    {V : Set (Vector 4)} (hV : IsOpen V)
    (hDV : EqOn D.toFun (collar b (e.toFun ∘ f)) V) {x : Vector 4} (hxV : x ∈ V)
    (hx : (1 / 2 : ℝ) < ‖x‖)
    (hTx : T x = boundaryFrameOperator
      (SevenSurgery.normalFrameOnSphere e a f (SphereRadialRetraction.retract b x)).val) :
    (A.transverseExtension b x).range ≤
      (OperatorSum.operator (T x) (fderiv ℝ D.toFun x)).rangeᗮ := by
  let s := SphereRadialRetraction.retract b x
  have hW : SevenSurgery.sphereNormalSpace e f s = (SevenSurgery.normalFrameOnSphere e a f s).val.rangeᗮ ⊓
      (mfderiv (𝓡 3) (𝓡 e.ambientDimension) (e.toFun ∘ f) s).rangeᗮ := by
    rw [SevenSurgery.normalFrameOnSphere_range e a f s]
    change SevenSurgery.sphereNormalSpace e f s = (e.tangentImage (f s))ᗮᗮ ⊓ _
    rw [Submodule.orthogonal_orthogonal]
    rfl
  rw [A.transverseExtension_eq_radial b hx,
    SevenSurgery.transverse_range_boundary e a f hf hd D A hTb, hTx]
  change (SevenSurgery.sphereNormalSpace e f s).map _ ≤ _
  rw [hW]
  exact map_normal_le_combined_orthogonal_radial b (e.toFun ∘ f) (e.smooth.comp hf)
    hV hDV hxV hx (SevenSurgery.normalFrameOnSphere e a f s).val

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

noncomputable section

open Function Set Metric
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
  (hd : ∀ s, Injective (mfderiv (𝓡 3) (𝓡 7) f s))
  {b : Sphere 3} (D : DiskData b (e.toFun ∘ f))
  {T : Vector 4 → Vector ((e.ambientDimension - 7) + 5) →L[ℝ]
    Vector (e.ambientDimension + 6)}
  (A : EightDimensionalFramedProduct.FramedProduct D.toFun T)
  (hTb : ∀ s : Sphere 3, T s.val = boundaryFrameOperator (SevenSurgery.normalFrameOnSphere e a f s).val)

include hf hd hTb in
theorem exists_radialTransverseProduct (r₀ : ℝ) (hr₀ : r₀ < 1)
    (hTc : ∀ x ∈ closedBall (0 : Vector 4) 1, r₀ ≤ ‖x‖ → T x = boundaryFrameOperator
      (SevenSurgery.normalFrameOnSphere e a f (SphereRadialRetraction.retract b x)).val) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ ∃ A' : EightDimensionalFramedProduct.FramedProduct D.toFun T,
      (∀ s : Sphere 3, A'.transverse s.val = A.transverse s.val) ∧
      ∀ x ∈ closedBall (0 : Vector 4) 1, r ≤ ‖x‖ →
        D.toFun x = collar b (e.toFun ∘ f) x ∧
        T x = boundaryFrameOperator
          (SevenSurgery.normalFrameOnSphere e a f (SphereRadialRetraction.retract b x)).val ∧
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
      (w : Vector 4) : ‖A.transverseExtension b x w‖ = ‖w‖ :=
    A.norm_transverseExtension b (hhalf x hx.2) w
  have hFr (x : Vector 4) (hx : x ∈ closedBall (0 : Vector 4) 1 ∩ U) :
      (A.transverseExtension b x).range ≤
        (OperatorSum.operator (T x) (fderiv ℝ D.toFun x)).rangeᗮ :=
    SevenSurgery.range_transverseExtension_le_complement e a f hf hd D A hTb hV hDV hx.2.1
      (hhalf x hx.2) (hTc x hx.1 (hr₀x x hx.2))
  have hDi : InjOn D.toFun (closedBall (0 : Vector 4) 1) := by
    intro x hx y hy hxy
    exact congrArg Subtype.val
      (D.embedded.injective (a₁ := ⟨x, hx⟩) (a₂ := ⟨y, hy⟩) hxy)
  have hN : ((e.ambientDimension - 7) + 5) + 4 + 4 = e.ambientDimension + 6 := by
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

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
