import Wikipedia.HopfProblem.DegreeCollapseLowFramedProduct
import Wikipedia.HopfProblem.DegreeCollapseDiskFullFrameCollar
import Wikipedia.NoExoticSixSphere.SmoothSphereRadialCollar
import Wikipedia.NoExoticSixSphere.SmoothOperatorComplement

/-!

# Exact transverse collars on low-dimensional framed products

Replace the transverse columns in the actual combined normal complement while
retaining the disk, core normal frame, and every original transverse boundary
value. The source and transverse dimensions are independent.
-/

noncomputable section

open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowFramedProduct.FramedProduct

open NoExoticSixSphere GLOrthonormalization

variable {d N k q : ℕ} {D : Vector (d + 1) → Vector N}
  {T : Vector (d + 1) → Vector k →L[ℝ] Vector N}
  (A : FramedProduct (q := q) D T)

theorem contMDiff_transverse_boundary :
    ContMDiff (𝓡 d) 𝓘(ℝ, Vector q →L[ℝ] Vector N) ∞
      (fun s : NoExoticSixSphere.Sphere d ↦ A.transverse s.val) := by
  let : Fact (Module.finrank ℝ (Vector (d + 1)) = d + 1) := ⟨finrank_euclideanSpace_fin⟩
  have hs : ContMDiff (𝓡 d) (𝓡 (d + 1)) ∞
      (fun s : NoExoticSixSphere.Sphere d ↦ s.val) := contMDiff_coe_sphere
  intro s
  exact (A.smooth_transverse s.val (Metric.sphere_subset_closedBall s.property)).contMDiffAt.comp
    s hs.contMDiffAt

variable (b : NoExoticSixSphere.Sphere d)

def transverseExtension : C(Vector (d + 1), Vector q →L[ℝ] Vector N) :=
  ⟨SmoothSphereAmbient.extension b (fun s ↦ A.transverse s.val),
    (SmoothSphereAmbient.contDiff_extension b _ A.contMDiff_transverse_boundary).continuous⟩

theorem contDiff_transverseExtension : ContDiff ℝ ∞ (A.transverseExtension b) :=
  SmoothSphereAmbient.contDiff_extension b _ A.contMDiff_transverse_boundary

theorem transverseExtension_coe (s : NoExoticSixSphere.Sphere d) :
    A.transverseExtension b s.val = A.transverse s.val :=
  SmoothSphereAmbient.extension_coe b (fun s ↦ A.transverse s.val) s

theorem transverseExtension_eq_radial {x : Vector (d + 1)} (hx : (1 / 2 : ℝ) < ‖x‖) :
    A.transverseExtension b x = A.transverse (SphereRadialRetraction.retract b x).val :=
  SmoothSphereAmbient.extension_eq_radial_of_half_le b (fun s ↦ A.transverse s.val) hx.le

theorem norm_transverseExtension {x : Vector (d + 1)} (hx : (1 / 2 : ℝ) < ‖x‖)
    (w : Vector q) : ‖A.transverseExtension b x w‖ = ‖w‖ := by
  rw [A.transverseExtension_eq_radial b hx]
  exact A.norm_transverse _ (Metric.sphere_subset_closedBall
    (SphereRadialRetraction.retract b x).property) w

end Wikipedia.HopfProblem.DegreeCollapse.LowFramedProduct.FramedProduct

noncomputable section

open Set Metric Function
open scoped Manifold ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.LowFramedProduct.FramedProduct

open NoExoticSixSphere GLOrthonormalization Stiefel

variable {d N k q : ℕ} {D : Vector (d + 1) → Vector N}
  {T : Vector (d + 1) → Vector k →L[ℝ] Vector N} (A : FramedProduct (q := q) D T)
  (hD : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ D x)
  (hiD : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, Injective (fderiv ℝ D x))
  (F : C(Vector (d + 1), Vector q →L[ℝ] Vector N)) (hFs : ContDiff ℝ ∞ F)
  (hFC : ∀ s : Sphere d, F s.val = A.transverse s.val)
  {V : Set (Vector (d + 1))} (hV : IsOpen V) (hSV : sphere 0 1 ⊆ V)
  (hFn : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1 ∩ V, ∀ w, ‖F x w‖ = ‖w‖)
  (hFr : ∀ x ∈ closedBall (0 : Vector (d + 1)) 1 ∩ V,
    (F x).range ≤ (OperatorSum.operator (T x) (fderiv ℝ D x)).rangeᗮ)

include A hD hiD hFs hFC hV hSV hFn hFr

theorem exists_transverseFrame_collar :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ closedBall (0 : Vector (d + 1)) 1 ∩ {x | r ≤ ‖x‖} ⊆ V ∧
      ∃ C : Vector (d + 1) → Vector q →L[ℝ] Vector N,
        (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ContDiffAt ℝ ∞ C x) ∧
        (∀ x ∈ closedBall (0 : Vector (d + 1)) 1, ∀ w, ‖C x w‖ = ‖w‖) ∧
        (∀ x ∈ closedBall (0 : Vector (d + 1)) 1,
          (C x).range = (OperatorSum.operator (T x) (fderiv ℝ D x)).rangeᗮ) ∧
        ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, r ≤ ‖x‖ → C x = F x := by
  let B : Vector (d + 1) → Vector (k + (d + 1)) →L[ℝ] Vector N :=
    fun x ↦ OperatorSum.operator (T x) (fderiv ℝ D x)
  have hBi (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) : Injective (B x) :=
    OperatorSum.injective_operator _ _ (Stiefel.injective ⟨T x, A.norm_coreFrame x hx⟩)
      (hiD x hx) ((fderiv ℝ D x).range.orthogonal_disjoint.symm.mono_left
        (A.range_coreFrame x hx))
  have hBs (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      ContDiffAt ℝ ∞ B x :=
    OperatorSum.contDiffAt_operator (A.smooth_coreFrame x hx)
      ((hD x hx).fderiv_right (by simp))
  let P := OperatorComplement.projection B
  have hP (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      IsIdempotentElem (P x) := OperatorComplement.idempotent_projection B x (hBi x hx)
  have hPs (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      ContDiffAt ℝ ∞ P x :=
    OperatorComplement.contDiffAt_projection B x (hBs x hx) (hBi x hx)
  have hPr (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      (P x).range = (B x).rangeᗮ := OperatorComplement.range_projection B x (hBi x hx)
  have hCr (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1) :
      (A.transverse x).range = (P x).range := (A.range_transverse x hx).trans (hPr x hx).symm
  have hFr' (x : Vector (d + 1)) (hx : x ∈ closedBall (0 : Vector (d + 1)) 1 ∩ V) :
      (F x).range ≤ (P x).range := by rw [hPr x hx.1]; exact hFr x hx
  obtain ⟨r, hr, hr1, hrV, C, hCs, hCn, hCr', hCF⟩ :=
    DiskPartialFrame.exists_smooth_full_frame_collar P hP hPs A.transverse A.smooth_transverse
      A.norm_transverse hCr F hFs hFC hV hSV hFn hFr'
  exact ⟨r, hr, hr1, hrV, C, hCs, hCn,
    fun x hx ↦ (hCr' x hx).trans (hPr x hx), hCF⟩

theorem exists_framedProduct_collar (hinj : InjOn D (closedBall (0 : Vector (d + 1)) 1))
    (hN : k + (d + 1) + q = N) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ closedBall (0 : Vector (d + 1)) 1 ∩ {x | r ≤ ‖x‖} ⊆ V ∧
      ∃ A' : FramedProduct (q := q) D T,
        (∀ s : Sphere d, A'.transverse s.val = A.transverse s.val) ∧
        ∀ x ∈ closedBall (0 : Vector (d + 1)) 1, r ≤ ‖x‖ → A'.transverse x = F x := by
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

end Wikipedia.HopfProblem.DegreeCollapse.LowFramedProduct.FramedProduct

