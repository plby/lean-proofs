import Wikipedia.HopfProblem.DegreeCollapseLowCurvedAttachingProduct

/-!

# Original normal columns on the entire low-dimensional native collar model

The original manifold normal frame and the graph axes are smooth,
orthonormal, and normal to the actual lifted native tube derivative.
Every statement retains the original native atlas and exact core values.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable (d : ℕ) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)

def stabilizedHeightMap (G : E → M) (ρ : E → ℝ) (x : E) :
    Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
  coordinates e.ambientDimension (d + 1) ((e.toFun (G x), ρ x), 0)

theorem contDiffAt_stabilizedHeightMap (G : E → M) (ρ : E → ℝ) {x : E}
    (hG : ContMDiffAt 𝓘(ℝ, E) (𝓡 7) ∞ G x) (hρ : ContDiffAt ℝ ∞ ρ x) :
    ContDiffAt ℝ ∞ (stabilizedHeightMap d e G ρ) x :=
  (coordinates e.ambientDimension (d + 1)).contDiff.contDiffAt.comp x
    (((e.smooth.contMDiffAt.comp x hG).contDiffAt.prodMk hρ).prodMk contDiffAt_const)

theorem fderiv_stabilizedHeightMap (G : E → M) (ρ : E → ℝ) {x : E}
    (hG : ContMDiffAt 𝓘(ℝ, E) (𝓡 7) ∞ G x) (hρ : ContDiffAt ℝ ∞ ρ x) (v : E) :
    fderiv ℝ (stabilizedHeightMap d e G ρ) x v = coordinates e.ambientDimension (d + 1)
      ((fderiv ℝ (e.toFun ∘ G) x v, fderiv ℝ ρ x v), 0) := by
  have he := (e.smooth.contMDiffAt.comp x hG).contDiffAt.differentiableAt (by simp)
  have hd := (coordinates e.ambientDimension (d + 1)).hasFDerivAt.comp x
    ((he.hasFDerivAt.prodMk (hρ.differentiableAt (by simp)).hasFDerivAt).prodMk
      (hasFDerivAt_const (0 : ℝ × Vector (d + 1)) x))
  rw [show fderiv ℝ (stabilizedHeightMap d e G ρ) x = _ from hd.fderiv]
  rfl

theorem range_fderiv_embedding_comp_le (G : E → M) {x : E}
    (hG : ContMDiffAt 𝓘(ℝ, E) (𝓡 7) ∞ G x) :
    (fderiv ℝ (e.toFun ∘ G) x).range ≤ e.tangentImage (G x) := by
  have he := mfderiv_comp x (e.smooth.mdifferentiableAt (by simp))
    (hG.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at he
  rw [he]
  rintro _ ⟨v, rfl⟩
  exact ⟨_, rfl⟩

variable (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)

def stabilizedNormalFrame (G : E → M) (x : E) :
    Vector ((e.ambientDimension - 7) + (1 + (d + 1))) →L[ℝ]
      Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
  boundaryFrameOperator d (a.orthonormal (G x)).val

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem norm_stabilizedNormalFrame (G : E → M) (x : E)
    (w : Vector ((e.ambientDimension - 7) + (1 + (d + 1)))) :
    ‖stabilizedNormalFrame d e a G x w‖ = ‖w‖ :=
  norm_boundaryFrameOperator d (a.orthonormal (G x)) w

theorem contDiffAt_stabilizedNormalFrame (G : E → M) {x : E}
    (hG : ContMDiffAt 𝓘(ℝ, E) (𝓡 7) ∞ G x) :
    ContDiffAt ℝ ∞ (stabilizedNormalFrame d e a G) x :=
  ((contMDiff_boundaryFrameOperator d a.contMDiff_orthonormal).contMDiffAt.comp x hG).contDiffAt

theorem stabilizedNormalFrame_normal (G : E → M) (ρ : E → ℝ) {x : E}
    (hG : ContMDiffAt 𝓘(ℝ, E) (𝓡 7) ∞ G x) (hρ : ContDiffAt ℝ ∞ ρ x) :
    (stabilizedNormalFrame d e a G x).range ≤
      (fderiv ℝ (stabilizedHeightMap d e G ρ) x).rangeᗮ := by
  have ha : (a.orthonormal (G x)).val.range = e.normalFiber (G x) :=
    (a.orthonormal_range (G x)).trans (e.range_normalProjection (G x))
  rintro _ ⟨w, rfl⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨v, rfl⟩
  change inner ℝ (fderiv ℝ (stabilizedHeightMap d e G ρ) x v)
    (boundaryFrameOperator d (a.orthonormal (G x)).val w) = 0
  rw [fderiv_stabilizedHeightMap d e G ρ hG hρ, boundaryFrameOperator_apply, inner_coordinates]
  simp only [inner_zero_right, inner_zero_left, add_zero, Prod.fst_zero, Prod.snd_zero]
  exact Submodule.inner_right_of_mem_orthogonal
    ((range_fderiv_embedding_comp_le e G hG) ⟨v, rfl⟩) (ha.le ⟨_, rfl⟩)

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M) (f : NoExoticSixSphere.Sphere d → M)
  (C : NoExoticSixSphere.Sphere d → Vector (7 - d) →L[ℝ] Vector e.ambientDimension)
  (R : EuclideanEmbedding.TubularRetraction e) (b : NoExoticSixSphere.Sphere d)

def radialInternalSphereTube (p : Vector (d + 1) × Vector (7 - d)) : M :=
  internalSphereTube e f C R (SphereRadialRetraction.retract b p.1, p.2)

theorem radialInternalSphereTube_core (x : Vector (d + 1)) :
    radialInternalSphereTube e f C R b (x, 0) = f (SphereRadialRetraction.retract b x) :=
  internalSphereTube_core e f C R _

theorem radialInternalSphereTube_coe (s : NoExoticSixSphere.Sphere d) (v : Vector (7 - d)) :
    radialInternalSphereTube e f C R b (s.val, v) = internalSphereTube e f C R (s, v) := by
  simp only [radialInternalSphereTube, SphereRadialRetraction.retract_coe]

theorem contMDiffAt_radialInternalSphereTube
    (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f)
    (hC : ContMDiff (𝓡 d) 𝓘(ℝ, Vector (7 - d) →L[ℝ] Vector e.ambientDimension) ∞ C)
    {x : Vector (d + 1)} (hx : x ≠ 0) (v : Vector (7 - d))
    (hp : (SphereRadialRetraction.retract b x, v) ∈ sphereTubeDomain e f C R) :
    ContMDiffAt 𝓘(ℝ, Vector (d + 1) × Vector (7 - d)) (𝓡 7) ∞
      (radialInternalSphereTube e f C R b) (x, v) := by
  have hI := (contMDiffOn_internalSphereTube e f C R hf hC).contMDiffAt
    ((isOpen_sphereTubeDomain e f C R hf hC).mem_nhds hp)
  exact hI.comp (x, v) (LowRadialProduct.contMDiffAt_radialProduct b hx v)

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

noncomputable section

open Function
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace Wikipedia.HopfProblem.DegreeCollapse.LowSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {d : ℕ} {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : NoExoticSixSphere.Sphere d → M)
  (C : NoExoticSixSphere.Sphere d → Vector (7 - d) →L[ℝ] Vector e.ambientDimension)
  (R : EuclideanEmbedding.TubularRetraction e) (b : NoExoticSixSphere.Sphere d)

def collarNormalFrame : Vector (d + 1) × Vector (7 - d) →
    Vector ((e.ambientDimension - 7) + (1 + (d + 1))) →L[ℝ]
      Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
  stabilizedNormalFrame d e a (radialInternalSphereTube e f C R b)

omit a in
def curvedCollarModel : Vector (d + 1) × Vector (7 - d) →
    Vector (e.ambientDimension + (1 + (1 + (d + 1)))) :=
  stabilizedHeightMap d e (radialInternalSphereTube e f C R b) (fun p ↦ definingFunction p.1)

theorem norm_collarNormalFrame (p : Vector (d + 1) × Vector (7 - d))
    (w : Vector ((e.ambientDimension - 7) + (1 + (d + 1)))) :
    ‖collarNormalFrame e a f C R b p w‖ = ‖w‖ :=
  norm_stabilizedNormalFrame d e a _ p w

theorem collarNormalFrame_core (x : Vector (d + 1)) :
    collarNormalFrame e a f C R b (x, 0) = boundaryFrameOperator d
      (a.orthonormal (f (SphereRadialRetraction.retract b x))).val := by
  unfold collarNormalFrame stabilizedNormalFrame
  rw [radialInternalSphereTube_core e]

theorem collarNormalFrame_coe (s : NoExoticSixSphere.Sphere d) (v : Vector (7 - d)) :
    collarNormalFrame e a f C R b (s.val, v) =
      boundaryFrameOperator d (a.orthonormal (internalSphereTube e f C R (s, v))).val := by
  unfold collarNormalFrame stabilizedNormalFrame
  rw [radialInternalSphereTube_coe e]

variable (hf : ContMDiff (𝓡 d) (𝓡 7) ∞ f)
  (hC : ContMDiff (𝓡 d) 𝓘(ℝ, Vector (7 - d) →L[ℝ] Vector e.ambientDimension) ∞ C)
  {x : Vector (d + 1)} (hx : x ≠ 0) (v : Vector (7 - d))
  (hp : (SphereRadialRetraction.retract b x, v) ∈ sphereTubeDomain e f C R)

include hf hC hx hp in
theorem contDiffAt_collarNormalFrame :
    ContDiffAt ℝ ∞ (collarNormalFrame e a f C R b) (x, v) :=
  contDiffAt_stabilizedNormalFrame d e a _
    (contMDiffAt_radialInternalSphereTube e f C R b hf hC hx v hp)

omit a in
include hf hC hx hp in
theorem contDiffAt_curvedCollarModel :
    ContDiffAt ℝ ∞ (curvedCollarModel e f C R b) (x, v) :=
  contDiffAt_stabilizedHeightMap d e _ _
    (contMDiffAt_radialInternalSphereTube e f C R b hf hC hx v hp)
    (contDiff_definingFunction.contDiffAt.comp (x, v) contDiffAt_fst)

include hf hC hx hp in
theorem collarNormalFrame_normal_model :
    (collarNormalFrame e a f C R b (x, v)).range ≤
      (fderiv ℝ (curvedCollarModel e f C R b) (x, v)).rangeᗮ :=
  stabilizedNormalFrame_normal d e a _ _
    (contMDiffAt_radialInternalSphereTube e f C R b hf hC hx v hp)
    (contDiff_definingFunction.contDiffAt.comp (x, v) contDiffAt_fst)

end Wikipedia.HopfProblem.DegreeCollapse.LowSurgery
