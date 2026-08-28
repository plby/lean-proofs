import Wikipedia.HopfProblem.DegreeCollapseSevenCurvedAttachingProduct

/-!
# SevenPrescribedCollarFrame

The actual original normal frame and five graph axes are smooth and orthonormal along the lifted radial tube, and normal to its actual derivative. The original native atlas and exact boundary-core values are retained.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)

def stabilizedHeightMap (G : E → M) (ρ : E → ℝ) (x : E) : Vector (e.ambientDimension + 6) :=
  coordinates e.ambientDimension 4 ((e.toFun (G x), ρ x), 0)

theorem contDiffAt_stabilizedHeightMap (G : E → M) (ρ : E → ℝ) {x : E}
    (hG : ContMDiffAt 𝓘(ℝ, E) (𝓡 7) ∞ G x) (hρ : ContDiffAt ℝ ∞ ρ x) :
    ContDiffAt ℝ ∞ (SevenSurgery.stabilizedHeightMap e G ρ) x :=
  (coordinates e.ambientDimension 4).contDiff.contDiffAt.comp x
    (((e.smooth.contMDiffAt.comp x hG).contDiffAt.prodMk hρ).prodMk contDiffAt_const)

theorem fderiv_stabilizedHeightMap (G : E → M) (ρ : E → ℝ) {x : E}
    (hG : ContMDiffAt 𝓘(ℝ, E) (𝓡 7) ∞ G x) (hρ : ContDiffAt ℝ ∞ ρ x) (v : E) :
    fderiv ℝ (SevenSurgery.stabilizedHeightMap e G ρ) x v = coordinates e.ambientDimension 4
      ((fderiv ℝ (e.toFun ∘ G) x v, fderiv ℝ ρ x v), 0) := by
  have he := (e.smooth.contMDiffAt.comp x hG).contDiffAt.differentiableAt (by simp)
  have hd := (coordinates e.ambientDimension 4).hasFDerivAt.comp x
    ((he.hasFDerivAt.prodMk (hρ.differentiableAt (by simp)).hasFDerivAt).prodMk
      (hasFDerivAt_const (0 : ℝ × Vector 4) x))
  rw [show fderiv ℝ (SevenSurgery.stabilizedHeightMap e G ρ) x = _ from hd.fderiv]
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
    Vector ((e.ambientDimension - 7) + 5) →L[ℝ] Vector (e.ambientDimension + 6) :=
  boundaryFrameOperator (a.orthonormal (G x)).val

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem norm_stabilizedNormalFrame (G : E → M) (x : E)
    (w : Vector ((e.ambientDimension - 7) + 5)) : ‖SevenSurgery.stabilizedNormalFrame e a G x w‖ = ‖w‖ :=
  norm_boundaryFrameOperator (a.orthonormal (G x)) w

theorem contDiffAt_stabilizedNormalFrame (G : E → M) {x : E}
    (hG : ContMDiffAt 𝓘(ℝ, E) (𝓡 7) ∞ G x) :
    ContDiffAt ℝ ∞ (SevenSurgery.stabilizedNormalFrame e a G) x :=
  ((contMDiff_boundaryFrameOperator a.contMDiff_orthonormal).contMDiffAt.comp x hG).contDiffAt

theorem stabilizedNormalFrame_normal (G : E → M) (ρ : E → ℝ) {x : E}
    (hG : ContMDiffAt 𝓘(ℝ, E) (𝓡 7) ∞ G x) (hρ : ContDiffAt ℝ ∞ ρ x) :
    (SevenSurgery.stabilizedNormalFrame e a G x).range ≤ (fderiv ℝ (SevenSurgery.stabilizedHeightMap e G ρ) x).rangeᗮ := by
  have ha : (a.orthonormal (G x)).val.range = e.normalFiber (G x) :=
    (a.orthonormal_range (G x)).trans (e.range_normalProjection (G x))
  rintro _ ⟨w, rfl⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨v, rfl⟩
  change inner ℝ (fderiv ℝ (SevenSurgery.stabilizedHeightMap e G ρ) x v)
    (boundaryFrameOperator (a.orthonormal (G x)).val w) = 0
  rw [SevenSurgery.fderiv_stabilizedHeightMap e G ρ hG hρ, boundaryFrameOperator_apply, inner_coordinates]
  simp only [inner_zero_right, inner_zero_left, add_zero, Prod.fst_zero, Prod.snd_zero]
  exact Submodule.inner_right_of_mem_orthogonal
    ((SevenSurgery.range_fderiv_embedding_comp_le e G hG) ⟨v, rfl⟩) (ha.le ⟨_, rfl⟩)

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

noncomputable section

open Function
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M) (f : Sphere 3 → M)
  (C : Sphere 3 → Vector 4 →L[ℝ] Vector e.ambientDimension)
  (R : EuclideanEmbedding.TubularRetraction e) (b : Sphere 3)

def radialInternalSphereTube (p : Vector 4 × Vector 4) : M :=
  SevenSurgery.internalSphereTube e f C R (SphereRadialRetraction.retract b p.1, p.2)

theorem radialInternalSphereTube_core (x : Vector 4) :
    SevenSurgery.radialInternalSphereTube e f C R b (x, 0) = f (SphereRadialRetraction.retract b x) :=
  SevenSurgery.internalSphereTube_core e f C R _

theorem radialInternalSphereTube_coe (s : Sphere 3) (v : Vector 4) :
    SevenSurgery.radialInternalSphereTube e f C R b (s.val, v) = SevenSurgery.internalSphereTube e f C R (s, v) := by
  simp only [radialInternalSphereTube, SphereRadialRetraction.retract_coe]

theorem contMDiffAt_radialInternalSphereTube
    (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
    (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector e.ambientDimension) ∞ C)
    {x : Vector 4} (hx : x ≠ 0) (v : Vector 4)
    (hp : (SphereRadialRetraction.retract b x, v) ∈ SevenSurgery.sphereTubeDomain e f C R) :
    ContMDiffAt 𝓘(ℝ, Vector 4 × Vector 4) (𝓡 7) ∞
      (SevenSurgery.radialInternalSphereTube e f C R b) (x, v) := by
  have hI := (SevenSurgery.contMDiffOn_internalSphereTube e f C R hf hC).contMDiffAt
    ((SevenSurgery.isOpen_sphereTubeDomain e f C R hf hC).mem_nhds hp)
  exact hI.comp (x, v) (GeneralRadialProduct.contMDiffAt_radialProduct b hx v)

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

noncomputable section

open Function
open scoped Manifold ContDiff
open Wikipedia.SmoothSixDPoincare.SphereBoundary

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery

open NoExoticSixSphere GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (f : Sphere 3 → M) (C : Sphere 3 → Vector 4 →L[ℝ] Vector e.ambientDimension)
  (R : EuclideanEmbedding.TubularRetraction e) (b : Sphere 3)

def collarNormalFrame : Vector 4 × Vector 4 →
    Vector ((e.ambientDimension - 7) + 5) →L[ℝ] Vector (e.ambientDimension + 6) :=
  SevenSurgery.stabilizedNormalFrame e a (SevenSurgery.radialInternalSphereTube e f C R b)

omit a in
def curvedCollarModel : Vector 4 × Vector 4 → Vector (e.ambientDimension + 6) :=
  SevenSurgery.stabilizedHeightMap e (SevenSurgery.radialInternalSphereTube e f C R b) (fun p ↦ definingFunction p.1)

theorem norm_collarNormalFrame (p : Vector 4 × Vector 4)
    (w : Vector ((e.ambientDimension - 7) + 5)) : ‖SevenSurgery.collarNormalFrame e a f C R b p w‖ = ‖w‖ :=
  SevenSurgery.norm_stabilizedNormalFrame e a _ p w

theorem collarNormalFrame_core (x : Vector 4) :
    SevenSurgery.collarNormalFrame e a f C R b (x, 0) = boundaryFrameOperator
      (SevenSurgery.normalFrameOnSphere e a f (SphereRadialRetraction.retract b x)).val := by
  unfold collarNormalFrame stabilizedNormalFrame
  rw [SevenSurgery.radialInternalSphereTube_core e]
  rfl

theorem collarNormalFrame_coe (s : Sphere 3) (v : Vector 4) :
    SevenSurgery.collarNormalFrame e a f C R b (s.val, v) =
      boundaryFrameOperator (a.orthonormal (SevenSurgery.internalSphereTube e f C R (s, v))).val := by
  unfold collarNormalFrame stabilizedNormalFrame
  rw [SevenSurgery.radialInternalSphereTube_coe e]

variable (hf : ContMDiff (𝓡 3) (𝓡 7) ∞ f)
  (hC : ContMDiff (𝓡 3) 𝓘(ℝ, Vector 4 →L[ℝ] Vector e.ambientDimension) ∞ C)
  {x : Vector 4} (hx : x ≠ 0) (v : Vector 4)
  (hp : (SphereRadialRetraction.retract b x, v) ∈ SevenSurgery.sphereTubeDomain e f C R)

include hf hC hx hp in
theorem contDiffAt_collarNormalFrame :
    ContDiffAt ℝ ∞ (SevenSurgery.collarNormalFrame e a f C R b) (x, v) :=
  SevenSurgery.contDiffAt_stabilizedNormalFrame e a _
    (SevenSurgery.contMDiffAt_radialInternalSphereTube e f C R b hf hC hx v hp)

omit a in
include hf hC hx hp in
theorem contDiffAt_curvedCollarModel :
    ContDiffAt ℝ ∞ (SevenSurgery.curvedCollarModel e f C R b) (x, v) :=
  SevenSurgery.contDiffAt_stabilizedHeightMap e _ _
    (SevenSurgery.contMDiffAt_radialInternalSphereTube e f C R b hf hC hx v hp)
    (contDiff_definingFunction.contDiffAt.comp (x, v) contDiffAt_fst)

include hf hC hx hp in
theorem collarNormalFrame_normal_model :
    (SevenSurgery.collarNormalFrame e a f C R b (x, v)).range ≤
      (fderiv ℝ (SevenSurgery.curvedCollarModel e f C R b) (x, v)).rangeᗮ :=
  SevenSurgery.stabilizedNormalFrame_normal e a _ _
    (SevenSurgery.contMDiffAt_radialInternalSphereTube e f C R b hf hC hx v hp)
    (contDiff_definingFunction.contDiffAt.comp (x, v) contDiffAt_fst)

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery
