import Wikipedia.NoExoticSixSphere.ManifoldSphereDisk

/-!
# Original normal frames for manifold-valued maps with a new height

Lift an original-manifold map by its actual Euclidean embedding, add a scalar
height, and then five zero graph coordinates. The original orthonormal normal
frame plus the five graph axes is normal to the lifted map's actual derivative.
No immersion or full-rank assertion about the source map is assumed here.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel StabilizedSpanningDisk

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector n) M]
  (e : EuclideanEmbedding n M)

def stabilizedHeightMap (G : E → M) (ρ : E → ℝ) (x : E) : Vector (e.ambientDimension + 6) :=
  coordinates e.ambientDimension 4 ((e.toFun (G x), ρ x), 0)

theorem contDiffAt_stabilizedHeightMap (G : E → M) (ρ : E → ℝ) {x : E}
    (hG : ContMDiffAt 𝓘(ℝ, E) (𝓡 n) ∞ G x) (hρ : ContDiffAt ℝ ∞ ρ x) :
    ContDiffAt ℝ ∞ (e.stabilizedHeightMap G ρ) x :=
  (coordinates e.ambientDimension 4).contDiff.contDiffAt.comp x
    (((e.smooth.contMDiffAt.comp x hG).contDiffAt.prodMk hρ).prodMk contDiffAt_const)

theorem fderiv_stabilizedHeightMap (G : E → M) (ρ : E → ℝ) {x : E}
    (hG : ContMDiffAt 𝓘(ℝ, E) (𝓡 n) ∞ G x) (hρ : ContDiffAt ℝ ∞ ρ x) (v : E) :
    fderiv ℝ (e.stabilizedHeightMap G ρ) x v = coordinates e.ambientDimension 4
      ((fderiv ℝ (e.toFun ∘ G) x v, fderiv ℝ ρ x v), 0) := by
  have he := (e.smooth.contMDiffAt.comp x hG).contDiffAt.differentiableAt (by simp)
  have hd := (coordinates e.ambientDimension 4).hasFDerivAt.comp x
    ((he.hasFDerivAt.prodMk (hρ.differentiableAt (by simp)).hasFDerivAt).prodMk
      (hasFDerivAt_const (0 : ℝ × Vector 4) x))
  rw [show fderiv ℝ (e.stabilizedHeightMap G ρ) x = _ from hd.fderiv]
  rfl

theorem range_fderiv_embedding_comp_le (G : E → M) {x : E}
    (hG : ContMDiffAt 𝓘(ℝ, E) (𝓡 n) ∞ G x) :
    (fderiv ℝ (e.toFun ∘ G) x).range ≤ e.tangentImage (G x) := by
  have he := mfderiv_comp x (e.smooth.mdifferentiableAt (by simp))
    (hG.mdifferentiableAt (by simp))
  rw [mfderiv_eq_fderiv] at he
  rw [he]
  rintro _ ⟨v, rfl⟩
  exact ⟨_, rfl⟩

variable (a : SmoothRangeFrame (𝓡 n) e.normalProjection e.NormalModel)

def stabilizedNormalFrame (G : E → M) (x : E) :
    Vector ((e.ambientDimension - n) + 5) →L[ℝ] Vector (e.ambientDimension + 6) :=
  boundaryFrameOperator (a.orthonormal (G x)).val

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem norm_stabilizedNormalFrame (G : E → M) (x : E)
    (w : Vector ((e.ambientDimension - n) + 5)) : ‖e.stabilizedNormalFrame a G x w‖ = ‖w‖ :=
  norm_boundaryFrameOperator (a.orthonormal (G x)) w

theorem contDiffAt_stabilizedNormalFrame (G : E → M) {x : E}
    (hG : ContMDiffAt 𝓘(ℝ, E) (𝓡 n) ∞ G x) :
    ContDiffAt ℝ ∞ (e.stabilizedNormalFrame a G) x :=
  ((contMDiff_boundaryFrameOperator a.contMDiff_orthonormal).contMDiffAt.comp x hG).contDiffAt

theorem stabilizedNormalFrame_normal (G : E → M) (ρ : E → ℝ) {x : E}
    (hG : ContMDiffAt 𝓘(ℝ, E) (𝓡 n) ∞ G x) (hρ : ContDiffAt ℝ ∞ ρ x) :
    (e.stabilizedNormalFrame a G x).range ≤ (fderiv ℝ (e.stabilizedHeightMap G ρ) x).rangeᗮ := by
  have ha : (a.orthonormal (G x)).val.range = e.normalFiber (G x) :=
    (a.orthonormal_range (G x)).trans (e.range_normalProjection (G x))
  rintro _ ⟨w, rfl⟩
  apply (Submodule.mem_orthogonal _ _).mpr
  rintro _ ⟨v, rfl⟩
  change inner ℝ (fderiv ℝ (e.stabilizedHeightMap G ρ) x v)
    (boundaryFrameOperator (a.orthonormal (G x)).val w) = 0
  rw [e.fderiv_stabilizedHeightMap G ρ hG hρ, boundaryFrameOperator_apply, inner_coordinates]
  simp only [inner_zero_right, inner_zero_left, add_zero, Prod.fst_zero, Prod.snd_zero]
  exact Submodule.inner_right_of_mem_orthogonal
    ((e.range_fderiv_embedding_comp_le G hG) ⟨v, rfl⟩) (ha.le ⟨_, rfl⟩)

end NoExoticSixSphere.EuclideanEmbedding
