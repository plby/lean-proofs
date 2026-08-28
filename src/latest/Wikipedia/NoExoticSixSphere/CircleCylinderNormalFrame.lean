import Wikipedia.NoExoticSixSphere.CircleCylinderNormalEquations
import Wikipedia.NoExoticSixSphere.NormalFrameOfEquations

/-!
# The genuine normal frame of the compact circle double

The normal space is the orthogonal complement of the actual native
inclusion's tangent image. The proved ambient regular equations supply
its smooth frame by their canonical orthogonal right inverse. The
inclusion is also a closed embedding into the genuine Hilbert product.
-/

noncomputable section

open Function Module
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

theorem finrank_hilbertAmbient (m : ℕ) : finrank ℝ (HilbertAmbient m) = 2 + (m + 1) := by
  rw [(WithLp.prodContinuousLinearEquiv 2 ℝ V
    (EuclideanSpace ℝ (Fin (m + 1)))).toLinearEquiv.finrank_eq, finrank_prod]
  simp only [V, finrank_euclideanSpace_fin]

theorem finrank_normalModel (n : ℕ) : finrank ℝ (NormalModel n) = n + 2 := by
  rw [(WithLp.prodContinuousLinearEquiv 2 ℝ ℝ
    (WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n)))).toLinearEquiv.finrank_eq,
    finrank_prod, finrank_self,
    (WithLp.prodContinuousLinearEquiv 2 ℝ ℝ
      (EuclideanSpace ℝ (Fin n))).toLinearEquiv.finrank_eq,
    finrank_prod, finrank_self, finrank_euclideanSpace_fin]
  omega

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

theorem continuous_ambientInclusion : Continuous (ambientInclusion d) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ V (EuclideanSpace ℝ (Fin (m + 1)))).symm.continuous.comp
    ((continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_subtype_val.comp (continuous_snd.comp continuous_subtype_val)))

theorem ambientInclusion_injective : Injective (ambientInclusion d) :=
  ProductSphereLevelEquations.inclusion_injective.comp Subtype.val_injective

theorem isClosedEmbedding_ambientInclusion : Topology.IsClosedEmbedding (ambientInclusion d) := by
  let := compactSpace_fiber d
  exact (continuous_ambientInclusion d).isClosedEmbedding (ambientInclusion_injective d)

theorem normal_dimension_eq (k : ℕ) (hd : m = n + k) :
    finrank ℝ (HilbertAmbient m) =
      finrank ℝ (NormalModel n) + finrank ℝ (EuclideanSpace ℝ (Fin (k + 1))) := by
  rw [finrank_hilbertAmbient, finrank_normalModel, finrank_euclideanSpace_fin]
  omega

def ambientNormalFrame (a : Sphere 1 × Sphere m) (k : ℕ) (hd : m = n + k) :
    letI := fiberAtlas d k hd;
    SmoothRangeFrame (𝓡 (k + 1))
      (fun p : Fiber d ↦
        (NormalFrameOfEquations.ambientDifferential (𝓡 (k + 1))
          (ambientInclusion d) p).rangeᗮ.starProjection) (NormalModel n) := by
  let := fiberAtlas d k hd
  exact NormalFrameOfEquations.inducedFrame
    (contMDiff_ambientInclusion d k hd) (contDiffAt_ambientEquations d a)
    (ambientEquations_zero d a) (surjective_fderiv_ambientEquations d a)
    (injective_mfderiv_ambientInclusion d k hd) (normal_dimension_eq k hd)

theorem ambientNormalFrame_ambient (a : Sphere 1 × Sphere m)
    (k : ℕ) (hd : m = n + k) (p : Fiber d) :
    letI := fiberAtlas d k hd;
    (ambientNormalFrame d a k hd).ambient p =
      orthogonalRightInverse (fderiv ℝ (ambientEquations d a) (ambientInclusion d p)) := by
  let := fiberAtlas d k hd
  apply ContinuousLinearMap.ext
  intro v
  rfl

end NoExoticSixSphere.CircleCylinder
