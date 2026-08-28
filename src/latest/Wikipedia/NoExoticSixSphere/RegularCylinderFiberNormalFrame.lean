import Wikipedia.NoExoticSixSphere.RegularCylinderFiberEmbedding
import Wikipedia.NoExoticSixSphere.SmoothRangeFrameOfOperator
import Wikipedia.NoExoticSixSphere.NormalProjection
import Wikipedia.NoExoticSixSphere.NormalBundle

/-!
# The prescribed regular-fiber normal frame in its actual Euclidean embedding

The original equation frame is transported by the ordered ambient isometry
and the ordered normal-coordinate isometry. Its range is the normal space
of the original embedding, in the original regular-fiber atlas. Thus no
additional framing existence hypothesis is needed for a regular fiber.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularCylinderFiber

open Wikipedia.HopfProblem.DegreeCollapse EuclideanProduct

variable {m n : ℕ} (f : C(ℝ × Sphere m, Sphere n))
  (hf : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n) ∞ f) (b : Sphere n)
  (hreg : ∀ p, f p = b → Surjective (mfderiv ((𝓘(ℝ, ℝ)).prod (𝓡 m)) (𝓡 n) f p))
  (k : ℕ) (hd : m = n + k)

def normalModelCoordinates :
    Vector ((m + 2) - (k + 1)) ≃L[ℝ] WithLp 2 (ℝ × Vector n) := by
  have he : (m + 2) - (k + 1) = n + 1 := by omega
  rw [he]
  exact (headIsometry n).symm.toContinuousLinearEquiv

theorem embedding_derivative (p : {p : ℝ × Sphere m // f p = b}) :
    letI := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
    mfderiv (𝓡 (k + 1)) (𝓡 (embedding f hf b hreg k hd).ambientDimension)
      (embedding f hf b hreg k hd).toFun p =
      (headIsometry (m + 1)).toContinuousLinearMap.comp
        (NormalFrameOfEquations.ambientDifferential (𝓡 (k + 1))
          (CylinderFiberNormalFrame.ambientInclusion f b) p) := by
  let _ := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
  let L := (headIsometry (m + 1)).toContinuousLinearMap
  change mfderiv (𝓡 (k + 1)) (𝓡 (m + 2))
    (L ∘ CylinderFiberNormalFrame.ambientInclusion f b) p = _
  rw [mfderiv_comp p L.differentiableAt.mdifferentiableAt
    ((CylinderFiberNormalFrame.contMDiff_ambientInclusion f hf b hreg k hd).mdifferentiableAt
      (by simp)), mfderiv_eq_fderiv, ContinuousLinearMap.fderiv]
  rfl

theorem embedding_tangentImage (p : {p : ℝ × Sphere m // f p = b}) :
    letI := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
    (embedding f hf b hreg k hd).tangentImage p =
      (NormalFrameOfEquations.ambientDifferential (𝓡 (k + 1))
        (CylinderFiberNormalFrame.ambientInclusion f b) p).range.map
          (headIsometry (m + 1)).toLinearEquiv.toLinearMap := by
  let _ := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
  change (mfderiv (𝓡 (k + 1)) (𝓡 (embedding f hf b hreg k hd).ambientDimension)
    (embedding f hf b hreg k hd).toFun p).range = _
  rw [embedding_derivative]
  exact LinearMap.range_comp _ _

theorem embedding_normalFiber (p : {p : ℝ × Sphere m // f p = b}) :
    letI := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
    (embedding f hf b hreg k hd).normalFiber p =
      (NormalFrameOfEquations.ambientDifferential (𝓡 (k + 1))
        (CylinderFiberNormalFrame.ambientInclusion f b) p).rangeᗮ.map
          (headIsometry (m + 1)).toLinearEquiv.toLinearMap := by
  let _ := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
  change ((embedding f hf b hreg k hd).tangentImage p)ᗮ = _
  rw [embedding_tangentImage]
  exact (Submodule.map_orthogonal_equiv _ (headIsometry (m + 1))).symm

def normalOperator (a : Sphere m) (p : {p : ℝ × Sphere m // f p = b}) :
    Vector ((m + 2) - (k + 1)) →L[ℝ] Vector (m + 2) := by
  let _ := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
  exact (headIsometry (m + 1)).toContinuousLinearMap.comp
    (((CylinderFiberNormalFrame.normalFrame f hf b hreg k hd a).ambient p).comp
      (normalModelCoordinates k hd).toContinuousLinearMap)

theorem contMDiff_normalOperator (a : Sphere m) :
    letI := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
    ContMDiff (𝓡 (k + 1)) 𝓘(ℝ, Vector ((m + 2) - (k + 1)) →L[ℝ] Vector (m + 2)) ∞
      (normalOperator f hf b hreg k hd a) := by
  let _ := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
  exact contMDiff_const.clm_comp
    ((CylinderFiberNormalFrame.normalFrame f hf b hreg k hd a).contMDiff_ambient.clm_comp
      contMDiff_const)

theorem normalOperator_injective (a : Sphere m) (p : {p : ℝ × Sphere m // f p = b}) :
    Injective (normalOperator f hf b hreg k hd a p) := by
  let _ := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
  exact (headIsometry (m + 1)).injective.comp
    (((CylinderFiberNormalFrame.normalFrame f hf b hreg k hd a).ambient_injective p).comp
      (normalModelCoordinates k hd).injective)

theorem normalOperator_range (a : Sphere m) (p : {p : ℝ × Sphere m // f p = b}) :
    letI := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
    (normalOperator f hf b hreg k hd a p).range =
      (embedding f hf b hreg k hd).normalFiber p := by
  let _ := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
  let A := CylinderFiberNormalFrame.normalFrame f hf b hreg k hd a
  have hn : (A.ambient p).range =
      (NormalFrameOfEquations.ambientDifferential (𝓡 (k + 1))
        (CylinderFiberNormalFrame.ambientInclusion f b) p).rangeᗮ := by
    rw [A.ambient_range_eq]
    exact Submodule.range_starProjection _
  have hc : ((A.ambient p).comp (normalModelCoordinates k hd).toContinuousLinearMap).range =
      (A.ambient p).range :=
    LinearMap.range_comp_of_range_eq_top _
      (LinearMap.range_eq_top.mpr (normalModelCoordinates k hd).surjective)
  change ((headIsometry (m + 1)).toLinearEquiv.toLinearMap.comp
    ((A.ambient p).comp (normalModelCoordinates k hd).toContinuousLinearMap).toLinearMap).range = _
  rw [LinearMap.range_comp, hc, hn, embedding_normalFiber]

theorem normalOperator_range_projection (a : Sphere m)
    (p : {p : ℝ × Sphere m // f p = b}) :
    letI := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
    (normalOperator f hf b hreg k hd a p).range =
      ((embedding f hf b hreg k hd).normalProjection p).range := by
  let _ := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
  rw [(embedding f hf b hreg k hd).range_normalProjection]
  exact normalOperator_range f hf b hreg k hd a p

def normalFrame (a : Sphere m) :
    letI := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
    SmoothRangeFrame (𝓡 (k + 1)) (embedding f hf b hreg k hd).normalProjection
      (embedding f hf b hreg k hd).NormalModel := by
  let _ := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
  exact SmoothRangeFrame.ofOperator (normalOperator f hf b hreg k hd a)
    (contMDiff_normalOperator f hf b hreg k hd a) (normalOperator_injective f hf b hreg k hd a)
    (normalOperator_range_projection f hf b hreg k hd a)

theorem normalFrame_ambient (a : Sphere m) (p : {p : ℝ × Sphere m // f p = b}) :
    letI := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
    (normalFrame f hf b hreg k hd a).ambient p = normalOperator f hf b hreg k hd a p := by
  let _ := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
  exact SmoothRangeFrame.ofOperator_ambient (normalOperator f hf b hreg k hd a)
    (contMDiff_normalOperator f hf b hreg k hd a) (normalOperator_injective f hf b hreg k hd a)
    (normalOperator_range_projection f hf b hreg k hd a) p

theorem normalFrame_ambient_equations (a : Sphere m) (p : {p : ℝ × Sphere m // f p = b}) :
    letI := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
    (normalFrame f hf b hreg k hd a).ambient p =
      (headIsometry (m + 1)).toContinuousLinearMap.comp
        ((orthogonalRightInverse (fderiv ℝ (CylinderFiberNormalFrame.equations f b a)
          (CylinderLevelEquations.inclusion p.val))).comp
            (normalModelCoordinates k hd).toContinuousLinearMap) := by
  let _ := regularFiberAtlas f hf b hreg (k + 1) (CylinderFiberNormalFrame.dimension_eq hd)
  rw [normalFrame_ambient, normalOperator, CylinderFiberNormalFrame.normalFrame_ambient]

end NoExoticSixSphere.RegularCylinderFiber
