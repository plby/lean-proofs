import Wikipedia.NoExoticSixSphere.SphereFiberNormalFrame
import Wikipedia.NoExoticSixSphere.NormalBundle
import Wikipedia.HopfProblem.DegreeCollapseEuclideanProductCoordinates

/-!
# The actual Euclidean embedding and frame of a regular sphere fiber

The embedding is the original fiber's inclusion into the original Euclidean
ambient space. Its atlas is the constructed regular-fiber atlas. The normal
frame is the existing orthogonal right inverse of the original defining
equations, with an explicit, constant change of normal-model coordinates.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.RegularSphereFiber

variable {m n : ℕ} (f : C(Sphere m, Sphere n))
  (hf : ContMDiff (𝓡 m) (𝓡 n) ∞ f) (b : Sphere n)
  (hreg : ∀ x, f x = b → Surjective (mfderiv (𝓡 m) (𝓡 n) f x))
  (k : ℕ) (hd : m = n + k)

theorem fiber_compact : CompactSpace {x : Sphere m // f x = b} :=
  isCompact_iff_compactSpace.mp (isClosed_eq f.continuous continuous_const).isCompact

def embedding :
    letI := regularFiberAtlas f hf b hreg k (by simpa using hd);
    EuclideanEmbedding k {x : Sphere m // f x = b} := by
  let := regularFiberAtlas f hf b hreg k (by simpa using hd)
  refine {
    ambientDimension := m + 1
    toFun := SphereFiberNormalFrame.ambientInclusion f b
    smooth := SphereFiberNormalFrame.contMDiff_ambientInclusion f hf b hreg k hd
    closedEmbedding := ?_
    injective_mfderiv := SphereFiberNormalFrame.injective_ambientDifferential f hf b hreg k hd }
  exact isClosed_sphere.isClosedEmbedding_subtypeVal.comp
    (isClosed_eq f.continuous continuous_const).isClosedEmbedding_subtypeVal

theorem embedding_apply (x : {x : Sphere m // f x = b}) :
    letI := regularFiberAtlas f hf b hreg k (by simpa using hd);
    (embedding f hf b hreg k hd).toFun x = x.val.val := rfl

def normalCoordinates :
    EuclideanSpace ℝ (Fin (m + 1 - k)) ≃L[ℝ]
      WithLp 2 (ℝ × EuclideanSpace ℝ (Fin n)) := by
  have he : m + 1 - k = n + 1 := by omega
  rw [he]
  let Q := Wikipedia.HopfProblem.DegreeCollapse.EuclideanProduct.headIsometry n
  exact Q.symm.toContinuousLinearEquiv

def frame (a : Sphere m) :
    letI := regularFiberAtlas f hf b hreg k (by simpa using hd);
    SmoothRangeFrame (𝓡 k) (embedding f hf b hreg k hd).normalProjection
      (embedding f hf b hreg k hd).NormalModel := by
  let := regularFiberAtlas f hf b hreg k (by simpa using hd)
  let A := SphereFiberNormalFrame.normalFrame f hf b hreg k hd a
  let Q := normalCoordinates k hd
  refine ⟨fun x ↦ Q.trans (A.equiv x), ?_⟩
  change ContMDiff (𝓡 k) 𝓘(ℝ, EuclideanSpace ℝ (Fin (m + 1 - k)) →L[ℝ]
    EuclideanSpace ℝ (Fin (m + 1))) ∞ (fun x ↦ (A.ambient x).comp Q.toContinuousLinearMap)
  exact A.contMDiff_ambient.clm_comp contMDiff_const

theorem frame_ambient (a : Sphere m) (x : {x : Sphere m // f x = b}) :
    letI := regularFiberAtlas f hf b hreg k (by simpa using hd);
    (frame f hf b hreg k hd a).ambient x =
      (orthogonalRightInverse
        (fderiv ℝ (SphereFiberNormalFrame.equations f b a) x.val.val)).comp
          (normalCoordinates k hd).toContinuousLinearMap := by
  let := regularFiberAtlas f hf b hreg k (by simpa using hd)
  change ((SphereFiberNormalFrame.normalFrame f hf b hreg k hd a).ambient x).comp
    (normalCoordinates k hd).toContinuousLinearMap = _
  rw [SphereFiberNormalFrame.normalFrame_ambient]

end NoExoticSixSphere.RegularSphereFiber
