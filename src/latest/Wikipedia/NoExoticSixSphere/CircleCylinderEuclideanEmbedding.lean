import Wikipedia.NoExoticSixSphere.CircleCylinderNormalFrame
import Wikipedia.NoExoticSixSphere.EuclideanTailSplitting
import Wikipedia.NoExoticSixSphere.NormalBundle

/-!
# Fixed Euclidean coordinates for the actual compact circle double

The literal Hilbert-product inclusion is composed with the standard
ordered Euclidean block isometry. This gives a closed Euclidean embedding
with injective native differential, without changing its regular-fiber atlas.
-/

noncomputable section

open Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.CircleCylinder

def ambientCoordinates (m : ℕ) :
    HilbertAmbient m ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (2 + (m + 1))) :=
  (EuclideanTailCoordinates.finAdd 2 (m + 1)).symm

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

def euclideanInclusion (p : Fiber d) : EuclideanSpace ℝ (Fin (2 + (m + 1))) :=
  ambientCoordinates m (ambientInclusion d p)

theorem contMDiff_euclideanInclusion (k : ℕ) (hd : m = n + k) :
    letI := fiberAtlas d k hd;
    ContMDiff (𝓡 (k + 1)) (𝓡 (2 + (m + 1))) ∞ (euclideanInclusion d) := by
  let := fiberAtlas d k hd
  exact (ambientCoordinates m).toContinuousLinearEquiv.contDiff.contMDiff.comp
    (contMDiff_ambientInclusion d k hd)

theorem isClosedEmbedding_euclideanInclusion :
    Topology.IsClosedEmbedding (euclideanInclusion d) :=
  (ambientCoordinates m).toHomeomorph.isClosedEmbedding.comp (isClosedEmbedding_ambientInclusion d)

theorem injective_mfderiv_euclideanInclusion (k : ℕ) (hd : m = n + k) (p : Fiber d) :
    letI := fiberAtlas d k hd;
    Injective (mfderiv (𝓡 (k + 1)) (𝓡 (2 + (m + 1))) (euclideanInclusion d) p) := by
  let := fiberAtlas d k hd
  change Injective (mfderiv (𝓡 (k + 1)) (𝓡 (2 + (m + 1)))
    ((ambientCoordinates m).toContinuousLinearEquiv ∘ ambientInclusion d) p)
  rw [mfderiv_comp p
    ((ambientCoordinates m).toContinuousLinearEquiv.differentiableAt.mdifferentiableAt)
    ((contMDiff_ambientInclusion d k hd).mdifferentiableAt (by simp)),
    mfderiv_eq_fderiv, ContinuousLinearEquiv.fderiv]
  exact (ambientCoordinates m).injective.comp (injective_mfderiv_ambientInclusion d k hd p)

def embedding (k : ℕ) (hd : m = n + k) :
    letI := fiberAtlas d k hd;
    EuclideanEmbedding (k + 1) (Fiber d) := by
  let := fiberAtlas d k hd
  exact {
    ambientDimension := 2 + (m + 1)
    toFun := euclideanInclusion d
    smooth := contMDiff_euclideanInclusion d k hd
    closedEmbedding := isClosedEmbedding_euclideanInclusion d
    injective_mfderiv := injective_mfderiv_euclideanInclusion d k hd }

theorem embedding_apply (k : ℕ) (hd : m = n + k) (p : Fiber d) :
    letI := fiberAtlas d k hd;
    (embedding d k hd).toFun p = ambientCoordinates m (ambientInclusion d p) := rfl

end NoExoticSixSphere.CircleCylinder
