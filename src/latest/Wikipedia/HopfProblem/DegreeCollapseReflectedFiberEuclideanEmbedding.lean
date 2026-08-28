import Wikipedia.HopfProblem.DegreeCollapseReflectedFiberSeamFrame
import Wikipedia.NoExoticSixSphere.NormalBundle

/-!
# The reflected fiber as an actual Euclidean embedding

Use the explicit isometry from the cylinder's L2 product to a standard
Euclidean space. Its actual derivative transports tangent and normal
spaces. The compactness premise is proved from the omitted right fiber.
-/

noncomputable section

open Function Set Topology
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder

open NoExoticSixSphere GLOrthonormalization

def ambientCoordinates (m : ℕ) : WithLp 2 (ℝ × Vector (m + 1)) ≃ₗᵢ[ℝ] Vector (m + 2) :=
  (EuclideanTailCoordinates.split (m + 1)).symm

theorem ambientCoordinates_apply (m : ℕ) (t : ℝ) (x : Vector (m + 1)) :
    ambientCoordinates m (WithLp.toLp 2 (t, x)) =
      EuclideanSpace.finAddEquivProd.symm (x, EuclideanTailCoordinates.scalar t) := rfl

variable {m n : ℕ} {b : Sphere n}
  (d : RegularCollaredCylinder (M := Sphere m) (𝓡 m) (𝓡 n) b 0 1)

def euclideanInclusion : Fiber d → Vector (m + 2) := ambientCoordinates m ∘ ambientInclusion d

theorem contMDiff_euclideanInclusion (k : ℕ) (hd : m = n + k) :
    letI := fiberAtlas d k hd;
    ContMDiff (𝓡 (k + 1)) (𝓡 (m + 2)) ∞ (euclideanInclusion d) := by
  let := fiberAtlas d k hd
  exact (ambientCoordinates m).toContinuousLinearEquiv.contDiff.contMDiff.comp
    (contMDiff_ambientInclusion d k hd)

def euclideanDifferential (k : ℕ) (hd : m = n + k) (p : Fiber d) :
    Vector (k + 1) →L[ℝ] Vector (m + 2) :=
  (ambientCoordinates m).toContinuousLinearMap.comp (ambientDifferential d k hd p)

theorem mfderiv_euclideanInclusion (k : ℕ) (hd : m = n + k) (p : Fiber d) :
    letI := fiberAtlas d k hd;
    mfderiv (𝓡 (k + 1)) (𝓡 (m + 2)) (euclideanInclusion d) p =
      euclideanDifferential d k hd p := by
  let := fiberAtlas d k hd
  have hC : HasMFDerivAt 𝓘(ℝ, WithLp 2 (ℝ × Vector (m + 1))) (𝓡 (m + 2))
      (ambientCoordinates m) (ambientInclusion d p)
      (ambientCoordinates m).toContinuousLinearMap :=
    (ambientCoordinates m).toContinuousLinearEquiv.hasFDerivAt.hasMFDerivAt
  exact (hC.comp p
    ((contMDiff_ambientInclusion d k hd).mdifferentiableAt (by simp)).hasMFDerivAt).mfderiv

theorem injective_euclideanDifferential (k : ℕ) (hd : m = n + k) (p : Fiber d) :
    Injective (euclideanDifferential d k hd p) :=
  (ambientCoordinates m).injective.comp (injective_ambientDifferential d k hd p)

theorem range_euclideanDifferential (k : ℕ) (hd : m = n + k) (p : Fiber d) :
    (euclideanDifferential d k hd p).range = (ambientDifferential d k hd p).range.map
      (ambientCoordinates m).toLinearEquiv.toLinearMap :=
  LinearMap.range_comp _ _

def embedding (hmiss : ∀ x, d.rightMap x ≠ b) (k : ℕ) (hd : m = n + k) :
    letI := fiberAtlas d k hd; EuclideanEmbedding (k + 1) (Fiber d) := by
  let := fiberAtlas d k hd
  exact
    { ambientDimension := m + 2
      toFun := euclideanInclusion d
      smooth := contMDiff_euclideanInclusion d k hd
      closedEmbedding := (ambientCoordinates m).toHomeomorph.isClosedEmbedding.comp
        (isClosedEmbedding_ambientInclusion d hmiss)
      injective_mfderiv := fun p ↦ by
        rw [mfderiv_euclideanInclusion]
        exact injective_euclideanDifferential d k hd p }

theorem normalProjection_range (hmiss : ∀ x, d.rightMap x ≠ b)
    (k : ℕ) (hd : m = n + k) (p : Fiber d) : letI := fiberAtlas d k hd;
    ((embedding d hmiss k hd).normalProjection p).range =
      (ambientDifferential d k hd p).rangeᗮ.map
        (ambientCoordinates m).toLinearEquiv.toLinearMap := by
  let := fiberAtlas d k hd
  have hD : (embedding d hmiss k hd).normalFiber p =
      (euclideanDifferential d k hd p).rangeᗮ :=
    congrArg (fun D : Vector (k + 1) →L[ℝ] Vector (m + 2) ↦ D.rangeᗮ)
      (mfderiv_euclideanInclusion d k hd p)
  have hN : (euclideanDifferential d k hd p).rangeᗮ =
      (ambientDifferential d k hd p).rangeᗮ.map
        (ambientCoordinates m).toLinearEquiv.toLinearMap := by
    rw [range_euclideanDifferential]
    exact (Submodule.map_orthogonal_equiv _ (ambientCoordinates m)).symm
  exact ((embedding d hmiss k hd).range_normalProjection p).trans (hD.trans hN)

theorem embedding_seamCollar (hmiss : ∀ x, d.rightMap x ≠ b)
    (k : ℕ) (hd : m = n + k) (t : ℝ) (ht : t ∈ seamCollarTimes d)
    (x : {x : Sphere m // d.leftMap x = b}) : letI := fiberAtlas d k hd;
    (embedding d hmiss k hd).toFun (seamCollarPoint d t ht x) =
      EuclideanSpace.finAddEquivProd.symm (x.val.val, EuclideanTailCoordinates.scalar t) := rfl

end Wikipedia.HopfProblem.DegreeCollapse.ReflectedCylinder
