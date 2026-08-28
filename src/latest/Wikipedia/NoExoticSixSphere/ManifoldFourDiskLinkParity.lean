import Wikipedia.NoExoticSixSphere.FourDiskParityBallOperator

/-!
# Parity one on every actual link of the global punctured-disk frame

The restriction of the constructed global operator is exactly the link
operator already compared in the original coordinates. Normalization and
proved equalities of dimensions preserve its extension obstruction.
The homology relation between these links and the outer boundary is a
separate assertion, not assumed or inferred from this local calculation.
-/

noncomputable section

open Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel DiskBoundary

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (g : Vector 4 → M)
  (hg : ∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
  (P : GenericFourDisk.ParityBallSystem g)

theorem puncturedFourDiskOperatorMap_link (x : DiskDoublePoints.singularSet g) :
    (e.puncturedFourDiskOperatorMap a g hg P).comp (P.linkingSphere x) =
      (P.ball x).globalOperatorLink e a hg := by
  apply ContinuousMap.ext
  intro s
  rfl

theorem puncturedFourDiskFrameMap_link (x : DiskDoublePoints.singularSet g) :
    (e.puncturedFourDiskFrameMap a g hg P).comp (P.linkingSphere x) =
      (Monomorphism.normalize e.ambientDimension ((e.ambientDimension - 7) + 4)).comp
        ((P.ball x).globalOperatorLink e a hg) := by
  apply ContinuousMap.ext
  intro s
  rfl

theorem puncturedFourDiskGlobalFrameMap_extends_iff (f : C(Sphere 3, P.puncturedDisk)) :
    Extends ((e.puncturedFourDiskGlobalFrameMap a g hg P).comp f) ↔
      Extends ((e.puncturedFourDiskFrameMap a g hg P).comp f) := by
  unfold puncturedFourDiskGlobalFrameMap
  exact extends_dimensionHomeomorph_iff _ _ ((e.puncturedFourDiskFrameMap a g hg P).comp f)

def fourDiskOuterObstruction : ZMod 2 :=
  sphereThirdObstruction ((e.ambientDimension - 7) + 2)
    ((e.puncturedFourDiskGlobalFrameMap a g hg P).comp P.outerBoundary)

def fourDiskLinkObstruction (x : DiskDoublePoints.singularSet g) : ZMod 2 :=
  sphereThirdObstruction ((e.ambientDimension - 7) + 2)
    ((e.puncturedFourDiskGlobalFrameMap a g hg P).comp (P.linkingSphere x))

theorem fourDiskLinkObstruction_one (x : DiskDoublePoints.singularSet g) :
    e.fourDiskLinkObstruction a g hg P x = 1 := by
  have hne : e.fourDiskLinkObstruction a g hg P x ≠ 0 := by
    intro hz
    have he := (sphereThirdObstruction_zero_iff_extension _ _).mp hz
    have hf := (e.puncturedFourDiskGlobalFrameMap_extends_iff a g hg P (P.linkingSphere x)).mp he
    rw [e.puncturedFourDiskFrameMap_link a g hg P x] at hf
    exact (P.ball x).normalized_globalOperatorLink_not_extends e a hg hf
  exact zmodTwo_eq_of_zero_iff _ _ (by simp [hne])

end NoExoticSixSphere.EuclideanEmbedding
