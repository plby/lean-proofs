import Wikipedia.NoExoticSixSphere.ManifoldFourAnnulusOperator
import Wikipedia.NoExoticSixSphere.ParityBallLocalGlobalOperator

/-!
# Parity one on the actual links of the original punctured-annulus frame

Restriction of the constructed global operator gives exactly the retained
local global link. The original target coordinates extend over the entire
model disk, and normalization and dimension changes preserve extension.
Thus every actual link has obstruction one. The two original endpoint
obstructions are retained separately; no boundary relation is assumed.
-/

noncomputable section

open Set Function
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel DiskBoundary SphereAnnulus

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (g : Vector 4 → M)
  (hg : ∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
  (P : GenericFourAnnulus.ParityBallSystem g)

theorem puncturedFourAnnulusOperatorMap_link (x : AnnulusDoublePoints.singularSet g) :
    (e.puncturedFourAnnulusOperatorMap a g hg P).comp (P.linkingSphere x) =
      (P.ball x).localGlobalOperatorLink e a
        (fun y hy ↦ hg y (openDomain_subset_domain 3
          ((P.ball x).closedRegion_subset_interior hy))) := by
  apply ContinuousMap.ext
  intro q
  rfl

theorem puncturedFourAnnulusFrameMap_link (x : AnnulusDoublePoints.singularSet g) :
    (e.puncturedFourAnnulusFrameMap a g hg P).comp (P.linkingSphere x) =
      (Monomorphism.normalize e.ambientDimension ((e.ambientDimension - 7) + 4)).comp
        ((P.ball x).localGlobalOperatorLink e a
          (fun y hy ↦ hg y (openDomain_subset_domain 3
            ((P.ball x).closedRegion_subset_interior hy)))) := by
  apply ContinuousMap.ext
  intro q
  rfl

theorem puncturedFourAnnulusGlobalFrameMap_extends_iff (f : C(Sphere 3, P.puncturedAnnulus)) :
    Extends ((e.puncturedFourAnnulusGlobalFrameMap a g hg P).comp f) ↔
      Extends ((e.puncturedFourAnnulusFrameMap a g hg P).comp f) := by
  unfold puncturedFourAnnulusGlobalFrameMap
  exact extends_dimensionHomeomorph_iff _ _ ((e.puncturedFourAnnulusFrameMap a g hg P).comp f)

def fourAnnulusInnerObstruction : ZMod 2 :=
  sphereThirdObstruction ((e.ambientDimension - 7) + 2)
    ((e.puncturedFourAnnulusGlobalFrameMap a g hg P).comp P.innerBoundary)

def fourAnnulusOuterObstruction : ZMod 2 :=
  sphereThirdObstruction ((e.ambientDimension - 7) + 2)
    ((e.puncturedFourAnnulusGlobalFrameMap a g hg P).comp P.outerBoundary)

def fourAnnulusLinkObstruction (x : AnnulusDoublePoints.singularSet g) : ZMod 2 :=
  sphereThirdObstruction ((e.ambientDimension - 7) + 2)
    ((e.puncturedFourAnnulusGlobalFrameMap a g hg P).comp (P.linkingSphere x))

theorem fourAnnulusLinkObstruction_one (x : AnnulusDoublePoints.singularSet g) :
    e.fourAnnulusLinkObstruction a g hg P x = 1 := by
  have hne : e.fourAnnulusLinkObstruction a g hg P x ≠ 0 := by
    intro hz
    have he := (sphereThirdObstruction_zero_iff_extension _ _).mp hz
    have hf :=
      (e.puncturedFourAnnulusGlobalFrameMap_extends_iff a g hg P (P.linkingSphere x)).mp he
    rw [e.puncturedFourAnnulusFrameMap_link a g hg P x] at hf
    exact (P.ball x).normalized_localGlobalOperatorLink_not_extends e a
      (fun y hy ↦ hg y (openDomain_subset_domain 3
        ((P.ball x).closedRegion_subset_interior hy))) hf
  exact zmodTwo_eq_of_zero_iff _ _ (by simp [hne])

end NoExoticSixSphere.EuclideanEmbedding
