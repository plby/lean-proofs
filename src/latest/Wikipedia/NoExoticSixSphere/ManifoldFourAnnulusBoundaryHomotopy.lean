import Wikipedia.NoExoticSixSphere.FourAnnulusBoundaryParity
import Wikipedia.NoExoticSixSphere.ManifoldFourAnnulusLinkParity
import Wikipedia.NoExoticSixSphere.InjectiveOperatorDimensionParity

/-!
# Homotopy of the normal-plus-derivative operators at both ends

The actual global frame has parity one at every retained singularity
link. The checked two-ended relation identifies its endpoint obstructions
when the singularity count is even. Reflecting homotopy through dimension
transport and normalization gives a homotopy between the original
injective operators. These operators still orthonormalize the prescribed
normal block; their actual annulus derivative columns are unchanged.
-/

noncomputable section

open Set Function Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel SphereAnnulus

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (g : Vector 4 → M)
  (hg : ∀ x ∈ domain 3, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
  (P : GenericFourAnnulus.ParityBallSystem g)

theorem fourAnnulusOuterObstruction_eq_inner
    (heven : Even (AnnulusDoublePoints.singularSet g).ncard) :
    e.fourAnnulusOuterObstruction a g hg P = e.fourAnnulusInnerObstruction a g hg P :=
  P.outer_frame_obstruction_eq_inner_of_even_links ((e.ambientDimension - 7) + 2)
    (e.puncturedFourAnnulusGlobalFrameMap a g hg P) heven
    (e.fourAnnulusLinkObstruction_one a g hg P)

theorem puncturedFourAnnulusGlobalFrameMap_outer_homotopic_inner
    (heven : Even (AnnulusDoublePoints.singularSet g).ncard) :
    ((e.puncturedFourAnnulusGlobalFrameMap a g hg P).comp P.outerBoundary).Homotopic
      ((e.puncturedFourAnnulusGlobalFrameMap a g hg P).comp P.innerBoundary) :=
  (sphereThirdObstruction_eq_iff_homotopic _ _ _).mp
    (e.fourAnnulusOuterObstruction_eq_inner a g hg P heven)

theorem puncturedFourAnnulusFrameMap_outer_homotopic_inner
    (heven : Even (AnnulusDoublePoints.singularSet g).ncard) :
    ((e.puncturedFourAnnulusFrameMap a g hg P).comp P.outerBoundary).Homotopic
      ((e.puncturedFourAnnulusFrameMap a g hg P).comp P.innerBoundary) := by
  have h := e.puncturedFourAnnulusGlobalFrameMap_outer_homotopic_inner a g hg P heven
  unfold puncturedFourAnnulusGlobalFrameMap at h
  exact (homotopic_dimensionHomeomorph_iff _ _ _ _).mp h

theorem puncturedFourAnnulusOperatorMap_outer_homotopic_inner
    (heven : Even (AnnulusDoublePoints.singularSet g).ncard) :
    ((e.puncturedFourAnnulusOperatorMap a g hg P).comp P.outerBoundary).Homotopic
      ((e.puncturedFourAnnulusOperatorMap a g hg P).comp P.innerBoundary) := by
  have h := e.puncturedFourAnnulusFrameMap_outer_homotopic_inner a g hg P heven
  exact (Monomorphism.normalize_homotopic_iff _ _).mp h

end NoExoticSixSphere.EuclideanEmbedding
