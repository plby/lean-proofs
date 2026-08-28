import Wikipedia.NoExoticSixSphere.CollaredZeroCapKernel
import Wikipedia.NoExoticSixSphere.ClopenSphereParity

/-!
# Quadratic vanishing on a native clopen boundary component

Only the chosen clopen component is assumed two-connected. Its original
restricted embedding and full induced normal frame are retained. Native
integral representatives, the actual coefficient kernel lift, and the
even-half-image sphere theorem prove vanishing on its full mod-two kernel.
The whole zero boundary may be disconnected.
-/

noncomputable section

open Function ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CollaredZero

open GLOrthonormalization EuclideanEmbedding SmoothCube
open Wikipedia.HopfProblem.DegreeCollapse
open Wikipedia.HopfProblem.SingularMayerVietoris Wikipedia.HopfProblem.SphereHomologyCoefficients
open Wikipedia.HopfProblem.PeriodTorusHigherHomology

attribute [local instance] modHomologyModule

variable {B : Type} [TopologicalSpace B] (S : LowCollaredSevenState B)
  (U : TopologicalSpace.Opens S.Zero) (hU : IsClosed (U : Set S.Zero))

def clopenHalfInclusion : C(U, S.PositiveHalf) :=
  (halfInclusion S).comp (subtypeInclusion (U : Set S.Zero))

include hU in
theorem clopenCompactSpace : CompactSpace U := by
  let := zeroCompactSpace S
  exact hU.isClosedEmbedding_subtypeVal.compactSpace

variable [SimplyConnectedSpace S.PositiveHalf]
  [Subsingleton (SingularHomology S.PositiveHalf 2)]
  [SimplyConnectedSpace U] (m : S.Space) (u : U) [Subsingleton (π_ 2 U u)]

theorem integralParity_zero_of_even_clopen_half_image :
    letI := S.zeroAtlas;
    letI := S.zero_isManifold;
    letI := clopenCompactSpace S U hU;
    let eU := ClopenEmbedding.restrict (embedding S) U hU;
    let aU := ClopenEmbedding.restrictNormalFrame (embedding S) U hU (normalFrame S m);
    ∀ (rU : eU.TubularRetraction) (x : SingularHomology U 3)
      (y : SingularHomology S.PositiveHalf 3),
      singularHomologyMap (clopenHalfInclusion S U) 3 x = (2 : ℤ) • y →
        eU.integralHomologyParity aU rU u x = 0 := by
  let := S.zeroAtlas
  let := S.zero_isManifold
  let := clopenCompactSpace S U hU
  let : SimplyConnectedSpace (TimeCollar.NonnegativeHalf S.zeroTimeMap) :=
    ‹SimplyConnectedSpace S.PositiveHalf›
  let : Subsingleton (SingularHomology (TimeCollar.NonnegativeHalf S.zeroTimeMap) 2) :=
    ‹Subsingleton (SingularHomology S.PositiveHalf 2)›
  let eU := ClopenEmbedding.restrict (embedding S) U hU
  let aU := ClopenEmbedding.restrictNormalFrame (embedding S) U hU (normalFrame S m)
  dsimp only
  intro rU x y hclass
  let f := (integralClassRepresentative u x).val
  obtain ⟨g, hg, H, hd, hi⟩ := TripleParameters.exists_embedded_sphere_representative eU rU f
  have hgclass : integralSphereClass g = x :=
    (integralSphereClass_homotopic H).symm.trans (integralSphereClass_representative u x)
  rw [← hgclass, integralHomologyParity_sphereClass,
    geometricSphereParity_eq_of_embedding _ _ _ _ hg hi.injective hd]
  rw [ClopenSphereParity.sphereParity_restrict (embedding S) U hU (normalFrame S m)
    g hg hd hi.injective]
  have hGclass : singularHomologyMap (halfInclusion S) 3
      (integralSphereClass ((subtypeInclusion (U : Set S.Zero)).comp g)) = (2 : ℤ) • y := by
    rw [integralSphereClass_comp, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
    change singularHomologyMap (clopenHalfInclusion S U) 3 (integralSphereClass g) = _
    rw [hgclass]
    exact hclass
  exact EmbeddedTime.sphereParity_zero_of_even_cube_half_image
    S.embedding (retraction S m) S.zeroTimeMap S.time_smooth S.time_regular
    S.normalFrame m S.collar ((subtypeInclusion (U : Set S.Zero)).comp g) y hGclass
    (ClopenSphereParity.smooth_inclusion_comp U g hg) (Subtype.val_injective.comp hi.injective)
    (ClopenSphereParity.inclusion_comp_mfderiv_injective U g hg hd)

theorem modTwoQuadraticForm_zero_on_clopen_kernel :
    letI := S.zeroAtlas;
    letI := S.zero_isManifold;
    letI := clopenCompactSpace S U hU;
    let eU := ClopenEmbedding.restrict (embedding S) U hU;
    let aU := ClopenEmbedding.restrictNormalFrame (embedding S) U hU (normalFrame S m);
    ∀ (rU : eU.TubularRetraction) (b : ModHomology 2 U 3),
      modHomologyMap 2 (clopenHalfInclusion S U) 3 b = 0 →
        eU.modTwoHomologyQuadraticForm aU rU u b = 0 := by
  let := S.zeroAtlas
  let := S.zero_isManifold
  let := clopenCompactSpace S U hU
  let := TwoConnectedCoefficients.secondHomology_subsingleton u
  dsimp only
  intro rU b hker
  obtain ⟨x, y, hx, hclass⟩ :=
    (MiddleKernelCoefficients.kernel_iff_has_half (clopenHalfInclusion S U) b).mp hker
  rw [modTwoHomologyQuadraticForm_apply, ← hx, modTwoHomologyParity_reduction]
  exact integralParity_zero_of_even_clopen_half_image S U hU m u rU x y hclass

end NoExoticSixSphere.CollaredZero
