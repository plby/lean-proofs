import Wikipedia.NoExoticSixSphere.CollaredZeroCapKernel
import Wikipedia.NoExoticSixSphere.NativeBoundarySumHomology
import Wikipedia.NoExoticSixSphere.SphereHomologyGroups

/-!
# The actual component kernel when the other boundary component has zero middle homology

The actual right component inclusion carries all native mod-two middle
classes if the left component's middle group is zero. The open-component
cap comparison therefore transfers self-orthogonality from the whole
zero boundary to that component's original cap and geometric polar forms.
The candidate six-sphere case supplies the vanishing groups from its given
homeomorphism without changing its atlas. Quadratic vanishing is separate.
-/

noncomputable section

open Function ContinuousMap
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.CollaredZero

open GLOrthonormalization Wikipedia.HopfProblem.DegreeCollapse
open Wikipedia.HopfProblem.SingularMayerVietoris Wikipedia.HopfProblem.SphereHomologyCoefficients

attribute [local instance] modHomologyModule

variable {B X Y : Type} [TopologicalSpace B] [TopologicalSpace X] [TopologicalSpace Y]
  (S : LowCollaredSevenState B) (h : (X ⊕ Y) ≃ₜ S.Zero)

def rightHalfInclusion : C(Y, S.PositiveHalf) :=
  (halfInclusion S).comp (NativeBoundarySum.inr h)

theorem rightHalfInclusion_homology (b : ModHomology 2 Y 3) :
    modHomologyMap 2 (halfInclusion S) 3 (modHomologyMap 2 (NativeBoundarySum.inr h) 3 b) =
      modHomologyMap 2 (rightHalfInclusion S h) 3 b :=
  (LinearMap.congr_fun
    (modHomologyMap_comp 2 (NativeBoundarySum.inr h) (halfInclusion S) 3) b).symm

variable [ChartedSpace (Vector 6) Y] [T2Space Y] [CompactSpace Y]
  [Subsingleton (SingularHomology S.PositiveHalf 2)]

local instance : Fact (Module.finrank ℝ (Vector 6) = (3 + 2) + 1) := ⟨by simp⟩

section Cap

variable [Subsingleton (SingularHomology X 2)] [Subsingleton (SingularHomology Y 2)]
  [Subsingleton (ModHomology 2 X 3)]

theorem rightCapKernel_selfOrthogonal (b : ModHomology 2 Y 3) :
    (∀ a : ModHomology 2 Y 3, modHomologyMap 2 (rightHalfInclusion S h) 3 a = 0 →
      ZeroSecondHomologyCap.pairing (E := Vector 6) Y a b = 0) ↔
      modHomologyMap 2 (rightHalfInclusion S h) 3 b = 0 := by
  let := S.zeroAtlas
  let := zeroCompactSpace S
  let := NativeBoundarySum.target_secondHomology_subsingleton h
  have hpair (a b : ModHomology 2 Y 3) :=
    ZeroSecondHomologyCap.pairing_openEmbedding (E := Vector 6)
      (NativeBoundarySum.inr h) (NativeBoundarySum.isOpenEmbedding_inr h) a b
  constructor
  · intro hb
    rw [← rightHalfInclusion_homology S h b]
    apply (capKernel_selfOrthogonal S _).mp
    intro a ha
    obtain ⟨a, rfl⟩ := NativeBoundarySum.inr_modTwo_surjective h a
    exact (hpair a b).trans (hb a ((rightHalfInclusion_homology S h a).symm.trans ha))
  · intro hb a ha
    exact (hpair a b).symm.trans
      ((capKernel_selfOrthogonal S _).mpr ((rightHalfInclusion_homology S h b).trans hb) _
        ((rightHalfInclusion_homology S h a).trans ha))

end Cap

variable [IsManifold (𝓡 6) ∞ Y] [SimplyConnectedSpace Y] (y : Y)
  [Subsingleton (π_ 2 Y y)] (e : EuclideanEmbedding 6 Y)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : e.TubularRetraction)

theorem rightPolarKernel_selfOrthogonal
    [Subsingleton (SingularHomology X 2)] [Subsingleton (ModHomology 2 X 3)]
    (b : ModHomology 2 Y 3) :
    (∀ a : ModHomology 2 Y 3, modHomologyMap 2 (rightHalfInclusion S h) 3 a = 0 →
      (e.modTwoHomologyQuadraticForm ν r y).polarBilin a b = 0) ↔
      modHomologyMap 2 (rightHalfInclusion S h) 3 b = 0 := by
  let := TwoConnectedCoefficients.secondHomology_subsingleton y
  have hpair (a b : ModHomology 2 Y 3) :
      ZeroSecondHomologyCap.pairing (E := Vector 6) Y a b =
        (e.modTwoHomologyQuadraticForm ν r y).polarBilin a b := by
    rw [ZeroSecondHomologyCap.pairing_eq_connected Y y, e.modTwoHomologyQuadraticForm_polar]
    exact e.cap_pairing_eq_geometric ν r y a b
  simpa only [hpair] using rightCapKernel_selfOrthogonal S h b

theorem rightPolarKernel_selfOrthogonal_of_sixSphere (hX : X ≃ₜ Sphere 6)
    (b : ModHomology 2 Y 3) :
    (∀ a : ModHomology 2 Y 3, modHomologyMap 2 (rightHalfInclusion S h) 3 a = 0 →
      (e.modTwoHomologyQuadraticForm ν r y).polarBilin a b = 0) ↔
      modHomologyMap 2 (rightHalfInclusion S h) 3 b = 0 := by
  let := subsingleton_singularHomology_of_homeomorph_sphere
    (k := 2) (by decide) (by decide) (by decide) hX
  let := sixSphere_middleModTwoHomology_subsingleton hX
  exact rightPolarKernel_selfOrthogonal S h y e ν r b

end NoExoticSixSphere.CollaredZero
