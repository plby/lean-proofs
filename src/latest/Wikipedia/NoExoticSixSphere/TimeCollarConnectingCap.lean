import Wikipedia.NoExoticSixSphere.TimeCollarRelativeFundamentalCap
import Wikipedia.NoExoticSixSphere.RelativePairCapConnecting

/-!
# Connecting cap for the actual collared half

The connecting image of the constructed relative fundamental class satisfies
the original pair's connecting-cap square. Its capped inclusion has kernel
equal to the image of actual cohomology restriction. Identifying this class
with the native zero boundary's fundamental class remains a separate step.
-/

noncomputable section

open Set Function ContinuousMap
open scoped Manifold ContDiff

namespace NoExoticSixSphere.TimeCollarDuality

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse Wikipedia.HopfProblem.DegreeCollapse.TimeCollar
open Wikipedia.HopfProblem.SphereHomologyCoefficients
open Wikipedia.HopfProblem.SingularMayerVietoris
open ModTwoCapProduct (Coefficient)

variable {M B : Type} [TopologicalSpace M] [TopologicalSpace B]
  [ChartedSpace (Vector 7) M] [IsManifold (𝓡 7) ∞ M] [T2Space M] [CompactSpace M]
  {t : M → ℝ} (C : TimeCollar t B)

def boundaryConnectingClass : ModHomology 2 (boundary t) 6 :=
  RelativeCoefficients.connecting Coefficient (boundary t) 6 (relativeFundamentalClass C)

theorem boundaryDualityMap_connecting (p q : ℕ) (h : p + q = 6)
    (a : ModTwoCapProduct.Cohomology (boundary t) p) :
    boundaryDualityMap C (p + 1) q (by omega)
        (RelativeModTwoCochains.connecting (boundary t) p a) =
      modHomologyMap 2 (subtypeInclusion (boundary t)) q
        (ModTwoCapProduct.capProductInDegree (boundary t) h a (boundaryConnectingClass C)) := by
  rw [← cap_relativeFundamentalClass]
  exact RelativeModTwoCap.pair_connecting_capInDegree (boundary t) h a
    (relativeFundamentalClass C)

theorem boundaryConnectingCap_kernel (p q : ℕ) (h : p + q = 6)
    (a : ModTwoCapProduct.Cohomology (boundary t) p) :
    modHomologyMap 2 (subtypeInclusion (boundary t)) q
        (ModTwoCapProduct.capProductInDegree (boundary t) h a (boundaryConnectingClass C)) = 0 ↔
      ∃ b : ModTwoCapProduct.Cohomology (NonnegativeHalf t) p,
        ModTwoCapProduct.cohomologyPullback (subtypeInclusion (boundary t)) p b = a := by
  rw [← boundaryDualityMap_connecting C p q h a]
  constructor
  · intro ha
    have hδ : a ∈ LinearMap.ker (RelativeModTwoCochains.connecting (boundary t) p) :=
      (boundaryDualityMap_bijective C (p + 1) q (by omega)).injective
        (ha.trans (boundaryDualityMap C (p + 1) q (by omega)).map_zero.symm)
    rw [← RelativeModTwoCochains.exact_at_subspace] at hδ
    exact hδ
  · intro ha
    have hδ : a ∈ LinearMap.range
        (ModTwoCapProduct.cohomologyPullback (subtypeInclusion (boundary t)) p) := ha
    rw [RelativeModTwoCochains.exact_at_subspace] at hδ
    change RelativeModTwoCochains.connecting (boundary t) p a = 0 at hδ
    rw [hδ, map_zero]

end NoExoticSixSphere.TimeCollarDuality
