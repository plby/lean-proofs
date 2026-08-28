import Wikipedia.NoExoticSixSphere.RegularSlabRelativeFundamentalCap
import Wikipedia.NoExoticSixSphere.RelativePairCapConnecting

/-!
# The actual slab duality and its boundary connecting class

The original homology connecting map applied to the constructed relative
fundamental class satisfies the genuine connecting-cap square. Duality
and the cohomology sequence then identify the kernel of its capped
inclusion map with the image of actual cohomology restriction.

This does not yet identify the connecting class with the original
boundary fundamental class, so no intersection or Arf assertion is made.
-/

noncomputable section

open Module
open scoped Manifold ContDiff
open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.RegularCollaredCylinder

open CylinderFiberSlab
open ModTwoCapProduct (Coefficient)

variable {B H M C H' N : Type}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [TopologicalSpace H] {I : ModelWithCorners ℝ B H} [I.Boundaryless]
  [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M] [CompactSpace M]
  [NormedAddCommGroup C] [NormedSpace ℝ C] [FiniteDimensional ℝ C]
  [TopologicalSpace H'] {J : ModelWithCorners ℝ C H'} [J.Boundaryless]
  [TopologicalSpace N] [T2Space N] [ChartedSpace H' N] [IsManifold J ∞ N]
  {z : N} {s t : ℝ} (d : RegularCollaredCylinder (M := M) I J z s t)
  (n : ℕ) (hd : finrank ℝ (ℝ × B) = finrank ℝ C + (n + 3))

def boundaryConnectingClass : ModHomology 2 (BoundaryPush.ends d.map z s t) (n + 2) :=
  RelativeCoefficients.connecting Coefficient (BoundaryPush.ends d.map z s t) (n + 2)
    (d.relativeFundamentalClass n hd)

theorem boundaryDualityMap_connecting (p q : ℕ) (h : p + q = n + 2)
    (a : ModTwoCapProduct.Cohomology (BoundaryPush.ends d.map z s t) p) :
    d.boundaryDualityMap n hd (p + 1) q (by omega)
        (RelativeModTwoCochains.connecting (BoundaryPush.ends d.map z s t) p a) =
      modHomologyMap 2 (subtypeInclusion (BoundaryPush.ends d.map z s t)) q
        (ModTwoCapProduct.capProductInDegree (BoundaryPush.ends d.map z s t) h a
          (d.boundaryConnectingClass n hd)) := by
  rw [← d.cap_relativeFundamentalClass]
  exact RelativeModTwoCap.pair_connecting_capInDegree (BoundaryPush.ends d.map z s t) h a
    (d.relativeFundamentalClass n hd)

theorem boundaryConnectingCap_kernel (p q : ℕ) (h : p + q = n + 2)
    (a : ModTwoCapProduct.Cohomology (BoundaryPush.ends d.map z s t) p) :
    modHomologyMap 2 (subtypeInclusion (BoundaryPush.ends d.map z s t)) q
        (ModTwoCapProduct.capProductInDegree (BoundaryPush.ends d.map z s t) h a
          (d.boundaryConnectingClass n hd)) = 0 ↔
      ∃ b : ModTwoCapProduct.Cohomology (slab d.map z s t) p,
        ModTwoCapProduct.cohomologyPullback (subtypeInclusion (BoundaryPush.ends d.map z s t))
          p b = a := by
  rw [← d.boundaryDualityMap_connecting n hd p q h a]
  constructor
  · intro ha
    have hδ : a ∈ LinearMap.ker
        (RelativeModTwoCochains.connecting (BoundaryPush.ends d.map z s t) p) :=
      (d.boundaryDualityMap_bijective n hd (p + 1) q (by omega)).injective
        (ha.trans (d.boundaryDualityMap n hd (p + 1) q (by omega)).map_zero.symm)
    rw [← RelativeModTwoCochains.exact_at_subspace] at hδ
    exact hδ
  · intro ha
    have hδ : a ∈ LinearMap.range
        (ModTwoCapProduct.cohomologyPullback (subtypeInclusion (BoundaryPush.ends d.map z s t))
          p) := ha
    rw [RelativeModTwoCochains.exact_at_subspace] at hδ
    change RelativeModTwoCochains.connecting (BoundaryPush.ends d.map z s t) p a = 0 at hδ
    rw [hδ, map_zero]

end NoExoticSixSphere.RegularCollaredCylinder
