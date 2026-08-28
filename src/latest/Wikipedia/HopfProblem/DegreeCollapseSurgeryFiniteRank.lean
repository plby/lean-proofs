import Wikipedia.HopfProblem.DegreeCollapseSurgeryRank
import Wikipedia.HopfProblem.DegreeCollapseCompactHomologyFinite

/-!
# Actual compact dual surgery strictly reduces middle rank

The proved native Morse attachment argument supplies finite generation
of the original compact manifold's H3. Thus the geometric rank decrease
has no remaining homology-finiteness or freeness hypothesis. Together
with the actual belt-vanishing and Hurewicz results it gives a single
two-connectivity-preserving rank reduction under the explicit framed
geometric-dual hypothesis. Such a dual still has to be constructed.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceBody

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hR : A.radius = 2)
  (B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M)
  (q u : Sphere 3)
  (hcross : ∀ x y, f x = FramedSurgery.coreMap (E := Vector 4) B y ↔ x = q ∧ y = u)
  (htrans : Surjective ((mfderiv (𝓡 3) (𝓡 6) f q).coprod
    (mfderiv (𝓡 3) (𝓡 6) (FramedSurgery.coreMap (E := Vector 4) B) u)))

include hcross htrans in
theorem compact_middle_finrank_drop_of_dual :
    Module.finrank ℤ (SingularHomology (UnitSurgery.Target A hR) 3) + 2 ≤
      Module.finrank ℤ (SingularHomology M 3) := by
  let : Module.Finite ℤ (SingularHomology M 3) :=
    MorseFiniteness.compactManifold_middleHomology_finite (Vector 6) M
  exact middle_finrank_drop_of_dual f A hR B q u hcross htrans

include hcross htrans in
theorem compact_middle_finrank_strict_decrease_of_dual :
    Module.finrank ℤ (SingularHomology (UnitSurgery.Target A hR) 3) <
      Module.finrank ℤ (SingularHomology M 3) := by
  have h := compact_middle_finrank_drop_of_dual f A hR B q u hcross htrans
  omega

include hcross htrans in
theorem compact_dual_surgery_reduction
    [SimplyConnectedSpace M] [Subsingleton (SingularHomology M 2)] :
    SimplyConnectedSpace (UnitSurgery.Target A hR) ∧
      (∀ x : UnitSurgery.Target A hR, Subsingleton (π_ 2 (UnitSurgery.Target A hR) x)) ∧
      Module.finrank ℤ (SingularHomology (UnitSurgery.Target A hR) 3) + 2 ≤
        Module.finrank ℤ (SingularHomology M 3) := by
  obtain ⟨_, _, hz⟩ := geometric_dual_primitive_and_belt_zero f A hR B q u hcross htrans
  have hconn := nativeTarget_twoConnected_of_belt_zero f A hR hz
  exact ⟨hconn.1, hconn.2, compact_middle_finrank_drop_of_dual f A hR B q u hcross htrans⟩

end Wikipedia.HopfProblem.DegreeCollapse.TraceBody
