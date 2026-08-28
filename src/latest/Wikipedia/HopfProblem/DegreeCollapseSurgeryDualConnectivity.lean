import Wikipedia.HopfProblem.DegreeCollapseSurgeryDualNormal
import Wikipedia.HopfProblem.DegreeCollapseSurgerySimpleConnectivity
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnected

/-!
# A geometric dual preserves two-connectivity in the actual framed surgery

Apply the single transverse crossing theorem to the original normalized
attaching face. Its core is the original map, with the native derivative
unchanged. Zero old H2 and the actual belt sequence give zero new H2.
The independently proved simple-connectivity preservation and genuine
second Hurewicz isomorphism then kill the new native second homotopy groups.
Existence of the required geometric dual is not asserted here.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceBody

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩
local instance : Fact (Module.finrank ℝ (Vector 3) = 2 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

theorem unitFace_coreMap_eq :
    FramedSurgery.coreMap (E := Vector 4) (UnitSurgery.face A hR) = f := by
  apply ContinuousMap.ext
  intro s
  exact A.tube_core s

theorem nativeBelt_homology_zero_of_single_dual
    (g : C(Sphere 3, M)) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (q s : Sphere 3) (hpoint : g q = f s)
    (hunique : ∀ x, g x ∈ range f → x = q)
    (htrans : Surjective ((mfderiv (𝓡 3) (𝓡 6) g q).coprod
      (mfderiv (𝓡 3) (𝓡 6) f s))) :
    singularHomologyMap (nativeBeltMap A hR) 2 = 0 := by
  apply SurgeryLink.single_transverse_dual_kills_belt
    (E := Vector 4) (UnitSurgery.face A hR) g hg q s
  · rwa [unitFace_coreMap_eq]
  · rwa [unitFace_coreMap_eq]
  · rwa [unitFace_coreMap_eq]

theorem native_second_homology_subsingleton_of_belt_zero
    [Subsingleton (SingularHomology M 2)] (hz : nativeBeltClass f A hR = 0) :
    Subsingleton (SingularHomology (UnitSurgery.Target A hR) 2) := by
  have hs : Submodule.span ℤ {nativeBeltClass f A hR} = ⊥ := by
    rw [hz]
    exact Submodule.span_zero_singleton ℤ
  have hzero (x : SingularHomology (UnitSurgery.Target A hR) 2) : x = 0 := by
    change x ∈ (⊥ : Submodule ℤ (SingularHomology (UnitSurgery.Target A hR) 2))
    rw [← hs, native_second_homology_span_belt f A hR]
    trivial
  exact ⟨fun x y => (hzero x).trans (hzero y).symm⟩

theorem nativeTarget_twoConnected_of_belt_zero
    [SimplyConnectedSpace M] [Subsingleton (SingularHomology M 2)]
    (hz : nativeBeltClass f A hR = 0) :
    SimplyConnectedSpace (UnitSurgery.Target A hR) ∧
      ∀ x : UnitSurgery.Target A hR, Subsingleton (π_ 2 (UnitSurgery.Target A hR) x) := by
  let : SimplyConnectedSpace (UnitSurgery.Target A hR) := nativeTarget_simplyConnected A hR
  let : Subsingleton (SingularHomology (UnitSurgery.Target A hR) 2) :=
    native_second_homology_subsingleton_of_belt_zero f A hR hz
  exact ⟨inferInstance, fun x =>
    (SecondHurewicz.SimplyConnected.hurewiczPi2Equiv x).injective.subsingleton⟩

theorem nativeTarget_twoConnected_of_single_dual
    [SimplyConnectedSpace M] [Subsingleton (SingularHomology M 2)]
    (g : C(Sphere 3, M)) (hg : ContMDiff (𝓡 3) (𝓡 6) ∞ g)
    (q s : Sphere 3) (hpoint : g q = f s)
    (hunique : ∀ x, g x ∈ range f → x = q)
    (htrans : Surjective ((mfderiv (𝓡 3) (𝓡 6) g q).coprod
      (mfderiv (𝓡 3) (𝓡 6) f s))) :
    SimplyConnectedSpace (UnitSurgery.Target A hR) ∧
      ∀ x : UnitSurgery.Target A hR, Subsingleton (π_ 2 (UnitSurgery.Target A hR) x) := by
  apply nativeTarget_twoConnected_of_belt_zero f A hR
  have h := nativeBelt_homology_zero_of_single_dual f A hR g hg q s hpoint hunique htrans
  change singularHomologyMap (nativeBeltMap A hR) 2 (unitSphereTopClass 1) = 0
  rw [h, LinearMap.zero_apply]

end Wikipedia.HopfProblem.DegreeCollapse.TraceBody
