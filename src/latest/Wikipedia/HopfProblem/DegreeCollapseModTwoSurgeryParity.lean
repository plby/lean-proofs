import Wikipedia.HopfProblem.DegreeCollapseModTwoSurgeryMap
import Wikipedia.HopfProblem.DegreeCollapseSurgeryHomologyParity

/-!
# The actual mod-two surgery map preserves geometric parity and intersection

Every class in the actual orthogonal complement is the coefficient
reduction of a class in the exact integer detector kernel. The native
surgery map retains the coefficient-reduction formula, so the checked
integral parity and intersection comparisons give the actual mod-two
comparisons. The new atlas, framing, connectivity, and coefficient module
are the original constructions throughout.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct SmoothCube
open SingularMayerVietoris PeriodTorusHigherHomology SphereHomologyCoefficients

attribute [local instance] modHomologyModule

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [SimplyConnectedSpace M]
  [Subsingleton (SingularHomology M 2)]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r : TubularRetraction e) (m : M) [Subsingleton (π_ 2 M m)]
  (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hR : A.radius = 2)
  (d : SingularHomology M 3) (hd : detector f A hR d = 1)

theorem modTwoSurgeryMap_parity :
    letI := UnitSurgery.targetChartedSpace A hR;
    letI := UnitSurgery.target_isManifold A hR;
    letI := UnitSurgery.compactSpace_target A hR;
    letI : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
      (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1;
    ∀ (r' : TubularRetraction (UnitSurgery.inducedEmbedding A hR)) (m' : UnitSurgery.Target A hR),
      letI : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
        (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m';
      ∀ x : LinearMap.ker (orthogonalFunctional e r m f),
        (UnitSurgery.inducedEmbedding A hR).modTwoHomologyParity
          (UnitSurgery.normalFraming A hR) r' m' (modTwoSurgeryMap e a r m f A hR d hd x) =
        e.modTwoHomologyParity a r m x := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  let : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1
  intro r' m'
  let : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m'
  intro x
  obtain ⟨c, rfl⟩ := kernelReduction_surjective e a r m f A hR d hd x
  have hF := modTwoSurgeryMap_reduction e a r m f A hR d hd c
  have hn := nativeLift_parity f A hR d hd r m r' m' c
  have hr := (UnitSurgery.inducedEmbedding A hR).modTwoHomologyParity_reduction
    (UnitSurgery.normalFraming A hR) r' m' (nativeLift f A hR d hd c)
  have ho := e.modTwoHomologyParity_reduction a r m c.val
  exact (congrArg ((UnitSurgery.inducedEmbedding A hR).modTwoHomologyParity
    (UnitSurgery.normalFraming A hR) r' m') hF).trans (hr.trans (hn.trans ho.symm))

theorem modTwoSurgeryMap_intersection :
    letI := UnitSurgery.targetChartedSpace A hR;
    letI := UnitSurgery.target_isManifold A hR;
    letI := UnitSurgery.compactSpace_target A hR;
    letI : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
      (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1;
    ∀ (r' : TubularRetraction (UnitSurgery.inducedEmbedding A hR)) (m' : UnitSurgery.Target A hR),
      letI : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
        (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m';
      ∀ x y : LinearMap.ker (orthogonalFunctional e r m f),
        (UnitSurgery.inducedEmbedding A hR).modTwoHomologyIntersection r' m'
          (modTwoSurgeryMap e a r m f A hR d hd x) (modTwoSurgeryMap e a r m f A hR d hd y) =
        e.modTwoHomologyIntersection r m x y := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  let : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1
  intro r' m'
  let : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m'
  intro x y
  obtain ⟨c, rfl⟩ := kernelReduction_surjective e a r m f A hR d hd x
  obtain ⟨k, rfl⟩ := kernelReduction_surjective e a r m f A hR d hd y
  have hF := modTwoSurgeryMap_reduction e a r m f A hR d hd c
  have hG := modTwoSurgeryMap_reduction e a r m f A hR d hd k
  have hn := nativeLift_intersection f A hR d hd r m r' m' c k
  have hr := (UnitSurgery.inducedEmbedding A hR).modTwoHomologyIntersection_reduction r' m'
    (nativeLift f A hR d hd c) (nativeLift f A hR d hd k)
  have ho := e.modTwoHomologyIntersection_reduction r m c.val k.val
  exact (congrArg₂ (fun u v : ModHomology 2 (UnitSurgery.Target A hR) 3 ↦
    (UnitSurgery.inducedEmbedding A hR).modTwoHomologyIntersection r' m' u v) hF hG).trans
    (hr.trans (hn.trans ho.symm))

include A hR d hd in
theorem modTwoParity_eq_of_surgeryMap_eq (x y : LinearMap.ker (orthogonalFunctional e r m f))
    (hxy : modTwoSurgeryMap e a r m f A hR d hd x = modTwoSurgeryMap e a r m f A hR d hd y) :
    e.modTwoHomologyParity a r m x = e.modTwoHomologyParity a r m y := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  let : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1
  obtain ⟨r'⟩ := (UnitSurgery.inducedEmbedding A hR).nonempty_tubularRetraction
    (UnitSurgery.normalFraming A hR)
  let m' : UnitSurgery.Target A hR := Classical.choice inferInstance
  let : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m'
  exact (modTwoSurgeryMap_parity e a r m f A hR d hd r' m' x).symm.trans
    ((congrArg ((UnitSurgery.inducedEmbedding A hR).modTwoHomologyParity
      (UnitSurgery.normalFraming A hR) r' m') hxy).trans
      (modTwoSurgeryMap_parity e a r m f A hR d hd r' m' y))

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector
