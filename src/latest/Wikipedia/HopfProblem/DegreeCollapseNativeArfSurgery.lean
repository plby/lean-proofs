import Wikipedia.HopfProblem.DegreeCollapseNativeHyperbolicSurgery
import Wikipedia.HopfProblem.DegreeCollapseHyperbolicArfComparison
import Wikipedia.NoExoticSixSphere.CompactMiddleHomologyFinite

/-!
# Actual native surgery preserves the geometric Arf invariant

The original compact Morse construction and actual coefficient reduction
make native mod-two H3 a finite type. Define its integer geometric Gauss
sum from that finite type; the Arf invariant still takes actual polar
nondegeneracy as a hypothesis. The constructed native hyperbolic isometry
proves equivalence of old/new nondegeneracy, the exact factor-two Gauss-sum
formula, and Arf preservation from old nondegeneracy. No homology-finiteness
assumption or new-end nondegeneracy hypothesis is supplied.
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
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)
  (r : TubularRetraction e) (m : M) [Subsingleton (π_ 2 M m)]

def geometricGaussSum : ℤ := by
  let : Finite (ModHomology 2 M 3) := compactManifold_modTwoMiddleHomology_finiteType (Vector 6) M m
  let : Fintype (ModHomology 2 M 3) := Fintype.ofFinite _
  exact Arf.gaussSum (e.modTwoHomologyQuadraticForm a r m)

def geometricArf (hq : (e.modTwoHomologyQuadraticForm a r m).polarBilin.Nondegenerate) : ZMod 2 := by
  let : Finite (ModHomology 2 M 3) := compactManifold_modTwoMiddleHomology_finiteType (Vector 6) M m
  let : Fintype (ModHomology 2 M 3) := Fintype.ofFinite _
  exact Arf.invariant (e.modTwoHomologyQuadraticForm a r m) hq

theorem geometricArf_eq_gaussSign (hq : (e.modTwoHomologyQuadraticForm a r m).polarBilin.Nondegenerate) :
    geometricArf e a r m hq = Arf.signParity (geometricGaussSum e a r m) := rfl

variable [Subsingleton (SingularHomology M 2)]
  (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hR : A.radius = 2)
  (d : SingularHomology M 3) (hd : detector f A hR d = 1)

theorem native_quadratic_surgery_invariants :
    letI := UnitSurgery.targetChartedSpace A hR;
    letI := UnitSurgery.target_isManifold A hR;
    letI := UnitSurgery.compactSpace_target A hR;
    letI : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
      (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1;
    ∀ (r' : TubularRetraction (UnitSurgery.inducedEmbedding A hR)) (m' : UnitSurgery.Target A hR),
      letI : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
        (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m';
      ((e.modTwoHomologyQuadraticForm a r m).polarBilin.Nondegenerate ↔
        ((UnitSurgery.inducedEmbedding A hR).modTwoHomologyQuadraticForm
          (UnitSurgery.normalFraming A hR) r' m').polarBilin.Nondegenerate) ∧
      geometricGaussSum e a r m = 2 * geometricGaussSum (UnitSurgery.inducedEmbedding A hR)
        (UnitSurgery.normalFraming A hR) r' m' ∧
      (∀ hq : (e.modTwoHomologyQuadraticForm a r m).polarBilin.Nondegenerate,
        ∃ hq' : ((UnitSurgery.inducedEmbedding A hR).modTwoHomologyQuadraticForm
          (UnitSurgery.normalFraming A hR) r' m').polarBilin.Nondegenerate,
          geometricArf e a r m hq = geometricArf (UnitSurgery.inducedEmbedding A hR)
            (UnitSurgery.normalFraming A hR) r' m' hq') := by
  let := UnitSurgery.targetChartedSpace A hR
  let := UnitSurgery.target_isManifold A hR
  let := UnitSurgery.compactSpace_target A hR
  let : SimplyConnectedSpace (UnitSurgery.Target A hR) :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).1
  intro r' m'
  let : Subsingleton (π_ 2 (UnitSurgery.Target A hR) m') :=
    (FramedDual.compact_surgery_reduction_of_unit_homology f A hR d hd).2.1 m'
  let : Finite (ModHomology 2 M 3) := compactManifold_modTwoMiddleHomology_finiteType (Vector 6) M m
  let : Fintype (ModHomology 2 M 3) := Fintype.ofFinite _
  let : Finite (ModHomology 2 (UnitSurgery.Target A hR) 3) :=
    compactManifold_modTwoMiddleHomology_finiteType (Vector 6) (UnitSurgery.Target A hR) m'
  let : Fintype (ModHomology 2 (UnitSurgery.Target A hR) 3) := Fintype.ofFinite _
  let E := nativeHyperbolicSurgeryIsometry e a r m f A hR d hd r' m'
  refine ⟨HyperbolicReduction.nondegenerate_split_iff _ _ E, ?_, ?_⟩
  · change Arf.gaussSum (e.modTwoHomologyQuadraticForm a r m) =
      2 * Arf.gaussSum ((UnitSurgery.inducedEmbedding A hR).modTwoHomologyQuadraticForm
        (UnitSurgery.normalFraming A hR) r' m')
    exact HyperbolicReduction.gaussSum_split _ _ E
  · intro hq
    let hq' := HyperbolicReduction.nondegenerate_after_split _ _ E hq
    refine ⟨hq', ?_⟩
    change Arf.invariant (e.modTwoHomologyQuadraticForm a r m) hq =
      Arf.invariant ((UnitSurgery.inducedEmbedding A hR).modTwoHomologyQuadraticForm
        (UnitSurgery.normalFraming A hR) r' m') hq'
    exact HyperbolicReduction.arf_split _ _ E hq

end Wikipedia.HopfProblem.DegreeCollapse.SurgeryDetector
