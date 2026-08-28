import Wikipedia.NoExoticSixSphere.CompactManifoldOpenExtension
import Wikipedia.NoExoticSixSphere.ZeroSecondHomologyCapPairing

/-!
# The original middle cap pairing on open components

The diagonal comparison follows from the actual extension cap square and
evaluation naturality. Disjoint components have zero cross pairing by
the literal zero pullback of their extended cohomology classes.
The second-homology hypotheses allow disconnected target manifolds.
-/

noncomputable section

open Wikipedia.HopfProblem SphereHomologyCoefficients SingularMayerVietoris

namespace NoExoticSixSphere.ZeroSecondHomologyCap

attribute [local instance] modHomologyModule

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [Fact (Module.finrank ℝ E = (3 + 2) + 1)]
  {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] [T2Space X] [T2Space Y]
  [ChartedSpace E X] [ChartedSpace E Y] [CompactSpace X] [CompactSpace Y]
  [Subsingleton (SingularHomology X 2)] [Subsingleton (SingularHomology Y 2)]
  (f : C(X, Y)) (hf : Topology.IsOpenEmbedding f)

include hf

theorem pairing_openEmbedding (a b : ModHomology 2 X 3) :
    pairing (E := E) Y (modHomologyMap 2 f 3 a) (modHomologyMap 2 f 3 b) =
      pairing (E := E) X a b := by
  obtain ⟨α, rfl⟩ := (ManifoldCapMap.dualityEquiv (E := E) 3 X 3 3 rfl).surjective a
  change pairing (E := E) Y (modHomologyMap 2 f 3
    (ManifoldCapMap.dualityMap (E := E) 3 X 3 3 rfl α)) (modHomologyMap 2 f 3 b) = _
  rw [← CompactManifoldOpenExtension.cap_map f hf 3 3 3 rfl α, pairing_cap,
    ← ZeroSecondHomologyEvaluation.evaluation_naturality X f,
    CompactManifoldOpenExtension.pullback_map]
  exact (pairing_cap (E := E) X α b).symm

theorem pairing_disjoint_openEmbeddings {Z : Type} [TopologicalSpace Z]
    [Subsingleton (SingularHomology Z 2)] (g : C(Z, Y))
    (hd : Disjoint (Set.range f) (Set.range g))
    (a : ModHomology 2 X 3) (b : ModHomology 2 Z 3) :
    pairing (E := E) Y (modHomologyMap 2 f 3 a) (modHomologyMap 2 g 3 b) = 0 := by
  obtain ⟨α, rfl⟩ := (ManifoldCapMap.dualityEquiv (E := E) 3 X 3 3 rfl).surjective a
  change pairing (E := E) Y (modHomologyMap 2 f 3
    (ManifoldCapMap.dualityMap (E := E) 3 X 3 3 rfl α)) (modHomologyMap 2 g 3 b) = 0
  rw [← CompactManifoldOpenExtension.cap_map f hf 3 3 3 rfl α, pairing_cap,
    ← ZeroSecondHomologyEvaluation.evaluation_naturality Z g,
    CompactManifoldOpenExtension.pullback_map_disjoint f hf 3 g hd, map_zero]
  rfl

end NoExoticSixSphere.ZeroSecondHomologyCap
