import Wikipedia.HopfProblem.DegreeCollapseIntegralProductCoreSupport
import Wikipedia.HopfProblem.DegreeCollapseIntegralCompactSupportHomeomorph
import Wikipedia.HopfProblem.DegreeCollapseIntegralOpenManifoldDuality
import Wikipedia.NoExoticSixSphere.SphereNormalHomology

/-!
# Original core-supported cohomology and cap in an actual open sphere tube

Original excision pulls the core-supported class into the product model.
The proved core-support equivalence and the actual homeomorphism map put
it in compact-support cohomology of the original open tube. Original cap
duality there gives an equivalence to the tube's third integral homology,
and its inclusion is exactly the original ambient absolute cap.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralTubeCore

open NoExoticSixSphere FirstHurewicz SingularMayerVietoris

variable {M : Type} [TopologicalSpace M] [T2Space M] (U : Opens M)
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] [ProperSpace F]
  (e : (Sphere 3 × F) ≃ₜ U)

abbrev modelCore : Compacts (Sphere 3 × F) := IntegralRadialSupport.compactSupport (Sphere 3) F 0

def tubeMap : C(Sphere 3 × F, M) := (subtypeInclusion (U : Set M)).comp (e : C(Sphere 3 × F, U))

omit [T2Space M] [NormedSpace ℝ F] [ProperSpace F] in
theorem tubeMap_isOpenEmbedding : Topology.IsOpenEmbedding (tubeMap U e) :=
  U.isOpen.isOpenEmbedding_subtypeVal.comp e.isOpenEmbedding

def coreSupport : Compacts M :=
  IntegralCompactSupportCohomology.mapCompact (tubeMap U e) (modelCore (F := F))

def coreToOpenEquiv (p : ℕ) :
    IntegralSupportedCohomology.Cohomology (coreSupport U e : Set M) p ≃ₗ[ℤ]
      IntegralCompactSupportCohomology.Cohomology U p :=
  (IntegralOpenEmbeddingSupport.restrictionEquiv (tubeMap U e) (tubeMap_isOpenEmbedding U e)
    (modelCore (F := F) : Set (Sphere 3 × F)) (modelCore (F := F)).isCompact
    (coreSupport U e : Set M) rfl p).trans
      ((IntegralRadialSupport.coreToCompactEquiv (Sphere 3) F p).trans
        (IntegralCompactSupportCohomology.homeomorphEquiv e p))

theorem inclusion_coreToOpenEquiv (p : ℕ)
    (a : IntegralSupportedCohomology.Cohomology (coreSupport U e : Set M) p) :
    IntegralCompactSupportCohomology.inclusion (U : Set M) U.isOpen p (coreToOpenEquiv U e p a) =
      IntegralCompactSupportCohomology.of M p (coreSupport U e) a := by
  let b := IntegralOpenEmbeddingSupport.restrictionEquiv
    (tubeMap U e) (tubeMap_isOpenEmbedding U e)
    (modelCore (F := F) : Set (Sphere 3 × F)) (modelCore (F := F)).isCompact
    (coreSupport U e : Set M) rfl p a
  change IntegralCompactSupportCohomology.inclusion (U : Set M) U.isOpen p
    (IntegralCompactSupportCohomology.openMap (e : C(Sphere 3 × F, U)) e.isOpenEmbedding p
      (IntegralCompactSupportCohomology.of (Sphere 3 × F) p (modelCore (F := F)) b)) = _
  have hi := LinearMap.congr_fun
    (IntegralCompactSupportCohomology.openMap_subtype (U : Set M) U.isOpen p)
    (IntegralCompactSupportCohomology.openMap (e : C(Sphere 3 × F, U)) e.isOpenEmbedding p
      (IntegralCompactSupportCohomology.of (Sphere 3 × F) p (modelCore (F := F)) b))
  have hc := IntegralCompactSupportCohomology.openMap_comp
    (e : C(Sphere 3 × F, U)) e.isOpenEmbedding (subtypeInclusion (U : Set M))
    U.isOpen.isOpenEmbedding_subtypeVal p
    (IntegralCompactSupportCohomology.of (Sphere 3 × F) p (modelCore (F := F)) b)
  have ho := IntegralCompactSupportCohomology.openMap_of
    (tubeMap U e) (tubeMap_isOpenEmbedding U e) p (modelCore (F := F)) b
  have hr := congrArg (IntegralCompactSupportCohomology.of M p (coreSupport U e))
    (IntegralOpenEmbeddingSupport.extension_restriction
      (tubeMap U e) (tubeMap_isOpenEmbedding U e)
      (modelCore (F := F) : Set (Sphere 3 × F)) (modelCore (F := F)).isCompact
      (coreSupport U e : Set M) rfl p a)
  exact hi.symm.trans (hc.trans (ho.trans hr))

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Fact (Module.finrank ℝ V = 7)]
  [ChartedSpace V M] [CompactSpace M] [IsManifold 𝓘(ℝ, V) ∞ M] [SimplyConnectedSpace M]

def capEquiv : IntegralSupportedCohomology.Cohomology (coreSupport U e : Set M) 4 ≃ₗ[ℤ]
    SingularHomology U 3 :=
  (coreToOpenEquiv U e 4).trans (IntegralOpenFundamentalClass.dualityEquiv (E := V) 4 U 4 3 rfl)

theorem capEquiv_inclusion
    (a : IntegralSupportedCohomology.Cohomology (coreSupport U e : Set M) 4) :
    singularHomologyMap (subtypeInclusion (U : Set M)) 3 (capEquiv (V := V) U e a) =
      IntegralCompactSupportCap.absoluteDualityMap (E := V) 4 M 4 3 rfl
        (IntegralSupportedCohomology.toAbsolute (coreSupport U e : Set M) 4 a) := by
  have he := IntegralOpenFundamentalClass.dualityMap_inclusion (E := V) 4
    (U : Set M) U.isOpen 4 3 rfl (coreToOpenEquiv U e 4 a)
  rw [inclusion_coreToOpenEquiv] at he
  exact he.trans ((IntegralCompactSupportCap.dualityMap_of (E := V) 4 M 4 3 rfl
    (coreSupport U e) a).trans
      (IntegralCompactSupportCap.absoluteDualityMap_forget (E := V) 4 M 4 3 rfl
        (coreSupport U e) a).symm)

end Wikipedia.HopfProblem.DegreeCollapse.IntegralTubeCore
