import Wikipedia.HopfProblem.DegreeCollapseIntegralTubeCoreEquivalence
import Wikipedia.HopfProblem.SphereHomologyTop

/-!
# Original cap of a core-supported generator is a unit times the original core

The original sphere marking and the actual zero-section homotopy equivalence
mark the open tube's third integral homology. Bijectivity of the original
core cap sends a cohomology generator to a homology generator. The marking
then proves that its coefficient on the original core is an integer unit.
The original ambient cap comparison retains that same geometric core map.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.IntegralTubeCore

open NoExoticSixSphere SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

variable {M : Type} [TopologicalSpace M] [T2Space M] (U : Opens M)
  {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (e : (Sphere 3 × F) ≃ₜ U)

def coreInOpen : C(Sphere 3, U) :=
  (e : C(Sphere 3 × F, U)).comp (SphereNormalHomology.zeroSection F)

def coreHomologyEquiv : SingularHomology (Sphere 3) 3 ≃ₗ[ℤ] SingularHomology U 3 :=
  (homotopyEquivHomologyEquiv (SphereNormalHomology.projectionEquiv F).symm 3).trans
    (homeomorphHomologyEquiv e 3)

omit [T2Space M] in
theorem coreHomologyEquiv_apply (a : SingularHomology (Sphere 3) 3) :
    coreHomologyEquiv U e a = singularHomologyMap (coreInOpen U e) 3 a := by
  change singularHomologyMap (e : C(Sphere 3 × F, U)) 3
    (singularHomologyMap (SphereNormalHomology.zeroSection F) 3 a) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

def coreClass : SingularHomology U 3 :=
  singularHomologyMap (coreInOpen U e) 3 (unitSphereTopClass 2)

def coreMarking : SingularHomology U 3 ≃ₗ[ℤ] ℤ :=
  (coreHomologyEquiv U e).symm.trans (unitSphereHomologyTopEquiv 2)

omit [T2Space M] in
theorem coreMarking_coreClass : coreMarking U e (coreClass U e) = 1 := by
  change coreMarking U e (singularHomologyMap (coreInOpen U e) 3 (unitSphereTopClass 2)) = 1
  rw [← coreHomologyEquiv_apply]
  change unitSphereHomologyTopEquiv 2
    ((coreHomologyEquiv U e).symm (coreHomologyEquiv U e (unitSphereTopClass 2))) = 1
  rw [LinearEquiv.symm_apply_apply]
  exact unitSphereHomologyTopEquiv_topClass 2

variable [ProperSpace F]
  {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [Fact (Module.finrank ℝ V = 7)]
  [ChartedSpace V M] [CompactSpace M] [IsManifold 𝓘(ℝ, V) ∞ M] [SimplyConnectedSpace M]

theorem cap_generator_unit
    (a : IntegralSupportedCohomology.Cohomology (coreSupport U e : Set M) 4)
    (ha : ∀ b : IntegralSupportedCohomology.Cohomology (coreSupport U e : Set M) 4,
      ∃ l : ℤ, l • a = b) :
    ∃ k : ℤ, IsUnit k ∧ capEquiv (V := V) U e a = k • coreClass U e := by
  let C := capEquiv (V := V) U e
  let m := coreMarking U e
  let k : ℤ := m (C a)
  have hm : m (coreClass U e) = 1 := coreMarking_coreClass U e
  have hk : IsUnit k := by
    obtain ⟨l, hl⟩ := ha (C.symm (coreClass U e))
    have hz := congrArg (fun b ↦ m (C b)) hl
    rw [map_zsmul, map_zsmul, LinearEquiv.apply_symm_apply, hm] at hz
    change l • k = 1 at hz
    rw [zsmul_eq_mul, Int.cast_id] at hz
    exact isUnit_iff_dvd_one.mpr ⟨l, by rw [mul_comm]; exact hz.symm⟩
  refine ⟨k, hk, m.injective ?_⟩
  rw [map_zsmul, hm]
  change k = k • (1 : ℤ)
  simp only [zsmul_eq_mul, Int.cast_id, mul_one]

theorem absoluteCap_generator_unit
    (a : IntegralSupportedCohomology.Cohomology (coreSupport U e : Set M) 4)
    (ha : ∀ b : IntegralSupportedCohomology.Cohomology (coreSupport U e : Set M) 4,
      ∃ l : ℤ, l • a = b) :
    ∃ k : ℤ, IsUnit k ∧
      IntegralCompactSupportCap.absoluteDualityMap (E := V) 4 M 4 3 rfl
        (IntegralSupportedCohomology.toAbsolute (coreSupport U e : Set M) 4 a) =
      k • singularHomologyMap ((tubeMap U e).comp (SphereNormalHomology.zeroSection F)) 3
        (unitSphereTopClass 2) := by
  obtain ⟨k, hk, he⟩ := cap_generator_unit (V := V) U e a ha
  refine ⟨k, hk, ?_⟩
  rw [← capEquiv_inclusion (V := V) U e a, he, map_zsmul]
  change k • singularHomologyMap (subtypeInclusion (U : Set M)) 3
    (singularHomologyMap (coreInOpen U e) 3 (unitSphereTopClass 2)) = _
  rw [← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

end Wikipedia.HopfProblem.DegreeCollapse.IntegralTubeCore
