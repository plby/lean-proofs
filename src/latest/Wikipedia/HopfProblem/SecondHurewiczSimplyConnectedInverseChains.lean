import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedNormalizationCycles
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedNormalizationTetrahedra
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedTriangleHomology
import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedDescentAugmentation

/-!
# The native second-homotopy assignment on actual singular chains

Each singular triangle is replaced by its actual based normalization and
assigned the resulting native second homotopy class. The geometric
tetrahedron relation proves that this linear assignment kills every actual
three-boundary. Its Hurewicz image on a two-cycle is the original class.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- Linear assignment from the original singular chains to actual native `π₂`. -/
def triangleClassOperator (x : X) : Chains X 2 →ₗ[ℤ] Additive (π_ 2 X x) :=
  chainLift X 2 fun smp => basedTriangleClass (normalizedTriangle x smp)

@[simp] theorem triangleClassOperator_simplex (x : X) (smp : SingularSimplex X 2) :
    triangleClassOperator x (simplexChain X 2 smp) =
      basedTriangleClass (normalizedTriangle x smp) :=
  chainLift_simplex X 2 _ smp

/-- The genuine tetrahedron relation kills the boundary of every chain,
not only a chosen collection of representatives. -/
theorem triangleClassOperator_boundary (x : X) (b : Chains X 3) :
    triangleClassOperator x (((singularComplex X).d 3 2).hom b) = 0 := by
  have h : (triangleClassOperator x).comp ((singularComplex X).d 3 2).hom = 0 := by
    apply chainMap_ext X 3
    intro smp
    simp only [LinearMap.comp_apply, boundary_simplex, map_sum, map_zsmul,
      triangleClassOperator_simplex, LinearMap.zero_apply]
    exact normalizedTriangle_boundary_relation x smp
  exact LinearMap.congr_fun h b

/-- Linear assignment of the corrected genuine two-cycle for each normalized triangle. -/
def normalizedTriangleCycleOperator (x : X) :
    Chains X 2 →ₗ[ℤ] ModuleHomology.Cycle (singularComplex X) 2 :=
  chainLift X 2 fun smp => basedTriangleCycle (normalizedTriangle x smp)

@[simp] theorem normalizedTriangleCycleOperator_simplex (x : X)
    (smp : SingularSimplex X 2) :
    normalizedTriangleCycleOperator x (simplexChain X 2 smp) =
      basedTriangleCycle (normalizedTriangle x smp) :=
  chainLift_simplex X 2 _ smp

theorem normalizedTriangleCycleOperator_val (x : X) (c : Chains X 2) :
    (normalizedTriangleCycleOperator x c).val =
      chainLift X 2 (fun smp => simplexChain X 2 (normalizedTriangle x smp).val -
        simplexChain X 2 (ContinuousMap.const (Simplex 2) x)) c := by
  have h : (ModuleHomology.Cycle (singularComplex X) 2).subtype.comp
        (normalizedTriangleCycleOperator x) =
      chainLift X 2 (fun smp => simplexChain X 2 (normalizedTriangle x smp).val -
        simplexChain X 2 (ContinuousMap.const (Simplex 2) x)) := by
    apply chainMap_ext X 2
    intro smp
    simp only [LinearMap.comp_apply, normalizedTriangleCycleOperator_simplex,
      Submodule.subtype_apply, basedTriangleCycle_val, chainLift_simplex]
  exact LinearMap.congr_fun h c

/-- The constant-triangle corrections cancel because an actual singular
two-cycle has total coefficient sum zero. -/
theorem normalizedTriangleCycleOperator_twoCycle (x : X)
    (c : ModuleHomology.Cycle (singularComplex X) 2) :
    normalizedTriangleCycleOperator x c.val = normalizedTwoCycle x c := by
  apply Subtype.ext
  rw [normalizedTriangleCycleOperator_val, chainLift_sub_constant_twoCycle,
    normalizedTwoCycle_val]
  rfl

/-- The Hurewicz image of the native assignment is the actual corrected
triangle-cycle assignment, as an equality of linear maps. -/
theorem hurewiczMap_comp_triangleClassOperator (x : X) :
    (hurewiczMap x).comp (triangleClassOperator x) =
      (ModuleHomology.cycleClass (singularComplex X) 2).comp
        (normalizedTriangleCycleOperator x) := by
  apply chainMap_ext X 2
  intro smp
  simp only [LinearMap.comp_apply, triangleClassOperator_simplex,
    normalizedTriangleCycleOperator_simplex]
  exact hurewicz_basedTriangleClass (normalizedTriangle x smp)

/-- On every actual two-cycle the assignment is a right inverse of the
already constructed native Hurewicz map. -/
theorem hurewiczMap_triangleClassOperator_twoCycle (x : X)
    (c : ModuleHomology.Cycle (singularComplex X) 2) :
    hurewiczMap x (triangleClassOperator x c.val) =
      ModuleHomology.cycleClass (singularComplex X) 2 c := by
  have h := LinearMap.congr_fun (hurewiczMap_comp_triangleClassOperator x) c.val
  change hurewiczMap x (triangleClassOperator x c.val) =
    ModuleHomology.cycleClass (singularComplex X) 2 (normalizedTriangleCycleOperator x c.val) at h
  rw [normalizedTriangleCycleOperator_twoCycle] at h
  exact h.trans (normalizedTwoCycle_class x c)

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
