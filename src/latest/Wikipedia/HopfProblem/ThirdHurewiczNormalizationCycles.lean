import Wikipedia.HopfProblem.ThirdHurewiczNormalization
import Wikipedia.HopfProblem.ThirdHurewiczPrismCycles

/-!
# Three-stage normalization preserves actual third homology

Each coherent geometric stage acts on the original singular chain groups.
The already proved genuine four-dimensional prism formulas show that
the final whole-boundary-based three-cycle represents the original class.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SingularMayerVietoris SecondHurewicz.SimplyConnected

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)]

/-- Linearization of the actual normalized three-simplex maps. -/
def normalizedThreeChain : Chains X 3 →ₗ[ℤ] Chains X 3 :=
  chainLift X 3 fun smp => simplexChain X 3 (normalizedThreeSimplex x smp).val

@[simp] theorem normalizedThreeChain_simplex (smp : SingularSimplex X 3) :
    normalizedThreeChain x (simplexChain X 3 smp) =
      simplexChain X 3 (normalizedThreeSimplex x smp).val :=
  chainLift_simplex X 3 _ smp

theorem normalizedThreeChain_eq :
    normalizedThreeChain x =
      (simplexEndpointOperator 3 (triangleThreeSimplexHomotopy x) 1).comp
        ((simplexEndpointOperator 3 (tetrahedronEdgeStraighteningHomotopy x) 1).comp
          (simplexEndpointOperator 3 (vertexStraighteningHomotopy x 3) 1)) := by
  apply chainMap_ext X 3
  intro smp
  simp only [normalizedThreeChain_simplex, LinearMap.comp_apply, simplexEndpointOperator_simplex]
  rfl

def vertexNormalizedThreeCycle (c : ModuleHomology.Cycle (singularComplex X) 3) :
    ModuleHomology.Cycle (singularComplex X) 3 :=
  straightenedThreeCycle (vertexStraighteningHomotopy x 2) (vertexStraighteningHomotopy x 3)
    (vertexStraighteningHomotopy_face x 2) c

omit [Subsingleton (π_ 2 X x)] in
theorem vertexNormalizedThreeCycle_class (c : ModuleHomology.Cycle (singularComplex X) 3) :
    ModuleHomology.cycleClass (singularComplex X) 3 (vertexNormalizedThreeCycle x c) =
      ModuleHomology.cycleClass (singularComplex X) 3 c :=
  straightenedThreeCycle_class _ _ (vertexStraighteningHomotopy_face x 2)
    (vertexStraighteningHomotopy_timeSlice_zero x 3) c

def edgeNormalizedThreeCycle (c : ModuleHomology.Cycle (singularComplex X) 3) :
    ModuleHomology.Cycle (singularComplex X) 3 :=
  straightenedThreeCycle (triangleEdgeStraighteningHomotopy x)
    (tetrahedronEdgeStraighteningHomotopy x) (tetrahedronEdgeStraighteningHomotopy_face x)
    (vertexNormalizedThreeCycle x c)

omit [Subsingleton (π_ 2 X x)] in
theorem edgeNormalizedThreeCycle_class (c : ModuleHomology.Cycle (singularComplex X) 3) :
    ModuleHomology.cycleClass (singularComplex X) 3 (edgeNormalizedThreeCycle x c) =
      ModuleHomology.cycleClass (singularComplex X) 3 c := by
  have h₀ : ∀ smp, timeSlice (tetrahedronEdgeStraighteningHomotopy x smp) 0 = smp := by
    intro smp
    ext s
    exact tetrahedronEdgeStraighteningHomotopy_zero x smp s
  exact (straightenedThreeCycle_class _ _ (tetrahedronEdgeStraighteningHomotopy_face x) h₀
    (vertexNormalizedThreeCycle x c)).trans (vertexNormalizedThreeCycle_class x c)

/-- The final actual three-cycle after all three geometric stages. -/
def normalizedThreeCycle (c : ModuleHomology.Cycle (singularComplex X) 3) :
    ModuleHomology.Cycle (singularComplex X) 3 :=
  straightenedThreeCycle (triangleStraighteningHomotopy x) (triangleThreeSimplexHomotopy x)
    (triangleThreeSimplexHomotopy_face x) (edgeNormalizedThreeCycle x c)

@[simp] theorem normalizedThreeCycle_val (c : ModuleHomology.Cycle (singularComplex X) 3) :
    (normalizedThreeCycle x c).val = normalizedThreeChain x c.val := by
  rw [normalizedThreeChain_eq]
  rfl

/-- Actual integral third homology is unchanged by the three-stage normalization. -/
theorem normalizedThreeCycle_class (c : ModuleHomology.Cycle (singularComplex X) 3) :
    ModuleHomology.cycleClass (singularComplex X) 3 (normalizedThreeCycle x c) =
      ModuleHomology.cycleClass (singularComplex X) 3 c := by
  have h₀ : ∀ smp, timeSlice (triangleThreeSimplexHomotopy x smp) 0 = smp := by
    intro smp
    ext s
    exact triangleThreeSimplexHomotopy_zero x smp s
  exact (straightenedThreeCycle_class _ _ (triangleThreeSimplexHomotopy_face x) h₀
    (edgeNormalizedThreeCycle x c)).trans (edgeNormalizedThreeCycle_class x c)

end Wikipedia.HopfProblem.ThirdHurewicz
