import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedNormalization

/-!
# Straightening actual singular two-cycles

Both normalization stages are implemented on the original singular chain
groups. Their explicit prism boundaries prove that the final based-triangle
cycle represents exactly the original integral second homology class.
-/

noncomputable section

open scoped unitInterval Topology

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- Linearization of the actual normalized triangle maps. -/
def normalizedTwoChain (x : X) : Chains X 2 →ₗ[ℤ] Chains X 2 :=
  chainLift X 2 fun smp => simplexChain X 2 (normalizedTriangle x smp).val

@[simp] theorem normalizedTwoChain_simplex (x : X) (smp : SingularSimplex X 2) :
    normalizedTwoChain x (simplexChain X 2 smp) =
      simplexChain X 2 (normalizedTriangle x smp).val :=
  chainLift_simplex X 2 _ smp

/-- The linearized normalization is exactly the composition of the two
actual endpoint operators. -/
theorem normalizedTwoChain_eq (x : X) :
    normalizedTwoChain x =
      (simplexEndpointOperator 2 (triangleEdgeStraighteningHomotopy x) 1).comp
        (simplexEndpointOperator 2 (vertexStraighteningHomotopy x 2) 1) := by
  apply chainMap_ext X 2
  intro smp
  simp only [normalizedTwoChain_simplex, LinearMap.comp_apply, simplexEndpointOperator_simplex]
  rfl

/-- The vertex stage applied to an actual two-cycle. -/
def vertexNormalizedTwoCycle (x : X) (c : ModuleHomology.Cycle (singularComplex X) 2) :
    ModuleHomology.Cycle (singularComplex X) 2 :=
  straightenedTwoCycle (vertexStraighteningHomotopy x 1) (vertexStraighteningHomotopy x 2)
    (vertexStraighteningHomotopy_face x 1) c

theorem vertexNormalizedTwoCycle_class (x : X)
    (c : ModuleHomology.Cycle (singularComplex X) 2) :
    ModuleHomology.cycleClass (singularComplex X) 2 (vertexNormalizedTwoCycle x c) =
      ModuleHomology.cycleClass (singularComplex X) 2 c :=
  straightenedTwoCycle_class _ _ (vertexStraighteningHomotopy_face x 1)
    (vertexStraighteningHomotopy_timeSlice_zero x 2) c

/-- The final normalization retains a proof of the actual cycle equation. -/
def normalizedTwoCycle (x : X) (c : ModuleHomology.Cycle (singularComplex X) 2) :
    ModuleHomology.Cycle (singularComplex X) 2 :=
  straightenedTwoCycle (edgeStraighteningHomotopy x) (triangleEdgeStraighteningHomotopy x)
    (triangleEdgeStraighteningHomotopy_face x) (vertexNormalizedTwoCycle x c)

@[simp] theorem normalizedTwoCycle_val (x : X)
    (c : ModuleHomology.Cycle (singularComplex X) 2) :
    (normalizedTwoCycle x c).val = normalizedTwoChain x c.val := by
  rw [normalizedTwoChain_eq]
  rfl

/-- The two genuine prism constructions prove preservation of the original
categorical singular homology class. -/
theorem normalizedTwoCycle_class (x : X)
    (c : ModuleHomology.Cycle (singularComplex X) 2) :
    ModuleHomology.cycleClass (singularComplex X) 2 (normalizedTwoCycle x c) =
      ModuleHomology.cycleClass (singularComplex X) 2 c := by
  have h₀ : ∀ smp, timeSlice (triangleEdgeStraighteningHomotopy x smp) 0 = smp := by
    intro smp
    ext s
    exact triangleEdgeStraighteningHomotopy_zero x smp s
  exact (straightenedTwoCycle_class _ _ (triangleEdgeStraighteningHomotopy_face x) h₀
    (vertexNormalizedTwoCycle x c)).trans (vertexNormalizedTwoCycle_class x c)

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
