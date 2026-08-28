import Wikipedia.HopfProblem.SecondHurewiczSimplyConnectedInverseChains

/-!
# Descent of the actual degree-two inverse to singular homology

The normalized-triangle assignment annihilates every genuine boundary,
so it descends to the original categorical integral singular homology.
The explicit prism identities and zero coefficient sum of two-cycles
give the right-inverse identity for the original native Hurewicz map.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]

/-- The genuine linear inverse candidate, obtained by descent of the
constructed normalized-triangle assignment rather than by assuming an isomorphism. -/
def hurewiczInverse (x : X) : SingularHomology X 2 →ₗ[ℤ] Additive (π_ 2 X x) :=
  secondHomologyDesc (triangleClassOperator x) (triangleClassOperator_boundary x)

@[simp] theorem hurewiczInverse_cycleClass (x : X)
    (c : ModuleHomology.Cycle (singularComplex X) 2) :
    hurewiczInverse x (ModuleHomology.cycleClass (singularComplex X) 2 c) =
      triangleClassOperator x c.val :=
  secondHomologyDesc_cycleClass _ _ c

/-- The genuine Hurewicz map composed with the constructed descent is the identity. -/
theorem hurewiczMap_comp_hurewiczInverse (x : X) :
    (hurewiczMap x).comp (hurewiczInverse x) = LinearMap.id :=
  comp_secondHomologyDesc_eq_id (triangleClassOperator x) (triangleClassOperator_boundary x)
    (hurewiczMap x) (hurewiczMap_triangleClassOperator_twoCycle x)

@[simp] theorem hurewiczMap_hurewiczInverse (x : X) (c : SingularHomology X 2) :
    hurewiczMap x (hurewiczInverse x c) = c :=
  LinearMap.congr_fun (hurewiczMap_comp_hurewiczInverse x) c

/-- Surjectivity already follows from the explicit normalization construction. -/
theorem hurewiczMap_surjective (x : X) : Function.Surjective (hurewiczMap x) :=
  fun c => ⟨hurewiczInverse x c, hurewiczMap_hurewiczInverse x c⟩

end Wikipedia.HopfProblem.SecondHurewicz.SimplyConnected
