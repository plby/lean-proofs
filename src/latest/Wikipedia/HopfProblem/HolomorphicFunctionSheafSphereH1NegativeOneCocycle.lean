import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1Cech

/-!
# Mapping actual additive sheaf cocycles

This literal map on cocycles will be applied to the inclusion of the
ideal sheaf of functions vanishing at infinity into the holomorphic
function sheaf. Compatibility follows from the actual naturality of
the sheaf morphism with restriction.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F G : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X}

/-- Apply a morphism of actual additive sheaves to an actual one-cocycle. -/
def CechOneCocycle.map (φ : F ⟶ G) (c : CechOneCocycle F U) : CechOneCocycle G U where
  value i j := φ.hom.app (op (U i ⊓ U j)) (c.value i j)
  condition i j k := by
    rw [res_map, res_map, res_map, ← map_add, c.condition]

@[simp] theorem CechOneCocycle.map_value (φ : F ⟶ G) (c : CechOneCocycle F U)
    (i j : ι) :
    (c.map φ).value i j = φ.hom.app (op (U i ⊓ U j)) (c.value i j) := rfl

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
