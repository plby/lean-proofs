import Wikipedia.HopfProblem.SingularCohomologyCupClasses
import Wikipedia.HopfProblem.PeriodTorusCohomologyCupOneEdges
import Wikipedia.HopfProblem.PeriodTorusCohomologyCupOneRealization

/-!
# An actual Alexander--Whitney cocycle for the distinguished period form

The two-cochain is the cup of the first pair of indicated coordinate
one-cocycles plus six times the second pair.  Its value on every native
integer-affine simplex is proved from the genuine edge evaluations.
The corresponding square therefore evaluates by the exact formal
front/back function, before any finite numerical calculation is used.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomologyCup

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open PeriodTorusHigherHomology SingularCohomologyCup

attribute [local instance] integerLinearMapModule integerTensorModule

/-- The actual two-cochain whose alternating periods are the distinguished source form. -/
def coordinateEtaCochain : Cochain (ProductTorus 4) 2 :=
  cup (coordinateOneCochain 4 1) (coordinateOneCochain 4 2) +
    (6 : ℤ) • cup (coordinateOneCochain 4 0) (coordinateOneCochain 4 3)

/-- Closedness follows from the native Alexander--Whitney Leibniz identity. -/
theorem coordinateEtaCochain_closed : coboundary coordinateEtaCochain = 0 := by
  rw [coordinateEtaCochain, coboundary_add, coboundary_smul,
    cup_cocycle _ _ (coordinateOneCochain_coboundary 4 1)
      (coordinateOneCochain_coboundary 4 2),
    cup_cocycle _ _ (coordinateOneCochain_coboundary 4 0)
      (coordinateOneCochain_coboundary 4 3), smul_zero, zero_add]

/-- The genuine cocycle representative in the actual singular cochain complex. -/
def coordinateEtaCocycle : Cocycle (singularCochainComplex (ProductTorus 4)) 2 :=
  mkCocycle _ 2 coordinateEtaCochain coordinateEtaCochain_closed

@[simp] theorem coordinateEtaCocycle_val : coordinateEtaCocycle.val = coordinateEtaCochain := rfl

/-- Its class lies in the native singular cohomology object. -/
def coordinateEtaClass : SingularCohomology (ProductTorus 4) 2 :=
  cocycleClass _ 2 coordinateEtaCocycle

/-- The native two-cochain has precisely the specified adjacent-edge formula. -/
theorem coordinateEtaCochain_affineSimplex (v : Fin 3 → Lattice) :
    coordinateEtaCochain (simplexChain (ProductTorus 4) 2 (affineTorusSimplex v)) =
      etaTriangle v := by
  rw [coordinateEtaCochain, LinearMap.add_apply, LinearMap.smul_apply,
    coordinateOneCup_affineSimplex, coordinateOneCup_affineSimplex]
  simp only [etaTriangle, smul_eq_mul]
  ring

/-- The native cup square has exactly the formal front/back value on each actual simplex. -/
theorem coordinateEtaSquare_affineSimplex (v : Fin 5 → Lattice) :
    cup coordinateEtaCochain coordinateEtaCochain
      (simplexChain (ProductTorus 4) 4 (affineTorusSimplex v)) = etaSquareSimplex v := by
  rw [cup_simplex]
  simp only [frontFace, backFace, windowFace, affineTorusSimplex_vertexMap,
    coordinateEtaCochain_affineSimplex]
  rfl

/-- The actual two-cochain evaluates every realized chain by its literal formal functional. -/
theorem coordinateEtaCochain_affineChain (c : FormalChains Lattice 3) :
    coordinateEtaCochain (affineTorusChain 4 2 c) = formalEtaEvaluation c := by
  have h : coordinateEtaCochain.comp (affineTorusChain 4 2) = formalEtaEvaluation := by
    apply formalChains_ext
    intro v
    change coordinateEtaCochain (affineTorusChain 4 2 (formalSimplex v)) = _
    rw [affineTorusChain_simplex, coordinateEtaCochain_affineSimplex,
      formalEtaEvaluation_simplex]
  exact LinearMap.congr_fun h c

/-- The native cup square evaluates every realized formal chain by the actual formal square. -/
theorem coordinateEtaSquare_affineChain (c : FormalChains Lattice 5) :
    cup coordinateEtaCochain coordinateEtaCochain (affineTorusChain 4 4 c) =
      formalEtaSquareEvaluation c := by
  have h : (cup coordinateEtaCochain coordinateEtaCochain).comp
      (affineTorusChain 4 4) = formalEtaSquareEvaluation := by
    apply formalChains_ext
    intro v
    change cup coordinateEtaCochain coordinateEtaCochain
      (affineTorusChain 4 4 (formalSimplex v)) = _
    rw [affineTorusChain_simplex, coordinateEtaSquare_affineSimplex,
      formalEtaSquareEvaluation_simplex]
  exact LinearMap.congr_fun h c

end Wikipedia.HopfProblem.PeriodTorusCohomologyCup
