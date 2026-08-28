import Wikipedia.HopfProblem.PeriodTorusCohomologyCupFormal
import Wikipedia.HopfProblem.PeriodTorusCohomologyCupFormalNormalized

/-!
# The distinguished cup square on the positive period product

This is an evaluation on the literal existing formal prism chain. The
singular-cochain realization and complex-orientation comparison are
separate from this finite integral calculation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomologyCup

open SingularMayerVietoris PeriodTorusHigherHomology

private theorem cons_three_two {V : Type*} (a : V) (v : Fin 2 → V) :
    Fin.cons (α := fun _ => V) a v (2 : Fin 3) = v 1 := rfl

private theorem cons_four_two {V : Type*} (a : V) (v : Fin 3 → V) :
    Fin.cons (α := fun _ => V) a v (2 : Fin 4) = v 1 := rfl

private theorem cons_four_three {V : Type*} (a : V) (v : Fin 3 → V) :
    Fin.cons (α := fun _ => V) a v (3 : Fin 4) = v 2 := rfl

private theorem cons_five_two {V : Type*} (a : V) (v : Fin 4 → V) :
    Fin.cons (α := fun _ => V) a v (2 : Fin 5) = v 1 := rfl

private theorem cons_five_three {V : Type*} (a : V) (v : Fin 4 → V) :
    Fin.cons (α := fun _ => V) a v (3 : Fin 5) = v 2 := rfl

private theorem cons_five_four {V : Type*} (a : V) (v : Fin 4 → V) :
    Fin.cons (α := fun _ => V) a v (4 : Fin 5) = v 3 := rfl

private theorem vecCons_three_two {V : Type*} (a : V) (v : Fin 2 → V) :
    Matrix.vecCons a v (2 : Fin 3) = v 1 := rfl

private theorem vecCons_four_two {V : Type*} (a : V) (v : Fin 3 → V) :
    Matrix.vecCons a v (2 : Fin 4) = v 1 := rfl

private theorem vecCons_four_three {V : Type*} (a : V) (v : Fin 3 → V) :
    Matrix.vecCons a v (3 : Fin 4) = v 2 := rfl

private theorem vecCons_five_two {V : Type*} (a : V) (v : Fin 4 → V) :
    Matrix.vecCons a v (2 : Fin 5) = v 1 := rfl

private theorem vecCons_five_three {V : Type*} (a : V) (v : Fin 4 → V) :
    Matrix.vecCons a v (3 : Fin 5) = v 2 := rfl

private theorem vecCons_five_four {V : Type*} (a : V) (v : Fin 4 → V) :
    Matrix.vecCons a v (4 : Fin 5) = v 3 := rfl

private theorem fin_four_succ_two : (2 : Fin 3).succ = (3 : Fin 4) := rfl

theorem etaSquareSimplex_isNormalized : IsNormalizedFormalCochain etaSquareSimplex := by
  intro v i hi
  fin_cases i
  · change v 0 = v 1 at hi
    simp [etaSquareSimplex, etaTriangle, ← hi]
  · change v 1 = v 2 at hi
    simp [etaSquareSimplex, etaTriangle, ← hi]
  · change v 2 = v 3 at hi
    simp [etaSquareSimplex, etaTriangle, ← hi]
  · change v 3 = v 4 at hi
    simp [etaSquareSimplex, etaTriangle, ← hi]

/-- Contraction of the square with the first positive period direction. -/
def gammaContractedSimplex (v : Fin 4 → Lattice) : ℤ :=
  6 * ((v 1 3 - v 0 3) * etaTriangle ![v 1, v 2, v 3] +
    etaTriangle ![v 0, v 1, v 2] * (v 3 3 - v 2 3))

def gammaContractedEvaluation : FormalChains Lattice 4 →ₗ[ℤ] ℤ :=
  formalLift gammaContractedSimplex

theorem gammaContractedSimplex_isNormalized :
    IsNormalizedFormalCochain gammaContractedSimplex := by
  intro v i hi
  fin_cases i
  · change v 0 = v 1 at hi
    simp [gammaContractedSimplex, etaTriangle, ← hi]
  · change v 1 = v 2 at hi
    simp [gammaContractedSimplex, etaTriangle, ← hi]
  · change v 2 = v 3 at hi
    simp [gammaContractedSimplex, etaTriangle, ← hi]

/-- The second contraction is the explicit alternating w-delta cochain. -/
def gammaUContractedSimplex (v : Fin 3 → Lattice) : ℤ :=
  6 * ((v 1 2 - v 0 2) * (v 2 3 - v 1 3) -
    (v 1 3 - v 0 3) * (v 2 2 - v 1 2))

def gammaUContractedEvaluation : FormalChains Lattice 3 →ₗ[ℤ] ℤ :=
  formalLift gammaUContractedSimplex

theorem gamma_contraction_simplex (v : Fin 4 → Lattice) :
    formalEtaSquareEvaluation
      (formalPeriodProduct 3 (formalPeriodEdge (Pi.single 0 1)) (formalSimplex v)) =
        gammaContractedSimplex v := by
  change formalLift etaSquareSimplex _ = _
  rw [formalPeriodProduct_normalized_evaluation 3 _ _ _ etaSquareSimplex_isNormalized]
  norm_num [normalizedPeriodPrism, gammaContractedSimplex, etaSquareSimplex,
    etaTriangle, Function.comp_def, Fin.tail, cons_three_two, cons_four_two,
    cons_four_three, cons_five_two, cons_five_three, cons_five_four,
    vecCons_three_two, vecCons_four_two, vecCons_four_three,
    vecCons_five_two, vecCons_five_three, vecCons_five_four, fin_four_succ_two,
    Pi.single_apply, Fin.ext_iff]
  ring

theorem gamma_contraction (c : FormalChains Lattice 4) :
    formalEtaSquareEvaluation
      (formalPeriodProduct 3 (formalPeriodEdge (Pi.single 0 1)) c) =
        gammaContractedEvaluation c := by
  have h : formalEtaSquareEvaluation.comp
      (formalPeriodProduct 3 (formalPeriodEdge (Pi.single 0 1))) =
        gammaContractedEvaluation := by
    apply formalChains_ext
    intro v
    simpa only [LinearMap.comp_apply, gammaContractedEvaluation, formalLift_simplex] using
      gamma_contraction_simplex v
  exact LinearMap.congr_fun h c

theorem gamma_u_contraction_simplex (v : Fin 3 → Lattice) :
    gammaContractedEvaluation
      (formalPeriodProduct 2 (formalPeriodEdge (Pi.single 1 1)) (formalSimplex v)) =
        gammaUContractedSimplex v := by
  change formalLift gammaContractedSimplex _ = _
  rw [formalPeriodProduct_normalized_evaluation 2 _ _ _ gammaContractedSimplex_isNormalized]
  norm_num [normalizedPeriodPrism, gammaContractedSimplex, gammaUContractedSimplex,
    etaTriangle, Function.comp_def, Fin.tail, cons_three_two, cons_four_two, cons_four_three,
    vecCons_three_two, vecCons_four_two, vecCons_four_three, Pi.single_apply, Fin.ext_iff]
  ring

theorem gamma_u_contraction (c : FormalChains Lattice 3) :
    gammaContractedEvaluation
      (formalPeriodProduct 2 (formalPeriodEdge (Pi.single 1 1)) c) =
        gammaUContractedEvaluation c := by
  have h : gammaContractedEvaluation.comp
      (formalPeriodProduct 2 (formalPeriodEdge (Pi.single 1 1))) =
        gammaUContractedEvaluation := by
    apply formalChains_ext
    intro v
    simpa only [LinearMap.comp_apply, gammaUContractedEvaluation, formalLift_simplex] using
      gamma_u_contraction_simplex v
  exact LinearMap.congr_fun h c

theorem gamma_u_contraction_periodEdges (x y : Lattice) :
    gammaUContractedEvaluation
      (formalPeriodProduct 1 (formalPeriodEdge x) (formalPeriodEdge y)) =
        12 * (x 2 * y 3 - x 3 * y 2) := by
  simp only [formalPeriodProduct_apply, formalPeriodEdge,
    formalEdgeCrossProduct_simplex_succ, formalBoundary_simplex]
  simp [gammaUContractedEvaluation, gammaUContractedSimplex,
    Function.comp_def, cons_three_two]
  ring

/-- The Alexander--Whitney square has value twelve on the positive
ordered fourfold period product. -/
theorem formalEtaSquareEvaluation_positiveTop :
    formalEtaSquareEvaluation formalPositiveTop = 12 := by
  rw [formalPositiveTop, gamma_contraction, gamma_u_contraction,
    gamma_u_contraction_periodEdges]
  norm_num [Pi.single_apply, Fin.ext_iff]

end Wikipedia.HopfProblem.PeriodTorusCohomologyCup
