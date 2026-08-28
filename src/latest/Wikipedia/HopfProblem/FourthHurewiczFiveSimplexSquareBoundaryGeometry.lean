import Wikipedia.HopfProblem.FourthHurewiczCubeSubdivisionNativeBasic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The two edge routes across a square

The routes run from the lower-left to the upper-right vertex.  Their
coordinatewise affine interpolation fixes both endpoints throughout.
-/

noncomputable section

open scoped Topology unitInterval

namespace Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary

open NativeSubdivision

/-- The route along the bottom and then the right edge. -/
def squareLowerRoute : C(Fin 1 → I, Fin 2 → I) where
  toFun u := ![Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ)),
    Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1)]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp
    · exact continuous_projIcc.comp (by fun_prop)
    · exact continuous_projIcc.comp (by fun_prop)

/-- The route along the left and then the top edge. -/
def squareUpperRoute : C(Fin 1 → I, Fin 2 → I) where
  toFun u := ![Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1),
    Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ))]
  continuous_toFun := by
    apply continuous_pi
    intro i
    fin_cases i <;> dsimp
    · exact continuous_projIcc.comp (by fun_prop)
    · exact continuous_projIcc.comp (by fun_prop)

@[simp] theorem squareLowerRoute_zero (u : Fin 1 → I) (hu : u 0 = 0) :
    squareLowerRoute u = fun _ => 0 := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> norm_num [squareLowerRoute, hu, Set.projIcc]

@[simp] theorem squareLowerRoute_one (u : Fin 1 → I) (hu : u 0 = 1) :
    squareLowerRoute u = fun _ => 1 := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> norm_num [squareLowerRoute, hu, Set.projIcc]

@[simp] theorem squareUpperRoute_zero (u : Fin 1 → I) (hu : u 0 = 0) :
    squareUpperRoute u = fun _ => 0 := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> norm_num [squareUpperRoute, hu, Set.projIcc]

@[simp] theorem squareUpperRoute_one (u : Fin 1 → I) (hu : u 0 = 1) :
    squareUpperRoute u = fun _ => 1 := by
  funext i
  fin_cases i <;> apply Subtype.ext <;> norm_num [squareUpperRoute, hu, Set.projIcc]

theorem squareLowerRoute_of_le (u : Fin 1 → I) (hu : (u 0 : ℝ) ≤ 1 / 2) :
    squareLowerRoute u = ![Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ)), 0] := by
  funext i
  fin_cases i
  · rfl
  · exact Set.projIcc_of_le_left zero_le_one (by linarith)

theorem squareLowerRoute_of_not_le (u : Fin 1 → I) (hu : ¬(u 0 : ℝ) ≤ 1 / 2) :
    squareLowerRoute u = ![1, Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1)] := by
  funext i
  fin_cases i
  · exact Set.projIcc_of_right_le zero_le_one (by linarith)
  · rfl

theorem squareUpperRoute_of_le (u : Fin 1 → I) (hu : (u 0 : ℝ) ≤ 1 / 2) :
    squareUpperRoute u = ![0, Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ))] := by
  funext i
  fin_cases i
  · exact Set.projIcc_of_le_left zero_le_one (by linarith)
  · rfl

theorem squareUpperRoute_of_not_le (u : Fin 1 → I) (hu : ¬(u 0 : ℝ) ≤ 1 / 2) :
    squareUpperRoute u = ![Set.projIcc 0 1 zero_le_one (2 * (u 0 : ℝ) - 1), 1] := by
  funext i
  fin_cases i
  · rfl
  · exact Set.projIcc_of_right_le zero_le_one (by linarith)

/-- Affine interpolation of the two genuine edge routes. -/
def squareRoutesBlend : C(I × (Fin 1 → I), Fin 2 → I) where
  toFun u := nativeCubeBlend u.1 (squareLowerRoute u.2) (squareUpperRoute u.2)
  continuous_toFun := by
    apply continuous_pi
    intro i
    exact Set.Icc.continuous_convexComb_prod.comp
      (((continuous_apply i).comp (squareLowerRoute.continuous.comp continuous_snd)).prodMk
        (((continuous_apply i).comp (squareUpperRoute.continuous.comp continuous_snd)).prodMk
          continuous_fst))

@[simp] theorem squareRoutesBlend_zero (u : Fin 1 → I) :
    squareRoutesBlend (0, u) = squareLowerRoute u := nativeCubeBlend_zero _ _

@[simp] theorem squareRoutesBlend_one (u : Fin 1 → I) :
    squareRoutesBlend (1, u) = squareUpperRoute u := nativeCubeBlend_one _ _

theorem squareRoutesBlend_endpoint_zero (t : I) (u : Fin 1 → I) (hu : u 0 = 0) :
    squareRoutesBlend (t, u) = fun _ => 0 := by
  funext i
  simp [squareRoutesBlend, nativeCubeBlend, squareLowerRoute_zero u hu,
    squareUpperRoute_zero u hu]

theorem squareRoutesBlend_endpoint_one (t : I) (u : Fin 1 → I) (hu : u 0 = 1) :
    squareRoutesBlend (t, u) = fun _ => 1 := by
  funext i
  simp [squareRoutesBlend, nativeCubeBlend, squareLowerRoute_one u hu,
    squareUpperRoute_one u hu]

end Wikipedia.HopfProblem.HigherHurewicz.CubicalBoundary
