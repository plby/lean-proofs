import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FinCases

/-!
# The source's literal complex-linear coefficient complex

This file contains only the displayed linear algebra. Its identification
with actual global sections is proved separately from the actual sheaf
maps; it is not a definition of sheaf cohomology.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections

/-- The same source-signed scalar at each of the two actual endpoint coordinates. -/
def coefficientDifferential : (Fin 3 → ℂ) →ₗ[ℂ] (Fin 2 → ℂ) where
  toFun a := fun _ => a 0 - a 1 + a 2
  map_add' a b := by
    funext t
    simp only [Pi.add_apply]
    abel
  map_smul' c a := by
    funext t
    simp only [Pi.smul_apply, smul_add, smul_sub, RingHom.id_apply]

@[simp] theorem coefficientDifferential_apply (a : Fin 3 → ℂ) (t : Fin 2) :
    coefficientDifferential a t = a 0 - a 1 + a 2 := rfl

/-- The literal source complex ℂ →₀ ℂ³ → ℂ², with complex-linear arrows. -/
abbrev coefficientComplex : ShortComplex (ModuleCat ℂ) :=
  ShortComplex.mk (0 : ModuleCat.of ℂ ℂ ⟶ ModuleCat.of ℂ (Fin 3 → ℂ))
    (ModuleCat.ofHom coefficientDifferential) zero_comp

/-- The literal source matrix has two identical rows (1, -1, 1). -/
theorem coefficientDifferential_vector (a b c : ℂ) :
    coefficientDifferential ![a, b, c] = ![a - b + c, a - b + c] := by
  ext t
  fin_cases t <;> rfl

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyGlobalSections
