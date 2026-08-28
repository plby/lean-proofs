import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Algebra.Module.Torsion.Free
import Mathlib.Tactic.FinCases
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductBilinear

/-!
# Alternating maps from integral bilinear and trilinear operations

The operations are supplied as genuine curried linear maps. The alternating
laws are proved from explicit repeated-argument identities, or, in degree two,
from skew symmetry and torsion freeness of the target. The resulting maps lift
through the actual universal property of the exterior power.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryagin

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule

variable {M N P Q : Type*}
  [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
  [AddCommGroup P] [Module ℤ P] [AddCommGroup Q] [Module ℤ Q]

/-- A curried bilinear map, with its two arguments indexed by `Fin 2`. -/
def multilinearOfBilinear (β : M →ₗ[ℤ] M →ₗ[ℤ] N) :
    MultilinearMap ℤ (fun _ : Fin 2 => M) N where
  toFun v := β (v 0) (v 1)
  map_update_add' {hDecEq} v i x y := by
    have heq : hDecEq = instDecidableEqFin 2 := Subsingleton.elim _ _
    subst hDecEq
    fin_cases i <;> simp
  map_update_smul' {hDecEq} v i r x := by
    have heq : hDecEq = instDecidableEqFin 2 := Subsingleton.elim _ _
    subst hDecEq
    fin_cases i <;> simp

@[simp] theorem multilinearOfBilinear_apply (β : M →ₗ[ℤ] M →ₗ[ℤ] N)
    (v : Fin 2 → M) : multilinearOfBilinear β v = β (v 0) (v 1) := rfl

/-- A bilinear map with zero diagonal is genuinely alternating. -/
def alternatingOfBilinear (β : M →ₗ[ℤ] M →ₗ[ℤ] N)
    (hdiag : ∀ x : M, β x x = 0) : AlternatingMap ℤ M N (Fin 2) where
  toMultilinearMap := multilinearOfBilinear β
  map_eq_zero_of_eq' v i j hij hne := by
    have h : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;> simp_all
    change β (v 0) (v 1) = 0
    rw [h]
    exact hdiag _

@[simp] theorem alternatingOfBilinear_apply (β : M →ₗ[ℤ] M →ₗ[ℤ] N)
    (hdiag : ∀ x : M, β x x = 0) (v : Fin 2 → M) :
    alternatingOfBilinear β hdiag v = β (v 0) (v 1) := rfl

/-- Skew symmetry kills the diagonal over a torsion-free integral target. -/
theorem skewBilinear_diagonal_zero [Module.IsTorsionFree ℤ N]
    (β : M →ₗ[ℤ] M →ₗ[ℤ] N) (hskew : ∀ x y : M, β x y = -β y x) (x : M) :
    β x x = 0 := by
  apply (smul_eq_zero_iff_right (show (2 : ℤ) ≠ 0 by decide)).mp
  rw [two_smul ℤ]
  exact add_eq_zero_iff_eq_neg.mpr (hskew x x)

/-- The alternating map furnished by a skew bilinear map into a torsion-free target. -/
def alternatingOfSkewBilinear [Module.IsTorsionFree ℤ N]
    (β : M →ₗ[ℤ] M →ₗ[ℤ] N) (hskew : ∀ x y : M, β x y = -β y x) :
    AlternatingMap ℤ M N (Fin 2) :=
  alternatingOfBilinear β (skewBilinear_diagonal_zero β hskew)

@[simp] theorem alternatingOfSkewBilinear_apply [Module.IsTorsionFree ℤ N]
    (β : M →ₗ[ℤ] M →ₗ[ℤ] N) (hskew : ∀ x y : M, β x y = -β y x)
    (v : Fin 2 → M) : alternatingOfSkewBilinear β hskew v = β (v 0) (v 1) := rfl

/-- A curried trilinear map, with its three arguments indexed by `Fin 3`. -/
def multilinearOfTrilinear (g : M →ₗ[ℤ] M →ₗ[ℤ] M →ₗ[ℤ] N) :
    MultilinearMap ℤ (fun _ : Fin 3 => M) N where
  toFun v := g (v 0) (v 1) (v 2)
  map_update_add' {hDecEq} v i x y := by
    have heq : hDecEq = instDecidableEqFin 3 := Subsingleton.elim _ _
    subst hDecEq
    fin_cases i <;> simp
  map_update_smul' {hDecEq} v i r x := by
    have heq : hDecEq = instDecidableEqFin 3 := Subsingleton.elim _ _
    subst hDecEq
    fin_cases i <;> simp

@[simp] theorem multilinearOfTrilinear_apply (g : M →ₗ[ℤ] M →ₗ[ℤ] M →ₗ[ℤ] N)
    (v : Fin 3 → M) : multilinearOfTrilinear g v = g (v 0) (v 1) (v 2) := rfl

/-- The three possible repeated-argument identities give an alternating trilinear map. -/
def alternatingOfTrilinear (g : M →ₗ[ℤ] M →ₗ[ℤ] M →ₗ[ℤ] N)
    (h01 : ∀ x z : M, g x x z = 0)
    (h02 : ∀ x y : M, g x y x = 0)
    (h12 : ∀ x y : M, g x y y = 0) : AlternatingMap ℤ M N (Fin 3) where
  toMultilinearMap := multilinearOfTrilinear g
  map_eq_zero_of_eq' v i j hij hne := by
    have h : v 0 = v 1 ∨ v 0 = v 2 ∨ v 1 = v 2 := by
      fin_cases i <;> fin_cases j <;> simp_all
    change g (v 0) (v 1) (v 2) = 0
    rcases h with h | h | h
    · rw [h]
      exact h01 _ _
    · rw [h]
      exact h02 _ _
    · rw [h]
      exact h12 _ _

@[simp] theorem alternatingOfTrilinear_apply (g : M →ₗ[ℤ] M →ₗ[ℤ] M →ₗ[ℤ] N)
    (h01 : ∀ x z : M, g x x z = 0)
    (h02 : ∀ x y : M, g x y x = 0)
    (h12 : ∀ x y : M, g x y y = 0) (v : Fin 3 → M) :
    alternatingOfTrilinear g h01 h02 h12 v = g (v 0) (v 1) (v 2) := rfl

/-- Cyclic invariance and vanishing when the first two arguments agree suffice in degree three. -/
def alternatingOfCyclicTrilinear (g : M →ₗ[ℤ] M →ₗ[ℤ] M →ₗ[ℤ] N)
    (hcyclic : ∀ x y z : M, g x y z = g y z x)
    (h01 : ∀ x z : M, g x x z = 0) : AlternatingMap ℤ M N (Fin 3) :=
  alternatingOfTrilinear g h01
    (fun x y => (hcyclic x y x).trans ((hcyclic y x x).trans (h01 x y)))
    (fun x y => (hcyclic x y y).trans (h01 y x))

@[simp] theorem alternatingOfCyclicTrilinear_apply
    (g : M →ₗ[ℤ] M →ₗ[ℤ] M →ₗ[ℤ] N)
    (hcyclic : ∀ x y z : M, g x y z = g y z x)
    (h01 : ∀ x z : M, g x x z = 0) (v : Fin 3 → M) :
    alternatingOfCyclicTrilinear g hcyclic h01 v = g (v 0) (v 1) (v 2) := rfl

/-- The actual linear map out of the exterior square determined by a zero-diagonal bilinear map. -/
def bilinearExteriorLift (β : M →ₗ[ℤ] M →ₗ[ℤ] N)
    (hdiag : ∀ x : M, β x x = 0) : (⋀[ℤ]^2 M) →ₗ[ℤ] N :=
  exteriorPower.alternatingMapLinearEquiv (alternatingOfBilinear β hdiag)

@[simp] theorem bilinearExteriorLift_apply_ιMulti (β : M →ₗ[ℤ] M →ₗ[ℤ] N)
    (hdiag : ∀ x : M, β x x = 0) (v : Fin 2 → M) :
    bilinearExteriorLift β hdiag (exteriorPower.ιMulti ℤ 2 v) = β (v 0) (v 1) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

/-- The exterior-square lift obtained directly from skew symmetry and torsion freeness. -/
def skewBilinearExteriorLift [Module.IsTorsionFree ℤ N]
    (β : M →ₗ[ℤ] M →ₗ[ℤ] N) (hskew : ∀ x y : M, β x y = -β y x) :
    (⋀[ℤ]^2 M) →ₗ[ℤ] N :=
  exteriorPower.alternatingMapLinearEquiv (alternatingOfSkewBilinear β hskew)

@[simp] theorem skewBilinearExteriorLift_apply_ιMulti [Module.IsTorsionFree ℤ N]
    (β : M →ₗ[ℤ] M →ₗ[ℤ] N) (hskew : ∀ x y : M, β x y = -β y x)
    (v : Fin 2 → M) :
    skewBilinearExteriorLift β hskew (exteriorPower.ιMulti ℤ 2 v) = β (v 0) (v 1) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

/-- The actual linear map out of the exterior cube determined by the trilinear operation. -/
def trilinearExteriorLift (g : M →ₗ[ℤ] M →ₗ[ℤ] M →ₗ[ℤ] N)
    (h01 : ∀ x z : M, g x x z = 0)
    (h02 : ∀ x y : M, g x y x = 0)
    (h12 : ∀ x y : M, g x y y = 0) : (⋀[ℤ]^3 M) →ₗ[ℤ] N :=
  exteriorPower.alternatingMapLinearEquiv (alternatingOfTrilinear g h01 h02 h12)

@[simp] theorem trilinearExteriorLift_apply_ιMulti
    (g : M →ₗ[ℤ] M →ₗ[ℤ] M →ₗ[ℤ] N)
    (h01 : ∀ x z : M, g x x z = 0)
    (h02 : ∀ x y : M, g x y x = 0)
    (h12 : ∀ x y : M, g x y y = 0) (v : Fin 3 → M) :
    trilinearExteriorLift g h01 h02 h12 (exteriorPower.ιMulti ℤ 3 v) =
      g (v 0) (v 1) (v 2) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

/-- The exterior-cube lift under the shorter cyclic-invariance hypotheses. -/
def cyclicTrilinearExteriorLift (g : M →ₗ[ℤ] M →ₗ[ℤ] M →ₗ[ℤ] N)
    (hcyclic : ∀ x y z : M, g x y z = g y z x)
    (h01 : ∀ x z : M, g x x z = 0) : (⋀[ℤ]^3 M) →ₗ[ℤ] N :=
  exteriorPower.alternatingMapLinearEquiv (alternatingOfCyclicTrilinear g hcyclic h01)

@[simp] theorem cyclicTrilinearExteriorLift_apply_ιMulti
    (g : M →ₗ[ℤ] M →ₗ[ℤ] M →ₗ[ℤ] N)
    (hcyclic : ∀ x y z : M, g x y z = g y z x)
    (h01 : ∀ x z : M, g x x z = 0) (v : Fin 3 → M) :
    cyclicTrilinearExteriorLift g hcyclic h01 (exteriorPower.ιMulti ℤ 3 v) =
      g (v 0) (v 1) (v 2) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti _ _

/-- Naturality of exterior-power lifts, proved on the actual exterior-product generators. -/
theorem alternatingExteriorLift_naturality {n : ℕ}
    (α : AlternatingMap ℤ M N (Fin n)) (β : AlternatingMap ℤ P Q (Fin n))
    (f : M →ₗ[ℤ] P) (k : N →ₗ[ℤ] Q)
    (hnat : ∀ v : Fin n → M, k (α v) = β (f ∘ v)) :
    k.comp (exteriorPower.alternatingMapLinearEquiv α) =
      (exteriorPower.alternatingMapLinearEquiv β).comp (exteriorPower.map n f) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  exact hnat v

end Wikipedia.HopfProblem.PeriodTorusHigherHomologyPontryagin
