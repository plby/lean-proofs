import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Tactic.FinCases

/-!
# Exterior-square factorization of an actual alternating bilinear map

This uses Mathlib's original exterior power and its proved universal
property. The generator formula retains the original bilinear pairing.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SheafCupProduct

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]

/-- A given bilinear map with its two original inputs indexed by `Fin 2`. -/
def multilinearPairing (p : M →ₗ[R] M →ₗ[R] N) :
    MultilinearMap R (fun _ : Fin 2 => M) N where
  toFun v := p (v 0) (v 1)
  map_update_add' {hDecEq} v i x y := by
    have heq : hDecEq = instDecidableEqFin 2 := Subsingleton.elim _ _
    subst hDecEq
    fin_cases i <;> simp
  map_update_smul' {hDecEq} v i r x := by
    have heq : hDecEq = instDecidableEqFin 2 := Subsingleton.elim _ _
    subst hDecEq
    fin_cases i <;> simp

/-- A zero diagonal makes this actual bilinear map an alternating map. -/
def alternatingPairing (p : M →ₗ[R] M →ₗ[R] N) (hp : ∀ a, p a a = 0) :
    AlternatingMap R M N (Fin 2) where
  toMultilinearMap := multilinearPairing p
  map_eq_zero_of_eq' v i j hij hne := by
    have hv : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;> simp_all
    change p (v 0) (v 1) = 0
    rw [hv]
    exact hp _

@[simp] theorem alternatingPairing_apply (p : M →ₗ[R] M →ₗ[R] N)
    (hp : ∀ a, p a a = 0) (v : Fin 2 → M) :
    alternatingPairing p hp v = p (v 0) (v 1) := rfl

/-- The original alternating bilinear map factors through the genuine exterior square. -/
def exteriorPairing (p : M →ₗ[R] M →ₗ[R] N) (hp : ∀ a, p a a = 0) :
    ⋀[R]^2 M →ₗ[R] N :=
  exteriorPower.alternatingMapLinearEquiv (alternatingPairing p hp)

@[simp] theorem exteriorPairing_ιMulti (p : M →ₗ[R] M →ₗ[R] N)
    (hp : ∀ a, p a a = 0) (v : Fin 2 → M) :
    exteriorPairing p hp (exteriorPower.ιMulti R 2 v) = p (v 0) (v 1) :=
  exteriorPower.alternatingMapLinearEquiv_apply_ιMulti (alternatingPairing p hp) v

variable {M' N' : Type*} [AddCommGroup M'] [Module R M']
  [AddCommGroup N'] [Module R N']

/-- Original maps preserving the pairing also preserve its exterior-square factor. -/
theorem exteriorPairing_naturality
    (p : M →ₗ[R] M →ₗ[R] N) (hp : ∀ a, p a a = 0)
    (q : M' →ₗ[R] M' →ₗ[R] N') (hq : ∀ a, q a a = 0)
    (f : M →ₗ[R] M') (g : N →ₗ[R] N')
    (h : ∀ a b, g (p a b) = q (f a) (f b)) :
    g.comp (exteriorPairing p hp) =
      (exteriorPairing q hq).comp (exteriorPower.map 2 f) := by
  apply exteriorPower.linearMap_ext
  ext v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPairing_ιMulti, exteriorPower.map_apply_ιMulti, Function.comp_apply]
  exact h (v 0) (v 1)

end Wikipedia.HopfProblem.SheafCupProduct
