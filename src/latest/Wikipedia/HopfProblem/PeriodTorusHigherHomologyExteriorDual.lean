import Wikipedia.HopfProblem.Lattice
import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.Dual

/-!
# The actual exterior-dual pairing

The determinant pairing identifies the exterior power of the integral dual
with the dual of the exterior power. Its naturality specifies the ordinary
transpose convention for pullback, without any homology identification.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomologyExterior

open Module

/-- The canonical exterior-dual pairing, as an isomorphism of the two actual modules. -/
def dualPairingEquiv (n : ℕ) :
    (⋀[ℤ]^n (Module.Dual ℤ Lattice)) ≃ₗ[ℤ] Module.Dual ℤ (⋀[ℤ]^n Lattice) :=
  ((Pi.basisFun ℤ (Fin 4)).dualBasis.exteriorPower n).equiv
    ((Pi.basisFun ℤ (Fin 4)).exteriorPower n).dualBasis (Equiv.refl _)

@[simp] theorem dualPairingEquiv_basis (n : ℕ) (s : Set.powersetCard (Fin 4) n) :
    dualPairingEquiv n (((Pi.basisFun ℤ (Fin 4)).dualBasis.exteriorPower n) s) =
      ((Pi.basisFun ℤ (Fin 4)).exteriorPower n).dualBasis s := by
  simp only [dualPairingEquiv, Module.Basis.equiv_apply, Equiv.refl_apply]

theorem dualPairingEquiv_toLinearMap (n : ℕ) :
    (dualPairingEquiv n).toLinearMap = exteriorPower.pairingDual ℤ Lattice n := by
  apply ((Pi.basisFun ℤ (Fin 4)).dualBasis.exteriorPower n).ext
  intro s
  change dualPairingEquiv n (((Pi.basisFun ℤ (Fin 4)).dualBasis.exteriorPower n) s) = _
  rw [dualPairingEquiv_basis]
  rw [show ((Pi.basisFun ℤ (Fin 4)).exteriorPower n).dualBasis s =
      ((Pi.basisFun ℤ (Fin 4)).exteriorPower n).coord s from
    congrFun ((Pi.basisFun ℤ (Fin 4)).exteriorPower n).coe_dualBasis s]
  rw [exteriorPower.basis_coord]
  simp only [exteriorPower.ιMultiDual, exteriorPower.basis_apply, Module.Basis.coe_dualBasis]

@[simp] theorem dualPairingEquiv_apply (n : ℕ) (x : ⋀[ℤ]^n (Module.Dual ℤ Lattice)) :
    dualPairingEquiv n x = exteriorPower.pairingDual ℤ Lattice n x :=
  LinearMap.congr_fun (dualPairingEquiv_toLinearMap n) x

@[simp] theorem dualPairingEquiv_ιMulti_ιMulti (n : ℕ)
    (ξ : Fin n → Module.Dual ℤ Lattice) (v : Fin n → Lattice) :
    dualPairingEquiv n (exteriorPower.ιMulti ℤ n ξ) (exteriorPower.ιMulti ℤ n v) =
      Matrix.det (Matrix.of (fun i j => ξ j (v i))) := by
  rw [dualPairingEquiv_apply, exteriorPower.pairingDual_ιMulti_ιMulti]

/-- The canonical pairing is natural for the actual exterior-power map and dual map. -/
theorem pairingDual_naturality (n : ℕ) (f : Lattice →ₗ[ℤ] Lattice) :
    (exteriorPower.pairingDual ℤ Lattice n).comp (exteriorPower.map n f.dualMap) =
      (exteriorPower.map n f).dualMap.comp (exteriorPower.pairingDual ℤ Lattice n) := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro ξ
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  simp only [LinearMap.compAlternatingMap_apply, LinearMap.comp_apply,
    exteriorPower.map_apply_ιMulti, LinearMap.dualMap_apply,
    exteriorPower.pairingDual_ιMulti_ιMulti, Function.comp_apply]

theorem dualPairingEquiv_naturality (n : ℕ) (f : Lattice →ₗ[ℤ] Lattice) :
    (dualPairingEquiv n).toLinearMap.comp (exteriorPower.map n f.dualMap) =
      (exteriorPower.map n f).dualMap.comp (dualPairingEquiv n).toLinearMap := by
  rw [dualPairingEquiv_toLinearMap]
  exact pairingDual_naturality n f

/-- Matrix coordinates for the ordinary dual map are the transpose, not inverse transpose. -/
theorem dualMap_toMatrix (f : Lattice →ₗ[ℤ] Lattice) :
  LinearMap.toMatrix (Pi.basisFun ℤ (Fin 4)).dualBasis (Pi.basisFun ℤ (Fin 4)).dualBasis
      f.dualMap =
    (LinearMap.toMatrix (Pi.basisFun ℤ (Fin 4)) (Pi.basisFun ℤ (Fin 4)) f).transpose := by
  rw [LinearMap.dualMap_def, LinearMap.toMatrix_transpose]


end Wikipedia.HopfProblem.PeriodTorusHigherHomologyExterior
