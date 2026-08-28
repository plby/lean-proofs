import Mathlib.LinearAlgebra.Dual.Defs
import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.GroupTheory.Index

/-!
# Actual cokernels under integer coordinate equivalences

A commuting square with invertible changes of domain and codomain
identifies the actual image submodules, their cokernels, and their
additive indices.  Applying this construction to precomposition on
integer duals gives the corresponding dual-map comparison.

No topological map or cohomological interpretation is assumed here.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology.CohomologyDualComparison

universe u v u' v'

variable {M : Type u} {N : Type v} {M' : Type u'} {N' : Type v'}
  [AddCommGroup M] [Module ℤ M] [AddCommGroup N] [Module ℤ N]
  [AddCommGroup M'] [Module ℤ M'] [AddCommGroup N'] [Module ℤ N']

/-- The codomain coordinate equivalence carries one actual image onto the other. -/
theorem range_map_eq_of_intertwining (L : M →ₗ[ℤ] N) (q : M' →ₗ[ℤ] N')
    (eM : M ≃ₗ[ℤ] M') (eN : N ≃ₗ[ℤ] N') (h : ∀ x, eN (L x) = q (eM x)) :
    (LinearMap.range L).map eN.toLinearMap = LinearMap.range q := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, rfl⟩, rfl⟩
    exact ⟨eM z, (h z).symm⟩
  · rintro ⟨z, rfl⟩
    refine ⟨L (eM.symm z), ⟨eM.symm z, rfl⟩, ?_⟩
    change eN (L (eM.symm z)) = q z
    rw [h, LinearEquiv.apply_symm_apply]

/-- The actual quotient of the codomain is transported by its coordinate equivalence. -/
def cokernelEquivOfIntertwining (L : M →ₗ[ℤ] N) (q : M' →ₗ[ℤ] N')
    (eM : M ≃ₗ[ℤ] M') (eN : N ≃ₗ[ℤ] N') (h : ∀ x, eN (L x) = q (eM x)) :
    (N ⧸ LinearMap.range L) ≃ₗ[ℤ] (N' ⧸ LinearMap.range q) := by
  letI := Submodule.Quotient.module (LinearMap.range L)
  letI := Submodule.Quotient.module (LinearMap.range q)
  exact (Submodule.Quotient.equiv _ _ eN
    (range_map_eq_of_intertwining L q eM eN h)).toAddEquiv.toIntLinearEquiv

@[simp] theorem cokernelEquivOfIntertwining_apply_mk
    (L : M →ₗ[ℤ] N) (q : M' →ₗ[ℤ] N') (eM : M ≃ₗ[ℤ] M') (eN : N ≃ₗ[ℤ] N')
    (h : ∀ x, eN (L x) = q (eM x)) (y : N) :
    cokernelEquivOfIntertwining L q eM eN h (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (eN y) := rfl

@[simp] theorem cokernelEquivOfIntertwining_symm_apply_mk
    (L : M →ₗ[ℤ] N) (q : M' →ₗ[ℤ] N') (eM : M ≃ₗ[ℤ] M') (eN : N ≃ₗ[ℤ] N')
    (h : ∀ x, eN (L x) = q (eM x)) (y : N') :
    (cokernelEquivOfIntertwining L q eM eN h).symm (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (eN.symm y) := rfl

/-- The exact image index is preserved, including the infinite-index case. -/
theorem range_index_of_intertwining (L : M →ₗ[ℤ] N) (q : M' →ₗ[ℤ] N')
    (eM : M ≃ₗ[ℤ] M') (eN : N ≃ₗ[ℤ] N') (h : ∀ x, eN (L x) = q (eM x)) :
    (LinearMap.range L).toAddSubgroup.index = (LinearMap.range q).toAddSubgroup.index := by
  change Nat.card (N ⧸ LinearMap.range L) = Nat.card (N' ⧸ LinearMap.range q)
  exact Nat.card_congr (cokernelEquivOfIntertwining L q eM eN h).toEquiv

/-- The actual dual coordinate maps commute with pullback by the original linear map. -/
theorem dual_coordinates_commute (L : M →ₗ[ℤ] N) (eM : M ≃ₗ[ℤ] M') (eN : N ≃ₗ[ℤ] N')
    (q : M' →ₗ[ℤ] N') (hq : ∀ x, q x = eN (L (eM.symm x))) (φ : N →ₗ[ℤ] ℤ) :
    eM.symm.dualMap (L.dualMap φ) = q.dualMap (eN.symm.dualMap φ) := by
  apply LinearMap.ext
  intro x
  simp only [LinearEquiv.dualMap_apply, LinearMap.dualMap_apply, hq,
    LinearEquiv.symm_apply_apply]

/-- Coordinate comparison for the actual dual cokernels. -/
def dualCokernelEquivOfCoordinates (L : M →ₗ[ℤ] N)
    (eM : M ≃ₗ[ℤ] M') (eN : N ≃ₗ[ℤ] N') (q : M' →ₗ[ℤ] N')
    (hq : ∀ x, q x = eN (L (eM.symm x))) :
    ((M →ₗ[ℤ] ℤ) ⧸ LinearMap.range L.dualMap) ≃ₗ[ℤ]
      ((M' →ₗ[ℤ] ℤ) ⧸ LinearMap.range q.dualMap) :=
  cokernelEquivOfIntertwining L.dualMap q.dualMap eN.symm.dualMap eM.symm.dualMap
    (dual_coordinates_commute L eM eN q hq)

@[simp] theorem dualCokernelEquivOfCoordinates_apply_mk (L : M →ₗ[ℤ] N)
    (eM : M ≃ₗ[ℤ] M') (eN : N ≃ₗ[ℤ] N') (q : M' →ₗ[ℤ] N')
    (hq : ∀ x, q x = eN (L (eM.symm x))) (φ : M →ₗ[ℤ] ℤ) :
    dualCokernelEquivOfCoordinates L eM eN q hq (Submodule.Quotient.mk φ) =
      Submodule.Quotient.mk (eM.symm.dualMap φ) := rfl

@[simp] theorem dualCokernelEquivOfCoordinates_symm_apply_mk (L : M →ₗ[ℤ] N)
    (eM : M ≃ₗ[ℤ] M') (eN : N ≃ₗ[ℤ] N') (q : M' →ₗ[ℤ] N')
    (hq : ∀ x, q x = eN (L (eM.symm x))) (φ : M' →ₗ[ℤ] ℤ) :
    (dualCokernelEquivOfCoordinates L eM eN q hq).symm (Submodule.Quotient.mk φ) =
      Submodule.Quotient.mk (eM.dualMap φ) := rfl

theorem dualRange_index_of_coordinates (L : M →ₗ[ℤ] N)
    (eM : M ≃ₗ[ℤ] M') (eN : N ≃ₗ[ℤ] N') (q : M' →ₗ[ℤ] N')
    (hq : ∀ x, q x = eN (L (eM.symm x))) :
    (LinearMap.range L.dualMap).toAddSubgroup.index =
      (LinearMap.range q.dualMap).toAddSubgroup.index :=
  range_index_of_intertwining L.dualMap q.dualMap eN.symm.dualMap eM.symm.dualMap
    (dual_coordinates_commute L eM eN q hq)

end Wikipedia.HopfProblem.Elliptic.HigherHomology.CohomologyDualComparison
