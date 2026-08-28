import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyDual
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.Data.ZMod.QuotientGroup

/-!
# The actual dual of a scalar map on an integer line

A literal scalar map on `ℤ¹` induces the same scalar map on its integer
dual.  Its actual dual cokernel is reduction modulo that scalar of
evaluation on the standard basis vector.  The index formula includes
the zero scalar, using the infinite-index convention.

These are algebraic statements about an explicitly specified linear map,
with no cohomological or topological covering interpretation assumed.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology.CohomologyDualAlgebra

abbrev rankOneLattice := Fin 1 → ℤ
abbrev rankOneDual := rankOneLattice →ₗ[ℤ] ℤ

/-- Evaluation on the unique standard basis vector identifies the actual dual with `ℤ`. -/
def rankOneDualEquivInt : rankOneDual ≃ₗ[ℤ] ℤ :=
  (intDualCoordinates 1).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ)

@[simp] theorem rankOneDualEquivInt_apply (φ : rankOneDual) :
    rankOneDualEquivInt φ = φ (Pi.single (0 : Fin 1) 1) := by
  change intDualCoordinates 1 φ 0 = _
  exact intDualCoordinates_apply 1 φ 0

@[simp] theorem rankOneDualEquivInt_symm_apply (k : ℤ) (x : rankOneLattice) :
    rankOneDualEquivInt.symm k x = k * x 0 := by
  change (intDualCoordinates 1).symm (fun _ => k) x = _
  rw [intDualCoordinates_symm_apply]
  simp

variable (d : ℕ) (q : rankOneLattice →ₗ[ℤ] rankOneLattice)

theorem rankOneDualMap_apply (hq : ∀ x, q x = d • x)
    (φ : rankOneDual) (x : rankOneLattice) :
    q.dualMap φ x = (d : ℤ) * φ x := by
  rw [LinearMap.dualMap_apply, hq, map_nsmul, nsmul_eq_mul]

/-- The actual dual map is multiplication by `d` in the canonical dual coordinates. -/
theorem rankOneDualMap_coordinates (hq : ∀ x, q x = d • x) (φ : rankOneDual) :
    intDualCoordinates 1 (q.dualMap φ) = d • intDualCoordinates 1 φ := by
  funext i
  change intDualCoordinates 1 (q.dualMap φ) i = d • intDualCoordinates 1 φ i
  rw [intDualCoordinates_apply, rankOneDualMap_apply d q hq,
    intDualCoordinates_apply, nsmul_eq_mul]

theorem rankOneDualMap_equivInt (hq : ∀ x, q x = d • x) (φ : rankOneDual) :
    rankOneDualEquivInt (q.dualMap φ) = (d : ℤ) * rankOneDualEquivInt φ := by
  rw [rankOneDualEquivInt_apply, rankOneDualMap_apply d q hq, rankOneDualEquivInt_apply]

/-- The explicit residue functional on the actual integer dual. -/
def rankOneDualResidue : rankOneDual →ₗ[ℤ] ZMod d :=
  (Int.castAddHom (ZMod d)).toIntLinearMap.comp rankOneDualEquivInt.toLinearMap

@[simp] theorem rankOneDualResidue_apply (φ : rankOneDual) :
    rankOneDualResidue d φ = (φ (Pi.single (0 : Fin 1) 1) : ZMod d) := by
  change (rankOneDualEquivInt φ : ZMod d) = _
  rw [rankOneDualEquivInt_apply]

theorem rankOneDualResidue_surjective : Function.Surjective (rankOneDualResidue d) := by
  intro z
  obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
  refine ⟨rankOneDualEquivInt.symm k, ?_⟩
  change (rankOneDualEquivInt (rankOneDualEquivInt.symm k) : ZMod d) = (k : ZMod d)
  rw [LinearEquiv.apply_symm_apply]

/-- The actual dual image has precisely the stated divisibility condition. -/
theorem rankOneDualMap_range_iff (hq : ∀ x, q x = d • x) (φ : rankOneDual) :
    φ ∈ LinearMap.range q.dualMap ↔ (d : ℤ) ∣ φ (Pi.single (0 : Fin 1) 1) := by
  rw [← rankOneDualEquivInt_apply φ]
  constructor
  · rintro ⟨ψ, rfl⟩
    exact ⟨rankOneDualEquivInt ψ, rankOneDualMap_equivInt d q hq ψ⟩
  · rintro ⟨k, hk⟩
    refine ⟨rankOneDualEquivInt.symm k, rankOneDualEquivInt.injective ?_⟩
    rw [rankOneDualMap_equivInt d q hq, LinearEquiv.apply_symm_apply, ← hk]

theorem rankOneDualMap_range_eq_ker (hq : ∀ x, q x = d • x) :
    LinearMap.range q.dualMap = LinearMap.ker (rankOneDualResidue d) := by
  ext φ
  rw [rankOneDualMap_range_iff d q hq, LinearMap.mem_ker, rankOneDualResidue_apply,
    ZMod.intCast_zmod_eq_zero_iff_dvd]

/-- The actual cokernel of the dual map, not merely a coordinate-model quotient. -/
def rankOneDualCokernelEquivZMod (hq : ∀ x, q x = d • x) :
    (rankOneDual ⧸ LinearMap.range q.dualMap) ≃ₗ[ℤ] ZMod d :=
  (Submodule.quotEquivOfEq _ _ (rankOneDualMap_range_eq_ker d q hq)).trans
    ((rankOneDualResidue d).quotKerEquivOfSurjective (rankOneDualResidue_surjective d))

@[simp] theorem rankOneDualCokernelEquivZMod_apply_mk (hq : ∀ x, q x = d • x)
    (φ : rankOneDual) :
    rankOneDualCokernelEquivZMod d q hq (Submodule.Quotient.mk φ) =
      (φ (Pi.single (0 : Fin 1) 1) : ZMod d) := by
  simp [rankOneDualCokernelEquivZMod]

@[simp] theorem rankOneDualCokernelEquivZMod_symm_apply_intCast
    (hq : ∀ x, q x = d • x) (k : ℤ) :
    (rankOneDualCokernelEquivZMod d q hq).symm (k : ZMod d) =
      Submodule.Quotient.mk (rankOneDualEquivInt.symm k) := by
  apply (rankOneDualCokernelEquivZMod d q hq).injective
  rw [LinearEquiv.apply_symm_apply, rankOneDualCokernelEquivZMod_apply_mk,
    ← rankOneDualEquivInt_apply (rankOneDualEquivInt.symm k),
    LinearEquiv.apply_symm_apply]

/-- The image index in the actual dual is exactly the scalar, including `d = 0`. -/
theorem rankOneDualMap_range_index (hq : ∀ x, q x = d • x) :
    (LinearMap.range q.dualMap).toAddSubgroup.index = d := by
  change Nat.card (rankOneDual ⧸ LinearMap.range q.dualMap) = d
  calc
    _ = Nat.card (ZMod d) := Nat.card_congr (rankOneDualCokernelEquivZMod d q hq).toEquiv
    _ = d := Nat.card_zmod d

end Wikipedia.HopfProblem.Elliptic.HigherHomology.CohomologyDualAlgebra
