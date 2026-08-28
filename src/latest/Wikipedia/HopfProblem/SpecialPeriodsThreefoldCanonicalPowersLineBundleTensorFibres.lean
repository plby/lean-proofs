import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleBasic
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPowersLineBundleTensorFibresAlgebra
import Mathlib.RingTheory.PiTensorProduct

/-!
# Genuine tensor powers of the fibres of a holomorphic line bundle

The native fibre of the power cocycle is identified with the full finite
tensor product of the original native fibre.  These are linear equivalences
on the actual tensor products, not just formulas on scalar labels.  The
equivalences intertwine the full tensor products of coordinate changes and
of valid native local trivializations.
-/

noncomputable section

open Bundle Set
open scoped TensorProduct

namespace Wikipedia.HopfProblem.CanonicalGlobalLineBundle.Powers

open HolomorphicCharacterBundle

/-- Multiplication identifies the full tensor power of the scalar field
with the scalar field. -/
def scalarTensorPowerEquiv (n : ℕ) : TensorPower ℂ n ≃ₗ[ℂ] ℂ :=
  (PiTensorProduct.constantBaseRingEquiv (Fin n) ℂ).toLinearEquiv

@[simp] theorem scalarTensorPowerEquiv_tprod (n : ℕ) (v : Fin n → ℂ) :
    scalarTensorPowerEquiv n (PiTensorProduct.tprod ℂ v) = ∏ k, v k :=
  PiTensorProduct.constantBaseRingEquiv_tprod v

@[simp] theorem scalarTensorPowerEquiv_purePower (n : ℕ) (v : ℂ) :
    scalarTensorPowerEquiv n (purePower v n) = v ^ n := by
  simp [purePower]

variable {M ι : Type*} [TopologicalSpace M]

/-- The full algebraic tensor power of an actual native fibre, identified
with the actual native fibre of the power cocycle. -/
def fiberTensorPowerEquiv (A : TransitionData M ι) (x : M) (n : ℕ) :
    TensorPower (A.core.Fiber x) n ≃ₗ[ℂ] (A.power n).core.Fiber x :=
  scalarTensorPowerEquiv n

@[simp] theorem fiberTensorPowerEquiv_tprod (A : TransitionData M ι) (x : M) (n : ℕ)
    (v : Fin n → A.core.Fiber x) :
    fiberTensorPowerEquiv A x n (PiTensorProduct.tprod ℂ v) =
      ∏ k, id (α := ℂ) (v k) :=
  scalarTensorPowerEquiv_tprod n v

@[simp] theorem fiberTensorPowerEquiv_purePower (A : TransitionData M ι) (x : M) (n : ℕ)
    (v : A.core.Fiber x) :
    fiberTensorPowerEquiv A x n (purePower v n) = (id (α := ℂ) v) ^ n :=
  scalarTensorPowerEquiv_purePower n v

/-- Taking a pure tensor power preserves nonvanishing in the native
powered fibre, including the zeroth power. -/
theorem fiberTensorPowerEquiv_purePower_ne_zero (A : TransitionData M ι) (x : M) (n : ℕ)
    (v : A.core.Fiber x) (hv : v ≠ 0) :
    fiberTensorPowerEquiv A x n (purePower v n) ≠ 0 := by
  rw [fiberTensorPowerEquiv_purePower]
  change (id (α := ℂ) v) ^ n ≠ (0 : ℂ)
  exact pow_ne_zero n (show (id (α := ℂ) v) ≠ (0 : ℂ) from hv)

/-- Full linear-map compatibility with the tensor product of all the
original coordinate changes. -/
theorem fiberTensorPowerEquiv_coordChange (A : TransitionData M ι) (n : ℕ)
    (i j : ι) (x : M) :
    (fiberTensorPowerEquiv A x n).toLinearMap ∘ₗ
        tensorPowerMap (A.core.coordChange i j x).toLinearMap n =
      ((A.power n).core.coordChange i j x).toLinearMap ∘ₗ
        (fiberTensorPowerEquiv A x n).toLinearMap := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  change scalarTensorPowerEquiv n
      (tensorPowerMap (A.core.coordChange i j x).toLinearMap n
        (PiTensorProduct.tprod ℂ v)) =
    (A.power n).core.coordChange i j x
      (scalarTensorPowerEquiv n (PiTensorProduct.tprod ℂ v))
  rw [tensorPowerMap_tprod, scalarTensorPowerEquiv_tprod, scalarTensorPowerEquiv_tprod]
  change (∏ k, (A.transition i j x : ℂ) * v k) =
    (A.transition i j x : ℂ) ^ n * ∏ k, v k
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- The native powered local coefficient of an elementary tensor is the
product of the original native local coefficients. -/
theorem fiberTensorPowerEquiv_localTriv_tprod (A : TransitionData M ι) (n : ℕ)
    (i : ι) (x : M) (v : Fin n → A.core.Fiber x) :
    ((A.power n).core.localTriv i
        ⟨x, fiberTensorPowerEquiv A x n (PiTensorProduct.tprod ℂ v)⟩).2 =
      ∏ k, (A.core.localTriv i ⟨x, v k⟩).2 := by
  rw [TransitionData.power_core_localTriv_apply]
  simp only [TransitionData.core_localTriv_apply, fiberTensorPowerEquiv_tprod,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, id_eq]

/-- Compatibility on the full tensor product with the actual native local
trivializations over their domain. -/
theorem fiberTensorPowerEquiv_localTriv (A : TransitionData M ι) (n : ℕ)
    (i : ι) (x : M) (hx : x ∈ A.baseSet i) :
    ((A.power n).core.localTriv i).linearMapAt ℂ x ∘ₗ
        (fiberTensorPowerEquiv A x n).toLinearMap =
      (scalarTensorPowerEquiv n).toLinearMap ∘ₗ
        tensorPowerMap ((A.core.localTriv i).linearMapAt ℂ x) n := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro v
  simp only [LinearMap.compMultilinearMap_apply, LinearMap.comp_apply,
    tensorPowerMap, PiTensorProduct.map_tprod, LinearEquiv.coe_toLinearMap,
    scalarTensorPowerEquiv_tprod]
  rw [Trivialization.coe_linearMapAt_of_mem _ hx]
  change ((A.power n).core.localTriv i
      ⟨x, fiberTensorPowerEquiv A x n (PiTensorProduct.tprod ℂ v)⟩).2 =
    ∏ k, ((A.core.localTriv i).linearMapAt ℂ x) (v k)
  rw [fiberTensorPowerEquiv_localTriv_tprod]
  apply Finset.prod_congr rfl
  intro k _
  rw [Trivialization.coe_linearMapAt_of_mem _ hx]

/-- For a pure tensor power the exact native coefficient is the power of
the original native coefficient. -/
theorem fiberTensorPowerEquiv_localTriv_purePower (A : TransitionData M ι) (n : ℕ)
    (i : ι) (x : M) (v : A.core.Fiber x) :
    ((A.power n).core.localTriv i
        ⟨x, fiberTensorPowerEquiv A x n (purePower v n)⟩).2 =
      ((A.core.localTriv i ⟨x, v⟩).2) ^ n := by
  simpa only [purePower, Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    fiberTensorPowerEquiv_localTriv_tprod A n i x (fun _ => v)

end Wikipedia.HopfProblem.CanonicalGlobalLineBundle.Powers
