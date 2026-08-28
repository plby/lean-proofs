import Mathlib.Algebra.Module.Equiv.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Prod
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Finiteness.Prod
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Finite products with native integral module structures

An abelian group has a unique `ℤ`-module structure. The product lemmas in
this file explicitly retain an arbitrary supplied integral module
instance on the underlying product. This makes them applicable to the
native homology objects, whose integer action need not be definitionally
the standard pointwise product action.
-/

noncomputable section

open scoped BigOperators TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.Finiteness

/-- Transport finite generation through an additive equivalence using the
actual integer actions on its source and target. -/
theorem finite_int_of_addEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (e : M ≃+ N) [Module.Finite ℤ M] :
    Module.Finite ℤ N :=
  Module.Finite.of_surjective e.toIntLinearEquiv.toLinearMap e.surjective

/-- A finite dependent product is finitely generated with any supplied
integer action on its native abelian group. -/
theorem finite_pi_int {ι : Type*} [Finite ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℤ (M i)]
    [∀ i, Module.Finite ℤ (M i)] [piModule : Module ℤ (∀ i, M i)] :
    Module.Finite ℤ (∀ i, M i) := by
  have h : piModule = Pi.module ι M ℤ := Subsingleton.elim _ _
  cases h
  exact Module.Finite.pi

/-- A binary product is finitely generated with its supplied native integer action. -/
theorem finite_prod_int (M N : Type*) [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] [Module.Finite ℤ M] [Module.Finite ℤ N]
    [prodModule : Module ℤ (M × N)] : Module.Finite ℤ (M × N) := by
  have h : prodModule = (Prod.instModule : Module ℤ (M × N)) := Subsingleton.elim _ _
  cases h
  exact Module.Finite.prod

/-- Additive identifications induce the actual tensor base-change equivalence,
even when the integer module instances are not definitionally identical. -/
def rationalizationEquivOfAddEquiv {M N : Type*} [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] (e : M ≃+ N) :
    (ℚ ⊗[ℤ] M) ≃ₗ[ℚ] (ℚ ⊗[ℤ] N) :=
  LinearEquiv.baseChange ℤ ℚ M N e.toIntLinearEquiv

/-- Rational dimension is unchanged by an additive equivalence; no freeness
or finite-generation assumption is necessary for this equality. -/
theorem rational_finrank_eq_of_addEquiv {M N : Type*}
    [AddCommGroup M] [AddCommGroup N] [Module ℤ M] [Module ℤ N] (e : M ≃+ N) :
    Module.finrank ℚ (ℚ ⊗[ℤ] M) = Module.finrank ℚ (ℚ ⊗[ℤ] N) :=
  (rationalizationEquivOfAddEquiv e).finrank_eq

/-- Rationalization commutes with a finite dependent product. The arbitrary
native integer action on that product is retained in the statement. -/
theorem rational_finrank_pi_int {ι : Type*} [Fintype ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℤ (M i)]
    [∀ i, Module.Finite ℤ (M i)] [piModule : Module ℤ (∀ i, M i)] :
    Module.finrank ℚ (ℚ ⊗[ℤ] (∀ i, M i)) =
      ∑ i, Module.finrank ℚ (ℚ ⊗[ℤ] M i) := by
  classical
  have h : piModule = Pi.module ι M ℤ := Subsingleton.elim _ _
  cases h
  exact (TensorProduct.piRight ℤ ℚ ℚ M).finrank_eq.trans
    (Module.finrank_pi_fintype ℚ)

/-- Rational dimension adds over binary products of finite integral modules,
including the native product actions supplied by homology objects. -/
theorem rational_finrank_prod_int (M N : Type*) [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] [Module.Finite ℤ M] [Module.Finite ℤ N]
    [prodModule : Module ℤ (M × N)] :
    Module.finrank ℚ (ℚ ⊗[ℤ] (M × N)) =
      Module.finrank ℚ (ℚ ⊗[ℤ] M) + Module.finrank ℚ (ℚ ⊗[ℤ] N) := by
  have h : prodModule = (Prod.instModule : Module ℤ (M × N)) := Subsingleton.elim _ _
  cases h
  exact (TensorProduct.prodRight ℤ ℚ ℚ M N).finrank_eq.trans Module.finrank_prod

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.Finiteness
