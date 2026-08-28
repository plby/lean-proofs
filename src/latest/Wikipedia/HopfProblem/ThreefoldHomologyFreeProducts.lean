import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessProducts
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Noetherian.Orzech

/-!
# Free finite products with their native integer actions

The unique integer action on an abelian group lets the usual free-product
and integral-rank theorems apply to the literal products of singular
homology objects.  No scalar action is silently replaced in the statements.
-/

noncomputable section

open scoped BigOperators

namespace Wikipedia.HopfProblem.ThreefoldHomologyFreeProducts

theorem free_pi_int {ι : Type*} [Finite ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℤ (M i)]
    [∀ i, Module.Free ℤ (M i)] [piModule : Module ℤ (∀ i, M i)] :
    Module.Free ℤ (∀ i, M i) := by
  have h : piModule = Pi.module ι M ℤ := Subsingleton.elim _ _
  cases h
  infer_instance

theorem free_prod_int (M N : Type*) [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] [Module.Free ℤ M] [Module.Free ℤ N]
    [prodModule : Module ℤ (M × N)] : Module.Free ℤ (M × N) := by
  have h : prodModule = (Prod.instModule : Module ℤ (M × N)) := Subsingleton.elim _ _
  cases h
  infer_instance

theorem finrank_pi_int {ι : Type*} [Fintype ι] (M : ι → Type*)
    [∀ i, AddCommGroup (M i)] [∀ i, Module ℤ (M i)]
    [∀ i, Module.Free ℤ (M i)] [∀ i, Module.Finite ℤ (M i)]
    [piModule : Module ℤ (∀ i, M i)] :
    Module.finrank ℤ (∀ i, M i) = ∑ i, Module.finrank ℤ (M i) := by
  have h : piModule = Pi.module ι M ℤ := Subsingleton.elim _ _
  cases h
  exact Module.finrank_pi_fintype ℤ

theorem finrank_prod_int (M N : Type*) [AddCommGroup M] [AddCommGroup N]
    [Module ℤ M] [Module ℤ N] [Module.Free ℤ M] [Module.Free ℤ N]
    [Module.Finite ℤ M] [Module.Finite ℤ N] [prodModule : Module ℤ (M × N)] :
    Module.finrank ℤ (M × N) = Module.finrank ℤ M + Module.finrank ℤ N := by
  have h : prodModule = (Prod.instModule : Module ℤ (M × N)) := Subsingleton.elim _ _
  cases h
  exact Module.finrank_prod

end Wikipedia.HopfProblem.ThreefoldHomologyFreeProducts
