import Mathlib.LinearAlgebra.Quotient.Basic
import Mathlib.LinearAlgebra.Prod
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Integral algebra for the actual deck coinvariants

The cokernel of a block-diagonal product operator is the product of
its actual cokernels.  The equivalence preserves the literal quotient
classes.  A second elementary lemma identifies any two-coordinate map
fixing the first basis vector and scaling the second coordinate as a
triangular map, and proves injectivity when the second multiplier is
nonzero.  These are algebraic helpers for the actual deck-homology maps.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

section Product

variable {M N : Type*} [AddCommGroup M] [Module ℤ M]
  [AddCommGroup N] [Module ℤ N]

local instance cokernelProductModule : Module ℤ (M × N) := Prod.instModule

/-- The actual cokernel of a product operator, with no abstract
replacement of either image submodule. -/
def prodCokernelEquiv (f : M →ₗ[ℤ] M) (g : N →ₗ[ℤ] N) :
    ((M × N) ⧸ LinearMap.range (f.prodMap g)) ≃ₗ[ℤ]
      (M ⧸ LinearMap.range f) × (N ⧸ LinearMap.range g) :=
  ((QuotientAddGroup.quotientAddEquivOfEq
    (show (LinearMap.range (f.prodMap g)).toAddSubgroup =
        (LinearMap.range f).toAddSubgroup.prod (LinearMap.range g).toAddSubgroup from
      congrArg Submodule.toAddSubgroup (LinearMap.range_prodMap f g))).trans
    (QuotientAddGroup.prodAddEquiv (LinearMap.range f).toAddSubgroup
      (LinearMap.range g).toAddSubgroup)).toIntLinearEquiv

@[simp] theorem prodCokernelEquiv_mk (f : M →ₗ[ℤ] M) (g : N →ₗ[ℤ] N) (x : M) (y : N) :
    prodCokernelEquiv f g (Submodule.Quotient.mk (x, y)) =
      (Submodule.Quotient.mk x, Submodule.Quotient.mk y) := rfl

@[simp] theorem prodCokernelEquiv_symm_mk
    (f : M →ₗ[ℤ] M) (g : N →ₗ[ℤ] N) (x : M) (y : N) :
    (prodCokernelEquiv f g).symm (Submodule.Quotient.mk x, Submodule.Quotient.mk y) =
      Submodule.Quotient.mk (x, y) := rfl

end Product

/-- Fixing the first integral basis vector and scaling the second
coordinate determines this literal triangular form. -/
theorem triangularFinTwo_apply (F : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ)) (d : ℤ)
    (hfirst : F ![1, 0] = ![1, 0])
    (hsecond : ∀ v, F v 1 = d * v 1) (v : Fin 2 → ℤ) :
    F v = ![v 0 + (F ![0, 1]) 0 * v 1, d * v 1] := by
  have hv : v = v 0 • ![1, 0] + v 1 • ![0, 1] := by
    ext i
    fin_cases i <;> simp [Pi.add_apply]
  have hF : F v = v 0 • ![1, 0] + v 1 • F ![0, 1] := by
    calc
      F v = F (v 0 • ![1, 0] + v 1 • ![0, 1]) := congrArg F hv
      _ = v 0 • ![1, 0] + v 1 • F ![0, 1] := by
        rw [map_add, map_smul, map_smul, hfirst]
  ext i
  fin_cases i
  · simpa [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_comm] using congrFun hF 0
  · exact hsecond v

/-- The actual triangular map is injective when its second diagonal
entry is nonzero; no injectivity is supplied separately. -/
theorem triangularFinTwo_injective (F : (Fin 2 → ℤ) →ₗ[ℤ] (Fin 2 → ℤ)) (d : ℤ)
    (hfirst : F ![1, 0] = ![1, 0])
    (hsecond : ∀ v, F v 1 = d * v 1) (hd : d ≠ 0) : Function.Injective F := by
  intro v w h
  have hm : d * v 1 = d * w 1 := by
    rw [← hsecond v, ← hsecond w, h]
  have h₁ : v 1 = w 1 := mul_left_cancel₀ hd hm
  rw [triangularFinTwo_apply F d hfirst hsecond v,
    triangularFinTwo_apply F d hfirst hsecond w] at h
  have h₀ := congrFun h 0
  change v 0 + (F ![0, 1]) 0 * v 1 = w 0 + (F ![0, 1]) 0 * w 1 at h₀
  rw [h₁] at h₀
  have h₀' : v 0 = w 0 := add_right_cancel h₀
  ext i
  fin_cases i
  · exact h₀'
  · exact h₁

end Wikipedia.HopfProblem.Elliptic.HigherHomology
