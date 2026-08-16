import Wikipedia.SzemeredisTheorem.Finite.Mean
import Mathlib.Data.ZMod.Basic

/-!
# Affine forms and the arithmetic-progression linear-forms system

The relative Szemerédi theorem uses one specific family of linear forms.  For
`j < k` and a vertex `ω` of the cube with the `j`th coordinate deleted, the
form is

`ψ_{j,ω}(x) = ∑ i ≠ j, (i - j) * xᵢ^(ωᵢ)`.

The quantitative predicate at the end of this file says that every
subproduct of these `k * 2^(k-1)` forms has normalized average within `η` of
one.  Encoding subproducts by Boolean exponents exactly matches the
Conlon--Fox--Zhao linear-forms condition.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- A finitely supported affine form, represented by all of its coefficients
on a finite index type. -/
structure AffineForm (ι R : Type*) [Zero R] where
  constant : R
  coefficient : ι → R

namespace AffineForm

/-- Evaluate an affine form at a vector. -/
def eval {ι R : Type*} [Fintype ι] [Semiring R]
    (ψ : AffineForm ι R) (x : ι → R) : R :=
  ψ.constant + ∑ i, ψ.coefficient i * x i

@[simp]
theorem eval_zero {ι R : Type*} [Fintype ι] [Semiring R]
    (ψ : AffineForm ι R) :
    ψ.eval (fun _ => 0) = ψ.constant := by
  simp [eval]

end AffineForm

/-- A point carrying two independent values in every one of `k`
coordinates. -/
abbrev CubePoint (k N : ℕ) :=
  Fin k → Bool → ZMod N

/-- A Boolean vertex of the `(k-1)`-cube obtained by deleting coordinate
`j`. -/
abbrev DeletedCube (k : ℕ) (j : Fin k) :=
  {i : Fin k // i ≠ j} → Bool

/-- The Conlon--Fox--Zhao form indexed by `j` and `ω`. -/
def apLinearForm (k N : ℕ) (j : Fin k) (ω : DeletedCube k j)
    (x : CubePoint k N) : ZMod N :=
  ∑ i : {i : Fin k // i ≠ j},
    (((i.1 : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x i.1 (ω i)

/-- Boolean choices of the subproduct of the arithmetic-progression linear-forms
system to be tested. -/
abbrev LinearFormsExponent (k : ℕ) :=
  (j : Fin k) → DeletedCube k j → Bool

/-- The subproduct selected by `e`, evaluated at the doubled variable
vector `x`. -/
def linearFormsProduct (k N : ℕ) (ν : ZMod N → ℝ)
    (e : LinearFormsExponent k) (x : CubePoint k N) : ℝ :=
  ∏ j : Fin k, ∏ ω : DeletedCube k j,
    if e j ω then ν (apLinearForm k N j ω x) else 1

/-- Quantitative `k`-linear-forms condition.

Every subproduct of the canonical arithmetic-progression forms must have
normalized average within `η` of one. -/
def HasLinearFormsCondition (k N : ℕ) [NeZero N]
    (ν : ZMod N → ℝ) (η : ℝ) : Prop :=
  ∀ e : LinearFormsExponent k,
    |mean (linearFormsProduct k N ν e) - 1| ≤ η

theorem HasLinearFormsCondition.mono {k N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {η η' : ℝ}
    (hν : HasLinearFormsCondition k N ν η) (hη : η ≤ η') :
    HasLinearFormsCondition k N ν η' :=
  fun e => (hν e).trans hη

end Wikipedia.SzemeredisTheorem
