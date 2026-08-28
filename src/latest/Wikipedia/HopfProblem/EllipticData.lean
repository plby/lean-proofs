import Wikipedia.HopfProblem.Lattice
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# The two elliptic logarithmic twists

This file fixes the actual order-three and order-four integral matrices
and twist vectors used in §5.  The flat affine maps below act on real
lattice coordinates; subsequent files transport them to the complex
period tori and construct the finite free quotients.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.Elliptic

inductive Kind where
  | three
  | four
  deriving DecidableEq

instance : Fintype Kind := ⟨{.three, .four}, by intro j; cases j <;> simp⟩

namespace Kind

def order : Kind → ℕ
  | .three => 3
  | .four => 4

def matrix : Kind → LatticeMatrix
  | .three => A₁
  | .four => A₂

/-- The twists actually chosen for the threefold: `ε` and `-ε'`. -/
def twist : Kind → Lattice
  | .three => ε
  | .four => -ε'

theorem order_pos (j : Kind) : 0 < j.order := by cases j <;> decide

theorem matrix_pow_order (j : Kind) : j.matrix ^ j.order = 1 := by
  cases j <;> decide

theorem matrix_fixes_twist (j : Kind) : j.matrix *ᵥ j.twist = j.twist := by
  cases j <;> decide

theorem twist_gamma (j : Kind) : γ j.twist = if j = .three then 1 else -1 := by
  cases j <;> rfl

end Kind

abbrev RealCoordinates := Fin 4 → ℝ

def realCast (v : Lattice) : RealCoordinates := fun i => (v i : ℝ)

def flatLinear (j : Kind) : RealCoordinates →ₗ[ℝ] RealCoordinates :=
  (j.matrix.map (Int.castRingHom ℝ)).mulVecLin

def flatAffine (j : Kind) (v : Lattice) (x : RealCoordinates) : RealCoordinates :=
  flatLinear j x + (1 / (j.order : ℝ)) • realCast v

/-- Congruence modulo the actual integral coordinate lattice. -/
def FlatCongruent (x y : RealCoordinates) : Prop := ∃ v : Lattice, x - y = realCast v

/-- The admissibility condition of Proposition 5.6. -/
def AdmissibleTwist (j : Kind) (v : Lattice) : Prop :=
  j.matrix *ᵥ v = v ∧ if j = .three then ¬3 ∣ γ v else Odd (γ v)

theorem mainTwist_admissible (j : Kind) : AdmissibleTwist j j.twist := by
  refine ⟨j.matrix_fixes_twist, ?_⟩
  cases j <;> norm_num [Kind.twist, γ, ε, ε']

end Wikipedia.HopfProblem.Elliptic
