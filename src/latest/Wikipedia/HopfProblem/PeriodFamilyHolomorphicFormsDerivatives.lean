import Wikipedia.HopfProblem.PeriodFamily
import Wikipedia.HopfProblem.PeriodTorusQuasiperiodicPeriods

/-!
# Actual derivatives of the varying integral periods

The shift associated to an integral marking is the actual family period
isomorphism applied to its fixed real coefficient vector. Its derivative
is Mathlib's manifold derivative evaluated in the unit base direction.
The two fixed identity columns have zero derivative, and coordinate
evaluation of the second column gives the genuine derivative of `τ`.
-/

noncomputable section

open scoped Matrix ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicForms

open PeriodTorusQuasiperiodic

variable {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B]
  (P : HolomorphicPeriodMap ℂ B)

/-- The actual varying lattice translation with the specified integral marking. -/
def periodShift (b : B) (ell : Lattice) : ComplexPlane₂ :=
  P.periodEquiv b (fun j => (ell j : ℝ))

/-- The family shift agrees with the independently constructed actual period vector. -/
theorem periodShift_eq_periodVector (b : B) (ell : Lattice) :
    periodShift P b ell = (P.point b).periodVector ell := by
  rw [periodShift, P.periodEquiv_coordinates, PeriodDomain.periodVector_apply]
  ext i
  fin_cases i <;>
    simp [PeriodPoint.matrix, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- The literal original period matrix acts on the four integral coefficients. -/
theorem periodShift_eq_matrix (b : B) (ell : Lattice) :
    periodShift P b ell = (P.point b).val.matrix *ᵥ (fun j => (ell j : ℂ)) :=
  periodShift_eq_periodVector P b ell

/-- Each fixed integral period varies holomorphically on the given base atlas. -/
theorem periodShift_holomorphic (ell : Lattice) :
    ContMDiff 𝓘(ℂ) (modelWithCornersSelf ℂ ComplexPlane₂) ω
      (fun b => periodShift P b ell) :=
  P.holomorphic_periodEquiv_const (fun j => (ell j : ℝ))

/-- A standard integral coordinate selects the corresponding original period column. -/
theorem periodShift_single (b : B) (j : Fin 4) :
    periodShift P b (Pi.single j 1) = periodColumn (P.point b) j := by
  rw [periodShift_eq_matrix]
  exact integer_period_single (P.point b) j

@[simp] theorem periodShift_single_two (b : B) :
    periodShift P b (Pi.single (2 : Fin 4) 1) = Pi.single (0 : Fin 2) (1 : ℂ) := by
  rw [periodShift_single, periodColumn_two]

@[simp] theorem periodShift_single_three (b : B) :
    periodShift P b (Pi.single (3 : Fin 4) 1) = Pi.single (1 : Fin 2) (1 : ℂ) := by
  rw [periodShift_single, periodColumn_three]

/-- The genuine derivative of the actual shift in the unit complex base direction. -/
def periodDerivative (b : B) (ell : Lattice) : ComplexPlane₂ :=
  mfderiv 𝓘(ℂ) (modelWithCornersSelf ℂ ComplexPlane₂)
    (fun c => periodShift P c ell) b (1 : ℂ)

/-- Complex linearity recovers the full actual Jacobian from its unit-direction value. -/
theorem mfderiv_periodShift_apply (b : B) (ell : Lattice) (v : ℂ) :
    mfderiv 𝓘(ℂ) (modelWithCornersSelf ℂ ComplexPlane₂)
        (fun c => periodShift P c ell) b v = v • periodDerivative P b ell := by
  let L : ℂ →L[ℂ] ComplexPlane₂ :=
    mfderiv 𝓘(ℂ) (modelWithCornersSelf ℂ ComplexPlane₂) (fun c => periodShift P c ell) b
  change L v = v • L 1
  simpa only [smul_eq_mul, mul_one] using L.map_smul v (1 : ℂ)

/-- The entire genuine derivative vanishes for the first fixed identity column. -/
theorem mfderiv_periodShift_single_two (b : B) :
    (mfderiv 𝓘(ℂ) (modelWithCornersSelf ℂ ComplexPlane₂)
      (fun c => periodShift P c (Pi.single (2 : Fin 4) 1)) b :
        ℂ →L[ℂ] ComplexPlane₂) = 0 := by
  calc
    _ = mfderiv 𝓘(ℂ) (modelWithCornersSelf ℂ ComplexPlane₂)
        (fun _ : B => (Pi.single (0 : Fin 2) (1 : ℂ) : ComplexPlane₂)) b :=
      mfderiv_congr (funext (periodShift_single_two P))
    _ = 0 := mfderiv_const

/-- The entire genuine derivative vanishes for the second fixed identity column. -/
theorem mfderiv_periodShift_single_three (b : B) :
    (mfderiv 𝓘(ℂ) (modelWithCornersSelf ℂ ComplexPlane₂)
      (fun c => periodShift P c (Pi.single (3 : Fin 4) 1)) b :
        ℂ →L[ℂ] ComplexPlane₂) = 0 := by
  calc
    _ = mfderiv 𝓘(ℂ) (modelWithCornersSelf ℂ ComplexPlane₂)
        (fun _ : B => (Pi.single (1 : Fin 2) (1 : ℂ) : ComplexPlane₂)) b :=
      mfderiv_congr (funext (periodShift_single_three P))
    _ = 0 := mfderiv_const

@[simp] theorem periodDerivative_single_two (b : B) :
    periodDerivative P b (Pi.single (2 : Fin 4) 1) = 0 :=
  congrArg (fun L : ℂ →L[ℂ] ComplexPlane₂ => L 1) (mfderiv_periodShift_single_two P b)

@[simp] theorem periodDerivative_single_three (b : B) :
    periodDerivative P b (Pi.single (3 : Fin 4) 1) = 0 :=
  congrArg (fun L : ℂ →L[ℂ] ComplexPlane₂ => L 1) (mfderiv_periodShift_single_three P b)

/-- Evaluation of a coordinate commutes with the actual derivative by the chain rule. -/
theorem periodDerivative_coordinate (b : B) (ell : Lattice) (i : Fin 2) :
    periodDerivative P b ell i =
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun c => periodShift P c ell i) b (1 : ℂ) := by
  let L : ComplexPlane₂ →L[ℂ] ℂ := ContinuousLinearMap.proj i
  have h := mfderiv_comp_apply b (g := L) (f := fun c => periodShift P c ell)
    L.mdifferentiableAt ((periodShift_holomorphic P ell).mdifferentiable (by simp) b) (1 : ℂ)
  rw [ContinuousLinearMap.mfderiv_eq] at h
  exact h.symm

/-- The first coordinate of the second period derivative is the genuine `τ` derivative. -/
theorem periodDerivative_single_one_zero (b : B) :
    periodDerivative P b (Pi.single (1 : Fin 4) 1) 0 =
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun c => (P.point c).val.τ) b (1 : ℂ) := by
  apply (periodDerivative_coordinate P b (Pi.single (1 : Fin 4) 1) 0).trans
  apply congrArg (fun L : ℂ →L[ℂ] ℂ => L 1)
  apply mfderiv_congr
  funext c
  rw [periodShift_single]
  rfl

/-- The second coordinate of the same column is the genuine `μ` derivative. -/
theorem periodDerivative_single_one_one (b : B) :
    periodDerivative P b (Pi.single (1 : Fin 4) 1) 1 =
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun c => (P.point c).val.μ) b (1 : ℂ) := by
  apply (periodDerivative_coordinate P b (Pi.single (1 : Fin 4) 1) 1).trans
  apply congrArg (fun L : ℂ →L[ℂ] ℂ => L 1)
  apply mfderiv_congr
  funext c
  rw [periodShift_single]
  rfl

/-- The second coordinate of the first column is the genuine `β` derivative. -/
theorem periodDerivative_single_zero_one (b : B) :
    periodDerivative P b (Pi.single (0 : Fin 4) 1) 1 =
      mfderiv 𝓘(ℂ) 𝓘(ℂ) (fun c => (P.point c).val.β) b (1 : ℂ) := by
  apply (periodDerivative_coordinate P b (Pi.single (0 : Fin 4) 1) 1).trans
  apply congrArg (fun L : ℂ →L[ℂ] ℂ => L 1)
  apply mfderiv_congr
  funext c
  rw [periodShift_single]
  rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicForms
