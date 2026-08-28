import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierParameterVertical
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDecay

/-!
# Elliptic operators on genuine jointly smooth torus families

Subtraction and actual vertical differentiation preserve joint smoothness.
Consequently the coordinate operators `1 - Dᵢ²`, their finite product, and
every iterate are genuine jointly smooth families on the original base.
Their slices are exactly the previously constructed torus operators.
-/

noncomputable section

open TopologicalSpace UnitAddTorus
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter

open PeriodTorusLineBundleClassification

variable {U : Opens ℂ} {d : Type*} [Fintype d]

namespace SmoothFamily

/-- Pointwise subtraction of the original functions preserves joint smoothness. -/
def sub (f g : SmoothFamily U d) : SmoothFamily U d where
  toFun x := f x - g x
  smooth_lift := (f.smooth_lift.sub g.smooth_lift).congr (fun x hx => by
    change x.1 ∈ U at hx
    simp only [ambientLift, dif_pos hx])

@[simp] theorem sub_apply (f g : SmoothFamily U d) (x : U × UnitAddTorus d) :
    f.sub g x = f x - g x := rfl

variable [DecidableEq d]

/-- The actual coordinate operator `1 - Dᵢ²` on the joint family. -/
def coordinateElliptic (f : SmoothFamily U d) (i : d) : SmoothFamily U d :=
  f.sub ((f.verticalDerivative (Pi.single i 1)).verticalDerivative (Pi.single i 1))

/-- The coordinate family operator is literally the frozen torus operator on each fibre. -/
@[simp] theorem coordinateElliptic_slice (f : SmoothFamily U d) (i : d) (b : U) :
    (f.coordinateElliptic i).slice b = torusCoordinateElliptic (f.slice b) i := rfl

/-- Apply a finite list of coordinate elliptic operators to the actual joint family. -/
def ellipticList : List d → SmoothFamily U d → SmoothFamily U d
  | [], f => f
  | i :: s, f => coordinateElliptic (ellipticList s f) i

@[simp] theorem ellipticList_slice (s : List d) (f : SmoothFamily U d) (b : U) :
    (ellipticList s f).slice b = torusEllipticList s (f.slice b) := by
  induction s with
  | nil => rfl
  | cons i s ih =>
    simp only [ellipticList, coordinateElliptic_slice, torusEllipticList, ih]

/-- The product of all coordinate elliptic operators on the joint family. -/
def ellipticOperator (f : SmoothFamily U d) : SmoothFamily U d :=
  ellipticList Finset.univ.toList f

@[simp] theorem ellipticOperator_slice (f : SmoothFamily U d) (b : U) :
    (ellipticOperator f).slice b = torusEllipticOperator (f.slice b) :=
  ellipticList_slice Finset.univ.toList f b

/-- Every iterate is jointly smooth, with no separately supplied derivative premise. -/
def ellipticPower : ℕ → SmoothFamily U d → SmoothFamily U d
  | 0, f => f
  | n + 1, f => ellipticOperator (ellipticPower n f)

@[simp] theorem ellipticPower_slice (n : ℕ) (f : SmoothFamily U d) (b : U) :
    (ellipticPower n f).slice b = torusEllipticPower n (f.slice b) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [ellipticPower, ellipticOperator_slice, torusEllipticPower, ih]

/-- The Fourier coefficients of the actual joint elliptic tower have the exact multiplier. -/
theorem ellipticPower_coeff (n : ℕ) (f : SmoothFamily U d) (b : U) (k : d → ℤ) :
    mFourierCoeff (fun t => ellipticPower n f (b, t)) k =
      (fourierEllipticWeight k : ℂ) ^ n * mFourierCoeff (fun t => f (b, t)) k := by
  change mFourierCoeff ((ellipticPower n f).slice b) k =
    (fourierEllipticWeight k : ℂ) ^ n * mFourierCoeff (f.slice b) k
  rw [ellipticPower_slice, torusEllipticPower_coeff]

end SmoothFamily

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter
