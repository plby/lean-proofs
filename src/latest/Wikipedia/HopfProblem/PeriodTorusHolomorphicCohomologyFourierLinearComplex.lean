import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyFourierLinearOperations
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyFourierTopSolver
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# The actual global Fourier Dolbeault complex as a linear complex

All terms are actual smooth functions on the marked real quotient torus.
The maps are the genuine native-coordinate Dolbeault derivatives. The
constant representatives and Haar means are literal maps on those functions.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierLinear

open PeriodTorusLineBundleClassification

/-- Actual smooth functions on the four-real-dimensional quotient torus. -/
abbrev Smooth := SmoothTorusFunction (Fin 4)

/-- Actual smooth coefficient pairs, in the fixed complex-coordinate order. -/
abbrev Pair := Fin 2 → Smooth

/-- The literal first Dolbeault differential. -/
def differential (p : PeriodDomain) : Smooth →ₗ[ℂ] Pair :=
  LinearMap.pi (dbarLinear p)

@[simp] theorem differential_apply (p : PeriodDomain) (f : Smooth) (i : Fin 2) :
    differential p f i = torusDbar p f i := rfl

/-- The literal top Dolbeault differential, with its geometric sign. -/
def top (p : PeriodDomain) : Pair →ₗ[ℂ] Smooth :=
  (dbarLinear p 0).comp (LinearMap.proj 1) -
    (dbarLinear p 1).comp (LinearMap.proj 0)

@[simp] theorem top_apply (p : PeriodDomain) (a : Pair) :
    top p a = FourierTop.topDifferential p a := rfl

/-- Actual differentiation, not just the corresponding symbols, squares to zero. -/
theorem top_differential (p : PeriodDomain) : (top p).comp (differential p) = 0 := by
  apply LinearMap.ext
  intro f
  apply smooth_ext
  exact FourierTop.topDifferential_torusDbar p f

/-- The genuine complex of actual smooth coefficients, retaining complex linearity. -/
def complex (p : PeriodDomain) : ShortComplex (ModuleCat ℂ) :=
  ShortComplex.moduleCatMk (differential p) (top p) (top_differential p)

/-- Componentwise integration for the actual probability Haar measure. -/
def pairMean : Pair →ₗ[ℂ] (Fin 2 → ℂ) :=
  LinearMap.pi fun i => meanLinear.comp (LinearMap.proj i)

@[simp] theorem pairMean_apply (a : Pair) (i : Fin 2) :
    pairMean a i = torusFourierMean (a i) := rfl

/-- The actual constant coefficient pair representing a constant antiholomorphic form. -/
def constantPair : (Fin 2 → ℂ) →ₗ[ℂ] Pair :=
  LinearMap.pi fun i => constantLinear.comp (LinearMap.proj i)

@[simp] theorem constantPair_apply (c : Fin 2 → ℂ) (i : Fin 2) :
    constantPair c i = constantLinear (c i) := rfl

@[simp] theorem pairMean_constantPair (c : Fin 2 → ℂ) : pairMean (constantPair c) = c := by
  funext i
  exact mean_constant (c i)

@[simp] theorem pairMean_differential (p : PeriodDomain) (f : Smooth) :
    pairMean (differential p f) = 0 := by
  funext i
  exact mean_dbar p i f

@[simp] theorem mean_top (p : PeriodDomain) (a : Pair) : meanLinear (top p a) = 0 :=
  FourierTop.topDifferential_mean p a

@[simp] theorem top_constantPair (p : PeriodDomain) (c : Fin 2 → ℂ) :
    top p (constantPair c) = 0 := by
  change dbarLinear p 0 (constantLinear (c 1)) -
    dbarLinear p 1 (constantLinear (c 0)) = 0
  rw [dbar_constant, dbar_constant, sub_self]

/-- Literal closedness is exactly the kernel condition of the actual top differential. -/
theorem top_eq_zero_iff (p : PeriodDomain) (a : Pair) :
    top p a = 0 ↔ TorusDbarClosed p a := by
  constructor
  · intro h t
    exact sub_eq_zero.mp (congrArg (fun f : Smooth => f t) h)
  · intro h
    apply smooth_ext
    intro t
    exact sub_eq_zero.mpr (h t)

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierLinear
