import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransportRadial

/-!
# Actual local parallel transport for arbitrary native torus line bundles

The constructed smooth connection on the native universal-cover pullback has
explicit nonzero scalar transport. Its chart-change law and smooth dependence
on radial endpoints over a fixed chart segment are proved. No global frame,
global logarithm, or existence theorem for an ODE is assumed.
-/

noncomputable section

open Bundle Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport

open PeriodTorusLineBundleClassificationTopological

local notation "Iℂ" => modelWithCornersSelf ℂ ComplexPlane₂

variable (p : PeriodDomain) (V : p.Torus → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V] [ContMDiffVectorBundle ω ℂ V Iℂ]

/-- Explicit scalar transport of the constructed connection in an actual
native pullback ball chart. -/
def pullbackTransport (i : ComplexPlane₂) (γ : ℝ → ComplexPlane₂) (a b : ℝ) : ℂ :=
  connectionTransport (pullbackBallData p V) i γ a b

theorem pullbackTransport_ne_zero (i : ComplexPlane₂) (γ : ℝ → ComplexPlane₂)
    (a b : ℝ) : pullbackTransport p V i γ a b ≠ 0 :=
  connectionTransport_ne_zero (pullbackBallData p V) i γ a b

@[simp] theorem pullbackTransport_self (i : ComplexPlane₂) (γ : ℝ → ComplexPlane₂)
    (a : ℝ) : pullbackTransport p V i γ a a = 1 :=
  connectionTransport_self (pullbackBallData p V) i γ a

theorem pullbackTransport_reverse (i : ComplexPlane₂) (γ : ℝ → ComplexPlane₂)
    (a b : ℝ) : pullbackTransport p V i γ b a = (pullbackTransport p V i γ a b)⁻¹ :=
  connectionTransport_reverse (pullbackBallData p V) i γ a b

theorem pullbackTransport_comp (i : ComplexPlane₂) (γ : ℝ → ComplexPlane₂)
    (hγ : ContDiff ℝ ∞ γ) (a b c : ℝ)
    (hab : MapsTo γ (uIcc a b) ((pullbackBallData p V).baseSet i))
    (hbc : MapsTo γ (uIcc b c) ((pullbackBallData p V).baseSet i)) :
    pullbackTransport p V i γ a c =
      pullbackTransport p V i γ b c * pullbackTransport p V i γ a b :=
  connectionTransport_comp (pullbackBallData p V) i γ hγ a b c hab hbc

/-- Coordinate covariance follows from the actual connection transformation
law and the real fundamental theorem of calculus. -/
theorem pullbackTransport_chart_change (i j : ComplexPlane₂) (γ : ℝ → ComplexPlane₂)
    (hγ : ContDiff ℝ ∞ γ) {a b : ℝ}
    (hchart : MapsTo γ (uIcc a b)
      ((pullbackBallData p V).baseSet i ∩ (pullbackBallData p V).baseSet j)) :
    pullbackTransport p V j γ a b =
      ((pullbackBallData p V).transition i j (γ b) : ℂ) *
        pullbackTransport p V i γ a b *
          ((pullbackBallData p V).transition i j (γ a) : ℂ)⁻¹ :=
  connectionTransport_chart_change (pullbackBallData p V) i j γ hγ hchart

/-- The endpoint-dependent scalar transport along the radial curve. -/
def pullbackRadialTransport (i : ComplexPlane₂) (a b : ℝ) (x : ComplexPlane₂) : ℂ :=
  radialTransport (pullbackBallData p V) i a b x

theorem pullbackRadialTransport_ne_zero (i : ComplexPlane₂) (a b : ℝ)
    (x : ComplexPlane₂) : pullbackRadialTransport p V i a b x ≠ 0 :=
  connectionTransport_ne_zero (pullbackBallData p V) i (radialCurve x) a b

/-- Actual smooth dependence in a neighborhood of a radial endpoint, when
the fixed compact segment lies in the designated native pullback chart. -/
theorem pullbackRadialTransport_contDiffAt (i : ComplexPlane₂) (a b : ℝ)
    (x₀ : ComplexPlane₂)
    (hchart : MapsTo (radialCurve x₀) (uIcc a b) ((pullbackBallData p V).baseSet i)) :
    ContDiffAt ℝ ∞ (pullbackRadialTransport p V i a b) x₀ :=
  radialTransport_contDiffAt (pullbackBallData p V) i a b x₀ hchart

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationTransport
