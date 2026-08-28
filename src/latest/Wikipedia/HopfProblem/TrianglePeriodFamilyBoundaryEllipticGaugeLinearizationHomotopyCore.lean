import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticTailHomology
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryCylinder
import Mathlib.Tactic.Ring

/-!
# Interpolating an exact real elliptic gauge recurrence

The time-linear gauge `t ↦ (t/m)v` satisfies the same forward recurrence
as the original real gauge whenever the original twist vector is fixed.
Their literal convex interpolation is jointly continuous and satisfies
that exact real recurrence at every homotopy time.  No equality modulo
the lattice is substituted for the real recurrence.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticGaugeLinearization

open Elliptic

/-- The time-linear real gauge, with no additional phase constant. -/
def linearGauge (j : Kind) (v : Lattice) : C(ℝ, RealCoordinates) :=
  ⟨fun t => (t / (j.order : ℝ)) • realCast v,
    (continuous_id.div_const (j.order : ℝ)).smul continuous_const⟩

@[simp] theorem linearGauge_apply (j : Kind) (v : Lattice) (t : ℝ) :
    linearGauge j v t = (t / (j.order : ℝ)) • realCast v := rfl

/-- The straight gauge has the required exact real forward recurrence. -/
theorem linearGauge_forward (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (t : ℝ) :
    flatLinear j (linearGauge j v (t + 1)) =
      linearGauge j v t + (1 / (j.order : ℝ)) • realCast v := by
  change flatLinear j (((t + 1) / (j.order : ℝ)) • realCast v) =
    (t / (j.order : ℝ)) • realCast v + (1 / (j.order : ℝ)) • realCast v
  rw [map_smul, flatLinear_realCast, hv, add_div, add_smul]

/-- The actual jointly continuous interpolation of real lifts. -/
def gaugeInterpolation (j : Kind) (v : Lattice) (a : C(ℝ, RealCoordinates)) :
    C(unitInterval × ℝ, RealCoordinates) :=
  ⟨fun p => (1 - (p.1 : ℝ)) • a p.2 + (p.1 : ℝ) • linearGauge j v p.2,
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (a.continuous.comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).smul
        ((linearGauge j v).continuous.comp continuous_snd))⟩

@[simp] theorem gaugeInterpolation_apply (j : Kind) (v : Lattice)
    (a : C(ℝ, RealCoordinates)) (s : unitInterval) (t : ℝ) :
    gaugeInterpolation j v a (s, t) =
      (1 - (s : ℝ)) • a t + (s : ℝ) • ((t / (j.order : ℝ)) • realCast v) := rfl

@[simp] theorem gaugeInterpolation_zero (j : Kind) (v : Lattice)
    (a : C(ℝ, RealCoordinates)) (t : ℝ) : gaugeInterpolation j v a (0, t) = a t := by
  change (1 - (0 : ℝ)) • a t + (0 : ℝ) • linearGauge j v t = a t
  simp

@[simp] theorem gaugeInterpolation_one (j : Kind) (v : Lattice)
    (a : C(ℝ, RealCoordinates)) (t : ℝ) :
    gaugeInterpolation j v a (1, t) = linearGauge j v t := by
  change (1 - (1 : ℝ)) • a t + (1 : ℝ) • linearGauge j v t = linearGauge j v t
  simp

/-- Each interpolation slice is an actual continuous real gauge. -/
def gaugeInterpolationSlice (j : Kind) (v : Lattice) (a : C(ℝ, RealCoordinates))
    (s : unitInterval) : C(ℝ, RealCoordinates) :=
  ⟨fun t => gaugeInterpolation j v a (s, t),
    (gaugeInterpolation j v a).continuous.comp (continuous_const.prodMk continuous_id)⟩

@[simp] theorem gaugeInterpolationSlice_apply (j : Kind) (v : Lattice)
    (a : C(ℝ, RealCoordinates)) (s : unitInterval) (t : ℝ) :
    gaugeInterpolationSlice j v a s t = gaugeInterpolation j v a (s, t) := rfl

/-- Convex interpolation preserves the exact affine recurrence at every real time. -/
theorem gaugeInterpolation_forward (j : Kind) (v : Lattice)
    (hv : j.matrix *ᵥ v = v) (a : C(ℝ, RealCoordinates))
    (ha : ∀ t, flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • realCast v)
    (s : unitInterval) (t : ℝ) :
    flatLinear j (gaugeInterpolationSlice j v a s (t + 1)) =
      gaugeInterpolationSlice j v a s t + (1 / (j.order : ℝ)) • realCast v := by
  change flatLinear j ((1 - (s : ℝ)) • a (t + 1) +
    (s : ℝ) • linearGauge j v (t + 1)) =
    ((1 - (s : ℝ)) • a t + (s : ℝ) • linearGauge j v t) +
      (1 / (j.order : ℝ)) • realCast v
  rw [map_add, map_smul, map_smul, ha, linearGauge_forward j v hv]
  ext i
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticGaugeLinearization
