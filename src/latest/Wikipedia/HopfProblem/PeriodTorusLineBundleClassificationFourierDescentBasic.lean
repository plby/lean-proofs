import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDerivativeBasic

/-!
# Actual descent of smooth integer-periodic functions

An integer-periodic smooth function on real coordinate space descends to the
actual product of additive circles. Independence of representatives, continuity,
and smoothness of the descended function are proved from the stated properties
of the original function.
-/

noncomputable section

open Function UnitAddTorus
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

variable {d : Type*}

theorem integerPeriodic_eq_of_torusQuotient_eq (u : (d → ℝ) → ℂ)
    (hper : ∀ x : d → ℝ, ∀ k : d → ℤ, u (x + (fun i => (k i : ℝ))) = u x)
    (x y : d → ℝ) (hxy : torusQuotient x = torusQuotient y) : u x = u y := by
  classical
  have hzero (i : d) : ((x i - y i : ℝ) : UnitAddCircle) = 0 := by
    change (x i : UnitAddCircle) - (y i : UnitAddCircle) = 0
    rw [show (x i : UnitAddCircle) = (y i : UnitAddCircle) from congrFun hxy i, sub_self]
  have hex (i : d) : ∃ n : ℤ, (n : ℝ) = x i - y i := by
    simpa only [zsmul_eq_mul, mul_one] using
      ((AddCircle.coe_eq_zero_iff (1 : ℝ)).mp (hzero i))
  choose k hk using hex
  have hx : x = y + (fun i => (k i : ℝ)) := by
    funext i
    dsimp only [Pi.add_apply]
    linarith [hk i]
  rw [hx, hper]

/-- A representative-based function, proved below to be the genuine descent
whenever the original function is integer-periodic. -/
def torusPeriodicDescendValue (u : (d → ℝ) → ℂ) (t : UnitAddTorus d) : ℂ :=
  u (surjInv torusQuotient_surjective t)

theorem torusPeriodicDescendValue_lift (u : (d → ℝ) → ℂ)
    (hper : ∀ x : d → ℝ, ∀ k : d → ℤ, u (x + (fun i => (k i : ℝ))) = u x)
    (x : d → ℝ) : torusLift (torusPeriodicDescendValue u) x = u x :=
  integerPeriodic_eq_of_torusQuotient_eq u hper _ x
    (surjInv_eq torusQuotient_surjective (torusQuotient x))

variable [Fintype d]

/-- Actual smoothness and periodicity construct, rather than assume, a
smooth function on the actual unit torus. -/
def smoothTorusOfPeriodic (u : (d → ℝ) → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : ∀ x : d → ℝ, ∀ k : d → ℤ, u (x + (fun i => (k i : ℝ))) = u x) :
    SmoothTorusFunction d where
  toContinuousMap :=
    { toFun := torusPeriodicDescendValue u
      continuous_toFun := torusQuotient_isQuotientMap.continuous_iff.mpr (by
        have he : torusPeriodicDescendValue u ∘ torusQuotient = u :=
          funext (torusPeriodicDescendValue_lift u hper)
        rw [he]
        exact hu.continuous) }
  smooth_lift := by
    change ContDiff ℝ ∞ (torusLift (torusPeriodicDescendValue u))
    have he : torusLift (torusPeriodicDescendValue u) = u :=
      funext (torusPeriodicDescendValue_lift u hper)
    rw [he]
    exact hu

@[simp]
theorem smoothTorusOfPeriodic_lift (u : (d → ℝ) → ℂ) (hu : ContDiff ℝ ∞ u)
    (hper : ∀ x : d → ℝ, ∀ k : d → ℤ, u (x + (fun i => (k i : ℝ))) = u x)
    (x : d → ℝ) : torusLift (smoothTorusOfPeriodic u hu hper) x = u x :=
  torusPeriodicDescendValue_lift u hper x

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
