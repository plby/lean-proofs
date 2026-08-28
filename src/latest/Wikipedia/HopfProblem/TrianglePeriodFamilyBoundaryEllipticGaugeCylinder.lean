import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticNativeCurve
import Wikipedia.HopfProblem.EllipticLogGaugeHolomorphic
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyTranslations

/-!
# The unchanged logarithmic gauge in the native boundary homotopy

The entire original gauge is retained as a jointly continuous function
of real boundary time and fibre point.  A fixed real phase is inserted
in both the actual base homotopy and this same gauge.  At any fixed time
the fibre map is literally a translation, whose effect on actual singular
homology is separately computed.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary

open SpecialPeriods SpecialPeriods.Triangle Elliptic Elliptic.LogGauge
open SpecialPeriods.EllipticFilling SpecialPeriods.Threefold.EllipticGeometry
open SingularMayerVietoris PeriodTorusHigherHomology

/-- Insert a fixed phase in the actual native positive base curve. -/
def nativeShiftedBase (j : Kind) (τ : ℝ) : C(ℝ, TriangleRegularPoint) :=
  (nativePositiveBase j).comp ⟨fun t => t + τ, continuous_id.add continuous_const⟩

@[simp] theorem nativeShiftedBase_apply (j : Kind) (τ t : ℝ) :
    nativeShiftedBase j τ t = nativePositiveBase j (t + τ) := rfl

/-- Insert precisely the same real phase in the actual whole lifted square. -/
def nativeShiftedSquareLift (j : Kind) (τ : ℝ) : C(unitInterval × ℝ, TriangleRegularPoint) :=
  (nativePositiveSquareLift j).comp
    ⟨fun p => (p.1, p.2 + τ), continuous_fst.prodMk (continuous_snd.add continuous_const)⟩

@[simp] theorem nativeShiftedSquareLift_apply (j : Kind) (τ : ℝ)
    (s : unitInterval) (t : ℝ) :
    nativeShiftedSquareLift j τ (s, t) = nativePositiveSquareLift j (s, t + τ) := rfl

@[simp] theorem nativeShiftedSquareLift_zero (j : Kind) (τ t : ℝ) :
    nativeShiftedSquareLift j τ (0, t) = nativeShiftedBase j τ t :=
  nativePositiveSquareLift_zero j (t + τ)

theorem nativeShiftedSquareLift_translate (j : Kind) (τ : ℝ)
    (s : unitInterval) (k : ℤ) (t : ℝ) :
    nativeShiftedSquareLift j τ (s, t + k) =
      (ellipticGenerator j ^ (-k)) • nativeShiftedSquareLift j τ (s, t) := by
  change nativePositiveSquareLift j (s, (t + k) + τ) =
    (ellipticGenerator j ^ (-k)) • nativePositiveSquareLift j (s, t + τ)
  rw [show (t + (k : ℝ)) + τ = (t + τ) + (k : ℝ) by ring]
  exact nativePositiveSquareLift_translate j s k (t + τ)

theorem nativeShiftedBase_translate (j : Kind) (τ : ℝ) (k : ℤ) (t : ℝ) :
    nativeShiftedBase j τ (t + k) =
      (ellipticGenerator j ^ (-k)) • nativeShiftedBase j τ t := by
  simpa only [nativeShiftedSquareLift_zero] using
    nativeShiftedSquareLift_translate j τ 0 k t

/-- The full native family point before the original logarithmic gauge. -/
def nativeGaugeFamilyStar (j : Kind) (τ : ℝ) :
    C(ℝ × RealTorus₄, FamilyStar (specialLocalData j).periods) where
  toFun p := ⟨(nativeClockwiseRoot j (-(p.1 + τ)), p.2),
    nativeClockwiseRoot_ne_zero j (-(p.1 + τ))⟩
  continuous_toFun :=
    (((nativeClockwiseRoot j).continuous.comp
      (continuous_fst.add continuous_const).neg).prodMk continuous_snd).subtype_mk _

/-- The complete continuous fibre-coordinate map of the native logarithmic gauge. -/
def nativeGaugeCylinder (j : Kind) (τ : ℝ) : C(ℝ × RealTorus₄, RealTorus₄) :=
  ⟨fun p => (gaugeMap (specialLocalData j).periods j.twist (nativeGaugeFamilyStar j τ p)).val.2,
    (continuous_snd.comp continuous_subtype_val).comp
      ((gaugeMap_continuous (specialLocalData j).periods j.twist).comp
        (nativeGaugeFamilyStar j τ).continuous)⟩

/-- The real-time translation is retained literally, without replacing
it by a constant or omitting its winding. -/
@[simp] theorem nativeGaugeCylinder_apply (j : Kind) (τ t : ℝ) (x : RealTorus₄) :
    nativeGaugeCylinder j τ (t, x) =
      x + sectionCoordinate (specialLocalData j).periods j.twist
        (nativeClockwiseRoot j (-(t + τ))) := rfl

/-- At a single fixed time the actual fibre map is an actual translation. -/
def nativeGaugeFibre (j : Kind) (τ t : ℝ) : C(RealTorus₄, RealTorus₄) :=
  (nativeGaugeCylinder j τ).comp ⟨fun x => (t, x), continuous_const.prodMk continuous_id⟩

theorem nativeGaugeFibre_eq_translation (j : Kind) (τ t : ℝ) :
    nativeGaugeFibre j τ t =
      rightTranslation (sectionCoordinate (specialLocalData j).periods j.twist
        (nativeClockwiseRoot j (-(t + τ)))) := by
  apply ContinuousMap.ext
  intro x
  rfl

/-- Only this fixed-time fibre map is removed on homology; the full
time-dependent boundary gauge remains part of the actual homotopy. -/
theorem nativeGaugeFibre_homology (j : Kind) (τ t : ℝ) (n : ℕ) :
    singularHomologyMap (nativeGaugeFibre j τ t) n = LinearMap.id := by
  rw [nativeGaugeFibre_eq_translation, rightTranslation_singularHomologyMap]

/-- The actual phased final base edge still retains the original tail frame. -/
theorem nativeShiftedSquareLift_final (j : Kind) (τ t : ℝ) :
    nativeShiftedSquareLift j τ (1, t) =
      nativeTailFrame j • clockwisePeriodicLift (attachingMeridianIndex j) (-(t + τ)) :=
  nativePositiveSquareLift_final j (t + τ)

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary
