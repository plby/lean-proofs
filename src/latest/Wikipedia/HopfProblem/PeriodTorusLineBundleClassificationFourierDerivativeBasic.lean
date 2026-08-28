import Mathlib.Analysis.Fourier.AddCircleMulti
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Actual smooth functions and directional derivatives on the unit torus

Smoothness is a property of the real lift of a continuous function on the
actual product of additive circles.  The Fréchet derivative is constant on
the fibres of the quotient map, hence descends to a smooth torus function.
-/

noncomputable section

open Function Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

variable {d : Type*}

/-- The actual coordinatewise quotient by the integer lattice. -/
def torusQuotient (x : d → ℝ) : UnitAddTorus d := fun i => (x i : UnitAddCircle)

@[simp] theorem torusQuotient_add (x y : d → ℝ) :
    torusQuotient (x + y) = torusQuotient x + torusQuotient y := by
  funext i
  rfl

@[simp] theorem torusQuotient_sub (x y : d → ℝ) :
    torusQuotient (x - y) = torusQuotient x - torusQuotient y := by
  funext i
  rfl

@[simp] theorem torusQuotient_zero : torusQuotient (0 : d → ℝ) = 0 := by
  funext i
  rfl

theorem torusQuotient_surjective : Surjective (torusQuotient (d := d)) :=
  Surjective.piMap fun _ => QuotientAddGroup.mk_surjective

theorem torusQuotient_isQuotientMap : IsQuotientMap (torusQuotient (d := d)) :=
  (IsOpenQuotientMap.piMap
    (fun _ : d => (QuotientAddGroup.isOpenQuotientMap_mk :
      IsOpenQuotientMap (fun x : ℝ => (x : UnitAddCircle))))).isQuotientMap

theorem torusQuotient_continuous : Continuous (torusQuotient (d := d)) :=
  torusQuotient_isQuotientMap.continuous

/-- The real lift through the actual quotient projection. -/
def torusLift (f : UnitAddTorus d → ℂ) : (d → ℝ) → ℂ := f ∘ torusQuotient

variable [Fintype d]

/-- A continuous torus function whose actual real lift is smooth. -/
structure SmoothTorusFunction (d : Type*) [Fintype d] where
  toContinuousMap : C(UnitAddTorus d, ℂ)
  smooth_lift : ContDiff ℝ ∞ (torusLift toContinuousMap)

instance : CoeFun (SmoothTorusFunction d) (fun _ => UnitAddTorus d → ℂ) :=
  ⟨fun f => f.toContinuousMap⟩

/-- Derivatives of a lifted torus function are independent of the real lift. -/
theorem torusLift_fderiv_eq (f : UnitAddTorus d → ℂ) (x y : d → ℝ)
    (hxy : torusQuotient x = torusQuotient y) :
    fderiv ℝ (torusLift f) x = fderiv ℝ (torusLift f) y := by
  have hshift : (fun z => torusLift f (z + (y - x))) = torusLift f := by
    funext z
    dsimp only [torusLift, Function.comp_apply]
    rw [torusQuotient_add, torusQuotient_sub, hxy, sub_self, add_zero]
  calc
    fderiv ℝ (torusLift f) x = fderiv ℝ (fun z => torusLift f (z + (y - x))) x := by
      rw [hshift]
    _ = fderiv ℝ (torusLift f) (x + (y - x)) := fderiv_comp_add_right (y - x)
    _ = fderiv ℝ (torusLift f) y := by
      congr 1
      abel

/-- The descended value of the actual real directional derivative. -/
def torusDerivativeValue (f : SmoothTorusFunction d) (v : d → ℝ) (t : UnitAddTorus d) : ℂ :=
  fderiv ℝ (torusLift f) (surjInv torusQuotient_surjective t) v

@[simp] theorem torusDerivativeValue_lift (f : SmoothTorusFunction d) (v x : d → ℝ) :
    torusDerivativeValue f v (torusQuotient x) = fderiv ℝ (torusLift f) x v := by
  unfold torusDerivativeValue
  rw [torusLift_fderiv_eq f _ x (surjInv_eq torusQuotient_surjective (torusQuotient x))]

theorem torusDerivativeValue_contDiff_lift (f : SmoothTorusFunction d) (v : d → ℝ) :
    ContDiff ℝ ∞ (torusLift (torusDerivativeValue f v)) := by
  have he : torusLift (torusDerivativeValue f v) =
      (fun x => fderiv ℝ (torusLift f) x v) := funext (torusDerivativeValue_lift f v)
  rw [he]
  exact (contDiff_infty_iff_fderiv.mp f.smooth_lift).2.clm_apply contDiff_const

theorem torusDerivativeValue_continuous (f : SmoothTorusFunction d) (v : d → ℝ) :
    Continuous (torusDerivativeValue f v) :=
  torusQuotient_isQuotientMap.continuous_iff.mpr
    (torusDerivativeValue_contDiff_lift f v).continuous

/-- Directional differentiation preserves actual smooth torus functions. -/
def torusDirectionalDerivative (f : SmoothTorusFunction d) (v : d → ℝ) :
    SmoothTorusFunction d where
  toContinuousMap := ⟨torusDerivativeValue f v, torusDerivativeValue_continuous f v⟩
  smooth_lift := torusDerivativeValue_contDiff_lift f v

@[simp] theorem torusDirectionalDerivative_lift (f : SmoothTorusFunction d) (v x : d → ℝ) :
    torusLift (torusDirectionalDerivative f v) x = fderiv ℝ (torusLift f) x v :=
  torusDerivativeValue_lift f v x

/-- Differentiating actual translations on the torus gives the descended
Fréchet derivative, at every real parameter and every torus point. -/
theorem hasDerivAt_torus_translate (f : SmoothTorusFunction d) (v : d → ℝ)
    (t : UnitAddTorus d) (s : ℝ) :
    HasDerivAt (fun r : ℝ => f (t + torusQuotient (r • v)))
      (torusDirectionalDerivative f v (t + torusQuotient (s • v))) s := by
  obtain ⟨x, rfl⟩ := torusQuotient_surjective t
  simp only [← torusQuotient_add]
  change HasDerivAt (fun r : ℝ => torusLift f (x + r • v))
    (torusLift (torusDirectionalDerivative f v) (x + s • v)) s
  rw [torusDirectionalDerivative_lift]
  have hp : HasDerivAt (fun r : ℝ => x + r • v) v s := by
    simpa using ((hasDerivAt_id s).smul_const v).const_add x
  have hd := ((contDiff_infty_iff_fderiv.mp f.smooth_lift).1 (x + s • v)).hasFDerivAt
  exact hd.comp_hasDerivAt s hp

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
