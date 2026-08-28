import Wikipedia.HopfProblem.CuspCoinvariantExtension
import Wikipedia.HopfProblem.CuspCircleOrbitLocalParameter

/-!
# Genuine unit-complex phases of the cusp gamma maps

The already constructed additive-circle maps are composed with the
original period-one exponential into the complex numbers.  The result is
an ambient complex-valued continuous function of norm one, still exactly
invariant under the original delta action.  No manifold structure on the
additive circle is used or introduced.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCoinvariantExtension.Phase

open CuspUniformization CuspRetraction SpecialPeriods.CuspFamily
open ThreefoldHomologyFinitenessCusp SpecialPeriods.Threefold.Homology

/-- The actual normalized exponential, viewed as a continuous complex phase. -/
def circlePhase : C(AddCircle (1 : ℝ), ℂ) :=
  ⟨fun t => (DeltaSweep.circleParameter t : ℂ),
    Units.continuous_val.comp DeltaSweep.circleParameter_continuous⟩

@[simp] theorem circlePhase_real (t : ℝ) :
    circlePhase (t : AddCircle (1 : ℝ)) = exponential (t : ℂ) := rfl

@[simp] theorem circlePhase_norm (t : AddCircle (1 : ℝ)) : ‖circlePhase t‖ = 1 :=
  SpecialPeriods.Threefold.VerticalAction.FixedCoordinates.CircleOrbit.circleParameter_norm t

theorem circlePhase_ne_zero (t : AddCircle (1 : ℝ)) : circlePhase t ≠ 0 :=
  (DeltaSweep.circleParameter t).ne_zero

/-- The original gamma phase on the whole actual punctured cusp. -/
def puncturedPhase (D : Data) :
    C(PuncturedQuotient D.correction D.radius, ℂ) :=
  circlePhase.comp (puncturedGamma D)

/-- Its exact formula in the native logarithmic cover, with the original
varying real-period inverse and original first coordinate. -/
theorem puncturedPhase_cover (D : Data) (p : LogCover D.radius) :
    puncturedPhase D (puncturedCuspCover D.correction D.radius p) =
      exponential ((((D.periods.periodEquiv ⟨p.val.1, p.property⟩).symm p.val.2) 0 : ℝ) : ℂ) := by
  change circlePhase (puncturedGamma D
    (puncturedCuspCover D.correction D.radius p)) = _
  rw [puncturedGamma_cover, circlePhase_real]

theorem puncturedPhase_realCoordinates (D : Data) (s : LogBase D.radius)
    (x : RealPlane₄) :
    puncturedPhase D (puncturedCuspCover D.correction D.radius
      ⟨((s : ℂ), D.periods.periodEquiv s x), s.property⟩) =
        exponential (x 0 : ℂ) := by
  change circlePhase (puncturedGamma D _) = _
  rw [puncturedGamma_realCoordinates, circlePhase_real]

@[simp] theorem puncturedPhase_norm (D : Data)
    (q : PuncturedQuotient D.correction D.radius) : ‖puncturedPhase D q‖ = 1 :=
  circlePhase_norm _

theorem puncturedPhase_realFlow (D : Data) (t : ℝ)
    (q : PuncturedQuotient D.correction D.radius) :
    puncturedPhase D (puncturedFlow D.correction D.radius (t : ℂ) q) =
      puncturedPhase D q := by
  change circlePhase (puncturedGamma D _) = circlePhase (puncturedGamma D q)
  rw [puncturedGamma_realFlow]

/-- The continuous unit phase on the full native cap from any proved
collar-adjusted extension. -/
def capPhase (D : Data) (bound : ℝ) (E : CollarExtension D bound) : C(FullSpace D, ℂ) :=
  circlePhase.comp E.map

@[simp] theorem capPhase_norm (D : Data) (bound : ℝ)
    (E : CollarExtension D bound) (q : FullSpace D) : ‖capPhase D bound E q‖ = 1 :=
  circlePhase_norm _

theorem capPhase_ne_zero (D : Data) (bound : ℝ)
    (E : CollarExtension D bound) (q : FullSpace D) : capPhase D bound E q ≠ 0 :=
  circlePhase_ne_zero _

theorem capPhase_central (D : Data) (bound : ℝ) (E : CollarExtension D bound)
    (q : QuotientCentralFibre D.correction D.radius) :
    capPhase D bound E q.val =
      circlePhase (centralGamma D.correction D.radius D.radius_pos D.holomorphic q) := by
  change circlePhase (E.map q.val) = _
  rw [E.central]

theorem capPhase_realFlow (D : Data) (bound : ℝ) (E : CollarExtension D bound)
    (t : ℝ) (q : FullSpace D) :
    capPhase D bound E
      (SpecialPeriods.Threefold.VerticalAction.Cusp.flow D.correction D.radius (t : ℂ) q) =
        capPhase D bound E q := by
  change circlePhase (E.map _) = circlePhase (E.map q)
  rw [E.realFlow]

theorem capPhase_outer (D : Data) (bound : ℝ) (E : CollarExtension D bound)
    (q : PuncturedQuotient D.correction D.radius)
    (hq : E.innerRadius ≤ parameterNorm D q.val) :
    capPhase D bound E q.val = puncturedPhase D q := by
  change circlePhase (E.map q.val) = circlePhase (puncturedGamma D q)
  rw [E.outer q hq]

/-- The phase on the actual cusp piece in the original glued threefold. -/
def specialCapPhase (bound : ℝ) (hbound : 0 < bound) :
    C(SpecialPeriods.Threefold.SpecialCuspPiece, ℂ) :=
  circlePhase.comp (specialCapGamma bound hbound)

@[simp] theorem specialCapPhase_eq_capPhase (bound : ℝ) (hbound : 0 < bound) :
    specialCapPhase bound hbound =
      capPhase SpecialPeriods.Threefold.CuspAttaching.data bound
        (specialCollarExtension bound hbound) := rfl

@[simp] theorem specialCapPhase_norm (bound : ℝ) (hbound : 0 < bound)
    (q : SpecialPeriods.Threefold.SpecialCuspPiece) :
    ‖specialCapPhase bound hbound q‖ = 1 := circlePhase_norm _

theorem specialCapPhase_realFlow (bound : ℝ) (hbound : 0 < bound)
    (t : ℝ) (q : SpecialPeriods.Threefold.SpecialCuspPiece) :
    specialCapPhase bound hbound
      (SpecialPeriods.Threefold.VerticalAction.Cusp.specialFlow (t : ℂ) q) =
        specialCapPhase bound hbound q :=
  congrArg circlePhase (specialCapGamma_realFlow bound hbound t q)

/-- The global native AddCircle orbits in the actual cusp piece preserve
the ambient complex phase, with the original orbit parameter. -/
theorem specialCapPhase_eq_of_globalCircle_related (bound : ℝ) (hbound : 0 < bound)
    (t : AddCircle (1 : ℝ)) (x y : SpecialPeriods.Threefold.SpecialCuspPiece)
    (h : DeltaSweep.actionMap (t, SpecialPeriods.Threefold.CuspGeometry.inclusion x) =
      SpecialPeriods.Threefold.CuspGeometry.inclusion y) :
    specialCapPhase bound hbound x = specialCapPhase bound hbound y :=
  congrArg circlePhase (specialCapGamma_eq_of_globalCircle_related bound hbound t x y h)

end Wikipedia.HopfProblem.CuspCoinvariantExtension.Phase
