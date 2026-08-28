import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryEllipticGaugeLinearizationHomotopyDeck
import Wikipedia.HopfProblem.TrianglePeriodFamilyBoundaryLiftedHomotopy

/-!
# A genuine homotopy from the original real gauge to the time-linear gauge

The exact real recurrence makes every interpolation slice equivariant for
all integer mapping-torus deck transformations.  Coupling the interpolation
to the given actual upstairs base lift and then using the open quotient
topology yields a jointly continuous homotopy of the entire boundary map.
The original translation is retained throughout the construction.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticGaugeLinearization

open Elliptic MappingTorus SpecialPeriods SpecialPeriods.Triangle
open SingularMayerVietoris PeriodTorusHigherHomology

attribute [local instance] triangleTorusAction triangleTorusAction_continuous

variable (D : Data ℂ TriangleRegularPoint) (j : Kind) (v : Lattice)

/-- The actual family cylinder, including the full original real gauge. -/
def gaugeCylinderMap (L : C(ℝ, TriangleRegularPoint)) (a : C(ℝ, RealCoordinates)) :
    C(ℝ × RealTorus₄, D.Space) :=
  familyCylinderMap D L (gaugeFibreCylinder a)

@[simp] theorem gaugeCylinderMap_apply (L : C(ℝ, TriangleRegularPoint))
    (a : C(ℝ, RealCoordinates)) (t : ℝ) (x : RealTorus₄) :
    gaugeCylinderMap D L a (t, x) = D.quotient (L t, x + standardLattice.mkQ (a t)) := rfl

/-- The two exact deck relations make the original family map invariant. -/
theorem gaugeCylinderMap_deck (a : C(ℝ, RealCoordinates))
    (ha : ∀ t, flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • realCast v)
    (L : C(ℝ, TriangleRegularPoint))
    (hL : ∀ (k : ℤ) t, L (t + k) = (ellipticGenerator j ^ (-k)) • L t)
    (k : ℤ) (p : ℝ × RealTorus₄) :
    gaugeCylinderMap D L a (deck (flatTorusAffine j v) k p) = gaugeCylinderMap D L a p :=
  familyCylinderMap_deck D (flatTorusAffine j v) L (gaugeFibreCylinder a)
    (ellipticGenerator j) hL (gaugeFibreCylinder_deck j v a ha) k p

/-- The map descended from the exact specified cylinder representatives. -/
def gaugeBoundaryMap (a : C(ℝ, RealCoordinates))
    (ha : ∀ t, flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • realCast v)
    (L : C(ℝ, TriangleRegularPoint))
    (hL : ∀ (k : ℤ) t, L (t + k) = (ellipticGenerator j ^ (-k)) • L t) :
    C(Torus (flatTorusAffine j v), D.Space) :=
  Cylinder.descend (flatTorusAffine j v) (gaugeCylinderMap D L a)
    (gaugeCylinderMap_deck D j v a ha L hL)

/-- The descended endpoint map has its literal original representative formula. -/
@[simp] theorem gaugeBoundaryMap_mk (a : C(ℝ, RealCoordinates))
    (ha : ∀ t, flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • realCast v)
    (L : C(ℝ, TriangleRegularPoint))
    (hL : ∀ (k : ℤ) t, L (t + k) = (ellipticGenerator j ^ (-k)) • L t)
    (t : ℝ) (x : RealTorus₄) :
    gaugeBoundaryMap D j v a ha L hL (mk (flatTorusAffine j v) (t, x)) =
      D.quotient (L t, x + standardLattice.mkQ (a t)) := rfl

/-- Joint interpolation on the actual family cylinder, with the base lift fixed. -/
def gaugeCylinderHomotopy (a : C(ℝ, RealCoordinates)) (L : C(ℝ, TriangleRegularPoint)) :
    (gaugeCylinderMap D L a).Homotopy (gaugeCylinderMap D L (linearGauge j v)) where
  toFun p := D.quotient (L p.2.1,
    p.2.2 + standardLattice.mkQ (gaugeInterpolation j v a (p.1, p.2.1)))
  continuous_toFun := D.quotient_continuous.comp
    ((L.continuous.comp (continuous_fst.comp continuous_snd)).prodMk
      ((continuous_snd.comp continuous_snd).add
        (standardLattice.continuous_mkQ.comp ((gaugeInterpolation j v a).continuous.comp
          (continuous_fst.prodMk (continuous_fst.comp continuous_snd))))))
  map_zero_left p := by
    change D.quotient (L p.1, p.2 + standardLattice.mkQ (gaugeInterpolation j v a (0, p.1))) =
      D.quotient (L p.1, p.2 + standardLattice.mkQ (a p.1))
    rw [gaugeInterpolation_zero]
  map_one_left p := by
    change D.quotient (L p.1, p.2 + standardLattice.mkQ (gaugeInterpolation j v a (1, p.1))) =
      D.quotient (L p.1, p.2 + standardLattice.mkQ (linearGauge j v p.1))
    rw [gaugeInterpolation_one]

/-- Full integer invariance holds at every time of the joint interpolation. -/
theorem gaugeCylinderHomotopy_deck (hv : j.matrix *ᵥ v = v)
    (a : C(ℝ, RealCoordinates))
    (ha : ∀ t, flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • realCast v)
    (L : C(ℝ, TriangleRegularPoint))
    (hL : ∀ (k : ℤ) t, L (t + k) = (ellipticGenerator j ^ (-k)) • L t)
    (s : unitInterval) (k : ℤ) (p : ℝ × RealTorus₄) :
    gaugeCylinderHomotopy D j v a L (s, deck (flatTorusAffine j v) k p) =
      gaugeCylinderHomotopy D j v a L (s, p) :=
  familyCylinderMap_deck D (flatTorusAffine j v) L
    (gaugeFibreCylinder (gaugeInterpolationSlice j v a s)) (ellipticGenerator j) hL
      (interpolatedGaugeFibreCylinder_deck j v hv a ha s) k p

/-- The entire original boundary map is genuinely homotopic to the time-linear gauge map. -/
def gaugeLinearizationHomotopy (hv : j.matrix *ᵥ v = v)
    (a : C(ℝ, RealCoordinates))
    (ha : ∀ t, flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • realCast v)
    (L : C(ℝ, TriangleRegularPoint))
    (hL : ∀ (k : ℤ) t, L (t + k) = (ellipticGenerator j ^ (-k)) • L t) :
    (gaugeBoundaryMap D j v a ha L hL).Homotopy
      (gaugeBoundaryMap D j v (linearGauge j v) (linearGauge_forward j v hv) L hL) :=
  Cylinder.descendHomotopy (flatTorusAffine j v)
    (gaugeCylinderMap D L a) (gaugeCylinderMap D L (linearGauge j v))
    (gaugeCylinderMap_deck D j v a ha L hL)
    (gaugeCylinderMap_deck D j v (linearGauge j v) (linearGauge_forward j v hv) L hL)
    (gaugeCylinderHomotopy D j v a L) (gaugeCylinderHomotopy_deck D j v hv a ha L hL)

/-- The whole descended homotopy keeps the literal interpolated translation. -/
@[simp] theorem gaugeLinearizationHomotopy_mk (hv : j.matrix *ᵥ v = v)
    (a : C(ℝ, RealCoordinates))
    (ha : ∀ t, flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • realCast v)
    (L : C(ℝ, TriangleRegularPoint))
    (hL : ∀ (k : ℤ) t, L (t + k) = (ellipticGenerator j ^ (-k)) • L t)
    (s : unitInterval) (t : ℝ) (x : RealTorus₄) :
    gaugeLinearizationHomotopy D j v hv a ha L hL (s, mk (flatTorusAffine j v) (t, x)) =
      D.quotient (L t, x + standardLattice.mkQ
        ((1 - (s : ℝ)) • a t + (s : ℝ) • ((t / (j.order : ℝ)) • realCast v))) := rfl

/-- The comparison preserves the actual singular homology map in every degree. -/
theorem gaugeLinearization_homology (hv : j.matrix *ᵥ v = v)
    (a : C(ℝ, RealCoordinates))
    (ha : ∀ t, flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • realCast v)
    (L : C(ℝ, TriangleRegularPoint))
    (hL : ∀ (k : ℤ) t, L (t + k) = (ellipticGenerator j ^ (-k)) • L t) (n : ℕ) :
    singularHomologyMap (gaugeBoundaryMap D j v a ha L hL) n =
      singularHomologyMap
        (gaugeBoundaryMap D j v (linearGauge j v) (linearGauge_forward j v hv) L hL) n :=
  homotopy_homologyMap (gaugeLinearizationHomotopy D j v hv a ha L hL) n

/-- Exact cylinder representatives identify an already constructed original map
with the descended gauge map, without any additional homotopy assumption. -/
theorem gaugeBoundaryMap_eq_of_mk (a : C(ℝ, RealCoordinates))
    (ha : ∀ t, flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • realCast v)
    (L : C(ℝ, TriangleRegularPoint))
    (hL : ∀ (k : ℤ) t, L (t + k) = (ellipticGenerator j ^ (-k)) • L t)
    (F : C(Torus (flatTorusAffine j v), D.Space))
    (hF : ∀ t x, F (mk (flatTorusAffine j v) (t, x)) =
      D.quotient (L t, x + standardLattice.mkQ (a t))) :
    F = gaugeBoundaryMap D j v a ha L hL := by
  apply ContinuousMap.ext
  intro q
  obtain ⟨⟨t, x⟩, rfl⟩ := mk_surjective (flatTorusAffine j v) q
  exact hF t x

/-- The genuine homotopy starts at any original map with the proved representatives. -/
def gaugeLinearizationHomotopyOfMk (hv : j.matrix *ᵥ v = v)
    (a : C(ℝ, RealCoordinates))
    (ha : ∀ t, flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • realCast v)
    (L : C(ℝ, TriangleRegularPoint))
    (hL : ∀ (k : ℤ) t, L (t + k) = (ellipticGenerator j ^ (-k)) • L t)
    (F : C(Torus (flatTorusAffine j v), D.Space))
    (hF : ∀ t x, F (mk (flatTorusAffine j v) (t, x)) =
      D.quotient (L t, x + standardLattice.mkQ (a t))) :
    F.Homotopy
      (gaugeBoundaryMap D j v (linearGauge j v) (linearGauge_forward j v hv) L hL) :=
  (gaugeLinearizationHomotopy D j v hv a ha L hL).cast
    (gaugeBoundaryMap_eq_of_mk D j v a ha L hL F hF).symm rfl

/-- The original representative map and the time-linear gauge induce the same maps on all Hn. -/
theorem gaugeLinearization_homology_of_mk (hv : j.matrix *ᵥ v = v)
    (a : C(ℝ, RealCoordinates))
    (ha : ∀ t, flatLinear j (a (t + 1)) = a t + (1 / (j.order : ℝ)) • realCast v)
    (L : C(ℝ, TriangleRegularPoint))
    (hL : ∀ (k : ℤ) t, L (t + k) = (ellipticGenerator j ^ (-k)) • L t)
    (F : C(Torus (flatTorusAffine j v), D.Space))
    (hF : ∀ t x, F (mk (flatTorusAffine j v) (t, x)) =
      D.quotient (L t, x + standardLattice.mkQ (a t))) (n : ℕ) :
    singularHomologyMap F n = singularHomologyMap
      (gaugeBoundaryMap D j v (linearGauge j v) (linearGauge_forward j v hv) L hL) n :=
  homotopy_homologyMap (gaugeLinearizationHomotopyOfMk D j v hv a ha L hL F hF) n

end Wikipedia.HopfProblem.TrianglePeriodFamily.Boundary.EllipticGaugeLinearization
