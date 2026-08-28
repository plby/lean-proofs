import Wikipedia.HopfProblem.CuspComplementFinitePresentation
import Wikipedia.HopfProblem.ToricTwistVolume

/-!
# Explicit original chart transitions in the finite cusp presentation

The finite identifications are written as the original lattice shift,
the original correction-dependent exponential multiplier, and the native
toric chart change with its actual source condition.  The finite deleted
sets retain the literal strict normal-radius inequality.  Neither the
phase factors nor the central overlap conditions are discarded.
-/

noncomputable section

open Set Topology

namespace Wikipedia.HopfProblem.CuspComplement

open CuspCircleNormalTrivialization SpecialPeriods SpecialPeriods.Threefold
open ToricCharts ToricFan Triangle

local notation "CD" => CuspGeometry.data

/-- The triangle reached by the original lattice shift. -/
def shiftedTriangle (v : Fin 2 → ℤ) (i : Coordinates.Index) : Triangle :=
  (Coordinates.triangle i).shift (ToricSpace.cuspVector v)

/-- The original parameter-dependent phase and modulus multiplier in that chart. -/
def shiftedCoordinates (v : Fin 2 → ℤ) (p : FiniteCoordinates) : CoordinateSpace 3 :=
  ToricSpace.scale (shiftedTriangle v p.1)
    (ToricSpace.fibreMultiplier
      (ToricSpace.exponentialMultiplier (CD).correction v (Triangle.time p.2))) p.2

/-- The actual deck map on each finite representative, with no frozen correction substituted. -/
theorem translate_coordinateLift_coe (v : Fin 2 → ℤ) (p : FiniteCoordinates) :
    (ToricSpace.tubeTranslate (CD).correction (CuspQuotient.disc (CD).radius) v
      (coordinateLift p) : ToricSpace.Space) =
      ToricSpace.inclusion (shiftedTriangle v p.1) (shiftedCoordinates v p) :=
  ToricSpace.twistedTranslate_chart_formula (Coordinates.triangle p.1) (CD).correction v p.2

/-- The source condition is the original toric overlap, including along the central strata. -/
theorem translate_coordinateLift_eq_iff (v : Fin 2 → ℤ) (p q : FiniteCoordinates) :
    ToricSpace.tubeTranslate (CD).correction (CuspQuotient.disc (CD).radius) v
        (coordinateLift q) = coordinateLift p ↔
      shiftedCoordinates v q ∈
          (chartChange (shiftedTriangle v q.1) (Coordinates.triangle p.1)).source ∧
        chartChange (shiftedTriangle v q.1) (Coordinates.triangle p.1)
          (shiftedCoordinates v q) = (p.2 : CoordinateSpace 3) := by
  rw [Subtype.ext_iff, translate_coordinateLift_coe]
  exact ToricSpace.inclusion_eq_iff (shiftedTriangle v q.1) (Coordinates.triangle p.1)
    (shiftedCoordinates v q) p.2

/-- The entire finite quotient relation is given by these finitely many exact native overlaps. -/
theorem finiteModel_mk_eq_iff_chart (p q : carvedCoordinates) :
    Quotient.mk coordinateRelation p = Quotient.mk coordinateRelation q ↔
      ∃ v ∈ finiteKCollision capRadius,
        shiftedCoordinates v q.val ∈
            (chartChange (shiftedTriangle v q.val.1) (Coordinates.triangle p.val.1)).source ∧
          chartChange (shiftedTriangle v q.val.1) (Coordinates.triangle p.val.1)
            (shiftedCoordinates v q.val) = (p.val.2 : CoordinateSpace 3) := by
  rw [finiteModel_mk_eq_iff]
  simp_rw [translate_coordinateLift_eq_iff]

/-- The deleted part in a finite chart has the literal strict normal-radius
condition and only the finite collection of original deck translates. -/
theorem coordinateLift_mem_deletedLift_iff_normal (p : FiniteCoordinates) :
    coordinateLift p ∈ deletedLift ↔
      ∃ v ∈ finiteRelevantDeck capRadius, ∃ n : ClosedNormalProduct,
        radiusSq n.2.val < closedRadius ^ 2 ∧
          ToricSpace.twistedTranslate (CD).correction v (fromProduct (n.1, n.2.val)) =
            ToricSpace.inclusion (Coordinates.triangle p.1) (p.2 : CoordinateSpace 3) := by
  change coordinateLift p ∈
    (⋃ v ∈ finiteRelevantDeck capRadius,
      ToricSpace.tubeTranslate (CD).correction (CuspQuotient.disc (CD).radius) v ''
        openNormalLifts) ↔ _
  rw [mem_iUnion₂]
  constructor
  · rintro ⟨v, hv, y, ⟨n, hn, rfl⟩, hy⟩
    exact ⟨v, hv, n, hn, congrArg (fun x : NativeTube => (x : ToricSpace.Space)) hy⟩
  · rintro ⟨v, hv, n, hn, h⟩
    exact ⟨v, hv, closedNormalLift n, ⟨n, hn, rfl⟩, Subtype.ext h⟩

end Wikipedia.HopfProblem.CuspComplement
