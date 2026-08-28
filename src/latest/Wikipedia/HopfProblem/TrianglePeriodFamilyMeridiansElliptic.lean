import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientEllipticCharts
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientRegularChartsTopology
import Wikipedia.HopfProblem.TrianglePeriodFamilyMeridiansEllipticDisc
import Mathlib.Topology.Path

/-!
# Explicit elliptic meridian lifts in the actual regular locus

The normalized Cayley coordinate on the chosen precisely invariant elliptic
neighbourhood gives actual regular upper-half-plane points away from zero.
Fractional counterclockwise turns in this coordinate lift full
counterclockwise circles in the genuine full quotient chart.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians

open SpecialPeriods SpecialPeriods.Triangle

attribute [local instance] triangleGeometricAction

/-- Inverting the actual elliptic chart has the prescribed normalized
Cayley coordinate. -/
theorem ellipticChart_symm_normalizedCayley (j : Elliptic.Kind) (u : Disc) :
    normalizedCayley (ellipticCenter j) (ellipticNeighborhoodRadius j)
      ((ellipticNeighborhoodChart j).symm u : ℍ) = (u : ℂ) := by
  change (ellipticNeighborhoodChart j ((ellipticNeighborhoodChart j).symm u) : ℂ) = _
  exact congrArg (fun w : Disc => (w : ℂ))
    ((ellipticNeighborhoodChart j).apply_symm_apply u)

/-- The genuine quotient coordinate is the indicated power of the
uniformizing disc coordinate. -/
theorem ellipticChart_symm_fullChart (j : Elliptic.Kind) (u : Disc) :
    ellipticFullChart j
      (triangleOrbitProjection ((ellipticNeighborhoodChart j).symm u : ℍ)) =
        (u : ℂ) ^ j.order := by
  rw [ellipticFullChart_projection]
  change (normalizedCayley (ellipticCenter j) (ellipticNeighborhoodRadius j)
    ((ellipticNeighborhoodChart j).symm u : ℍ)) ^ j.order = _
  rw [ellipticChart_symm_normalizedCayley]

theorem ellipticChart_symm_projection_mem_source (j : Elliptic.Kind) (u : Disc) :
    triangleOrbitProjection ((ellipticNeighborhoodChart j).symm u : ℍ) ∈
      (ellipticFullChart j).source := by
  rw [ellipticFullChart_source]
  exact ⟨(ellipticNeighborhoodChart j).symm u,
    ((ellipticNeighborhoodChart j).symm u).property, rfl⟩

/-- A nonzero point of the genuine local disc gives a point of the actual
free-action locus.  The local quotient excludes its own centre, and precise
neighbourhood choice excludes the other elliptic orbit. -/
theorem ellipticChart_symm_mem_regular (j : Elliptic.Kind) (u : Disc)
    (hu : (u : ℂ) ≠ 0) :
    ((ellipticNeighborhoodChart j).symm u : ℍ) ∈ triangleRegularLocus := by
  have hown : triangleOrbitProjection ((ellipticNeighborhoodChart j).symm u : ℍ) ≠
      ellipticOrbitCenter j := by
    intro h
    have hz := (ellipticFullChart_eq_zero_iff j
      (ellipticChart_symm_projection_mem_source j u)).mpr h
    rw [ellipticChart_symm_fullChart] at hz
    exact (pow_ne_zero j.order hu) hz
  have hother := ellipticNeighborhood_avoids_other j
    ((ellipticNeighborhoodChart j).symm u : ℍ)
    ((ellipticNeighborhoodChart j).symm u).property
  apply (triangleOrbitProjection_mem_regularDomain_iff _).mp
  apply (triangleOrbitRegularDomain_mem_iff _).mpr
  cases j
  · exact ⟨hown, hother⟩
  · exact ⟨hother, hown⟩

/-- The actual regular point supplied by a nonzero uniformizing disc
coordinate, not a new abstract local model. -/
def ellipticRegularPoint (j : Elliptic.Kind) (u : Disc) (hu : (u : ℂ) ≠ 0) :
    TriangleRegularPoint :=
  ⟨(ellipticNeighborhoodChart j).symm u, ellipticChart_symm_mem_regular j u hu⟩

@[simp] theorem ellipticRegularPoint_val (j : Elliptic.Kind) (u : Disc)
    (hu : (u : ℂ) ≠ 0) :
    (ellipticRegularPoint j u hu : ℍ) =
      ((ellipticNeighborhoodChart j).symm u : ℍ) := rfl

/-- The inverse local rotation is the inverse actual triangle generator
on the corresponding regular points. -/
theorem ellipticRegularPoint_inverse_generator (j : Elliptic.Kind)
    (u v : Disc) (hu : (u : ℂ) ≠ 0) (hv : (v : ℂ) ≠ 0)
    (hvu : v = (Elliptic.familyRotation j).symm u) :
    ellipticRegularPoint j v hv =
      (ellipticGenerator j)⁻¹ • ellipticRegularPoint j u hu := by
  let := ellipticNeighborhoodAction j
  have hN : ellipticStabilizerGenerator j • (ellipticNeighborhoodChart j).symm v =
      (ellipticNeighborhoodChart j).symm u := by
    apply (ellipticNeighborhoodChart j).injective
    change ellipticNeighborhoodChart j
      (ellipticStabilizerGenerator j • (ellipticNeighborhoodChart j).symm v) =
        ellipticNeighborhoodChart j ((ellipticNeighborhoodChart j).symm u)
    rw [ellipticNeighborhoodChart_generator,
      (ellipticNeighborhoodChart j).apply_symm_apply, hvu,
      (Elliptic.familyRotation j).apply_symm_apply,
      (ellipticNeighborhoodChart j).apply_symm_apply]
  apply eq_inv_smul_iff.mpr
  apply Subtype.ext
  exact congrArg (fun z : ellipticNeighborhood j => (z : ℍ)) hN

/-- A positive real normalized Cayley coordinate chooses an actual
regular base point near the indicated elliptic centre. -/
def ellipticBasePoint (j : Elliptic.Kind) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    TriangleRegularPoint :=
  ellipticRegularPoint j (ellipticDiscBase r hr hr1) (ellipticDiscBase_ne_zero r hr hr1)

/-- The literal inverse Cayley image of a fractional positive turn. -/
def ellipticLiftPoint (j : Elliptic.Kind) (r : ℝ) (hr : 0 < r) (hr1 : r < 1)
    (t : unitInterval) : TriangleRegularPoint :=
  ellipticRegularPoint j (ellipticDiscTurn j r hr hr1 t)
    (ellipticDiscTurn_ne_zero j r hr hr1 t)

theorem ellipticLiftPoint_continuous (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) : Continuous (ellipticLiftPoint j r hr hr1) :=
  (continuous_subtype_val.comp ((ellipticNeighborhoodChart j).symm.continuous.comp
    (ellipticDiscTurn_continuous j r hr hr1))).subtype_mk _

@[simp] theorem ellipticLiftPoint_zero (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    ellipticLiftPoint j r hr hr1 0 = ellipticBasePoint j r hr hr1 := by
  apply Subtype.ext
  change ((ellipticNeighborhoodChart j).symm (ellipticDiscTurn j r hr hr1 0) : ℍ) =
    ((ellipticNeighborhoodChart j).symm (ellipticDiscBase r hr hr1) : ℍ)
  rw [ellipticDiscTurn_zero]

/-- The endpoint is proved from the exact local rotation of the actual
generator.  It is not supplied as monodromy data. -/
@[simp] theorem ellipticLiftPoint_one (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    ellipticLiftPoint j r hr hr1 1 =
      (ellipticGenerator j)⁻¹ • ellipticBasePoint j r hr hr1 :=
  ellipticRegularPoint_inverse_generator j _ _ _ _ (ellipticDiscTurn_one j r hr hr1)

/-- An actual small counterclockwise elliptic meridian lift in the free
upper-half-plane locus, ending in the inverse generator sheet. -/
def ellipticCCWLift (j : Elliptic.Kind) (r : ℝ) (hr : 0 < r) (hr1 : r < 1) :
    Path (ellipticBasePoint j r hr hr1)
      ((ellipticGenerator j)⁻¹ • ellipticBasePoint j r hr hr1) where
  toFun := ellipticLiftPoint j r hr hr1
  continuous_toFun := ellipticLiftPoint_continuous j r hr hr1
  source' := ellipticLiftPoint_zero j r hr hr1
  target' := ellipticLiftPoint_one j r hr hr1

@[simp] theorem ellipticCCWLift_apply (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (t : unitInterval) :
    ellipticCCWLift j r hr hr1 t = ellipticLiftPoint j r hr hr1 t := rfl

theorem ellipticBasePoint_normalizedCayley (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) :
    normalizedCayley (ellipticCenter j) (ellipticNeighborhoodRadius j)
      (ellipticBasePoint j r hr hr1 : ℍ) = (r : ℂ) :=
  ellipticChart_symm_normalizedCayley j (ellipticDiscBase r hr hr1)

/-- The lift has exactly the prescribed fractional-turn coordinate. -/
theorem ellipticCCWLift_normalizedCayley (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (t : unitInterval) :
    normalizedCayley (ellipticCenter j) (ellipticNeighborhoodRadius j)
      (ellipticCCWLift j r hr hr1 t : ℍ) =
        (r : ℂ) * turn ((t : ℝ) / j.order) :=
  ellipticChart_symm_normalizedCayley j (ellipticDiscTurn j r hr hr1 t)

theorem ellipticCCWLift_normalizedCayley_exp (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (t : unitInterval) :
    normalizedCayley (ellipticCenter j) (ellipticNeighborhoodRadius j)
      (ellipticCCWLift j r hr hr1 t : ℍ) = (r : ℂ) *
        Complex.exp (2 * Real.pi * Complex.I * (t : ℝ) / (j.order : ℂ)) := by
  rw [ellipticCCWLift_normalizedCayley, turn]
  simp only [Complex.ofReal_div, Complex.ofReal_natCast, mul_div_assoc]

/-- The whole projected path remains in the actual elliptic quotient chart. -/
theorem ellipticCCWLift_projection_mem_source (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (t : unitInterval) :
    triangleOrbitProjection (ellipticCCWLift j r hr hr1 t : ℍ) ∈
      (ellipticFullChart j).source :=
  ellipticChart_symm_projection_mem_source j (ellipticDiscTurn j r hr hr1 t)

/-- The actual full quotient coordinate traces precisely one positive
circle, of radius `r ^ j.order`. -/
theorem ellipticCCWLift_fullChart (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (t : unitInterval) :
    ellipticFullChart j (triangleOrbitProjection (ellipticCCWLift j r hr hr1 t : ℍ)) =
      (r : ℂ) ^ j.order * turn (t : ℝ) :=
  (ellipticChart_symm_fullChart j (ellipticDiscTurn j r hr hr1 t)).trans
    (ellipticDiscTurn_pow j r hr hr1 t)

theorem ellipticCCWLift_fullChart_exp (j : Elliptic.Kind) (r : ℝ)
    (hr : 0 < r) (hr1 : r < 1) (t : unitInterval) :
    ellipticFullChart j (triangleOrbitProjection (ellipticCCWLift j r hr hr1 t : ℍ)) =
      (r : ℂ) ^ j.order * Complex.exp (2 * Real.pi * Complex.I * (t : ℝ)) :=
  ellipticCCWLift_fullChart j r hr hr1 t

end Wikipedia.HopfProblem.TrianglePeriodFamily.Meridians
