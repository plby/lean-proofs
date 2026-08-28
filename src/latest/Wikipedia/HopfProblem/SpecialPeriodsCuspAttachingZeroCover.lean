import Wikipedia.HopfProblem.CuspSection
import Wikipedia.HopfProblem.SpecialPeriodsCuspFamilyQuotient

/-!
# The zero-vector logarithmic cover is the actual cusp zero section

In the reference toric chart, exponentiating the zero fibre vector gives
the section coordinates `(t,1,1)`.  The resulting identities concern the
literal toric and period quotient maps, for arbitrary correction matrices.
-/

noncomputable section

open Set Topology
open scoped Matrix

namespace Wikipedia.HopfProblem.CuspUniformization

open ToricCharts ToricFan ToricSpace CuspQuotient
open SpecialPeriods.CuspFamily

/-- The toric exponential at the zero fibre vector is the reference-chart
section.  The coordinate identity also holds at the central parameter. -/
@[simp] theorem exponentialPoint_zero (t : ℂ) :
    exponentialPoint t 0 = inclusion referenceTriangle (sectionCoordinates t) := by
  change inclusion referenceTriangle
      (monomial referenceTriangle.dual (exponentialCoordinates t 0)) = _
  apply congrArg (inclusion referenceTriangle)
  ext i
  fin_cases i <;>
    simp [monomial, referenceTriangle, Triangle.dual, exponentialCoordinates,
      sectionCoordinates, Fin.prod_univ_succ]

/-- Equality already holds in the toric tube before taking the cusp quotient. -/
theorem totalExponentialLift_eq_sectionLift_of_zero (r : ℝ) (x : LogCover r)
    (hx : x.1.2 = 0) (t : disc r) (ht : (t : ℂ) = exponential x.1.1) :
    totalExponentialLift r x = sectionLift r t := by
  apply Subtype.ext
  change exponentialPoint (exponential x.1.1) x.1.2 =
    inclusion referenceTriangle (sectionCoordinates t)
  rw [hx, exponentialPoint_zero, ← ht]

/-- The zero-vector cover formula in the whole cusp quotient. -/
theorem totalCuspCover_eq_zeroSection_of_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (x : LogCover r)
    (hx : x.1.2 = 0) (t : disc r) (ht : (t : ℂ) = exponential x.1.1) :
    totalCuspCover C r x = zeroSection C r t :=
  congrArg (quotientMap C r) (totalExponentialLift_eq_sectionLift_of_zero r x hx t ht)

/-- The punctured logarithmic cover sends every zero fibre vector to the
extended zero section, with no regularity assumption on the correction. -/
theorem puncturedCuspCover_eq_zeroSection_of_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (x : LogCover r)
    (hx : x.1.2 = 0) (t : disc r) (ht : (t : ℂ) = exponential x.1.1) :
    (puncturedCuspCover C r x : QuotientSpace C r) = zeroSection C r t :=
  totalCuspCover_eq_zeroSection_of_zero C r x hx t ht

/-- A logarithmic-base formulation with a separately supplied disc point
avoids any dependence on a chosen proof of disc membership. -/
theorem puncturedCuspCover_zero
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (s : LogBase r)
    (t : disc r) (ht : (t : ℂ) = exponential s) :
    (puncturedCuspCover C r ⟨((s : ℂ), 0), s.property⟩ : QuotientSpace C r) =
      zeroSection C r t :=
  puncturedCuspCover_eq_zeroSection_of_zero C r _ rfl t ht

end Wikipedia.HopfProblem.CuspUniformization

namespace Wikipedia.HopfProblem.SpecialPeriods.CuspFamily.Data

open CuspUniformization

/-- The genuine period-family quotient sends the zero vector to the zero
of the real-coordinate torus over the same logarithm. -/
@[simp] theorem familyCover_zero (D : CuspFamily.Data) (s : LogBase D.radius) :
    D.familyCover ⟨((s : ℂ), 0), s.property⟩ = (s, 0) := by
  simp only [familyCover_apply, HolomorphicPeriodMap.quotientMap, map_zero]

/-- The iterated lattice and monodromy quotient has the same zero-vector
representative. -/
@[simp] theorem iteratedCover_zero (D : CuspFamily.Data) (s : LogBase D.radius) :
    D.iteratedCover ⟨((s : ℂ), 0), s.property⟩ = D.quotient (s, 0) := by
  change D.quotient (D.familyCover _) = _
  rw [D.familyCover_zero]

end Wikipedia.HopfProblem.SpecialPeriods.CuspFamily.Data
