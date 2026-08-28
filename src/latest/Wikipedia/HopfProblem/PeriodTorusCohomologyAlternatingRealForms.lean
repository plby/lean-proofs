import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingCoordinates
import Wikipedia.HopfProblem.PeriodTorusCohomologyAlternatingEta
import Wikipedia.HopfProblem.PeriodTorusTypeOneOneIntrinsic

/-!
# Native second cohomology and integral alternating period forms

Every genuine integral singular cohomology class determines a real
alternating form on the actual covering tangent space. Its values on
integer periods are exactly the evaluations of that class on products
of positive period loops. Conversely, every real alternating form
integral on the actual lattice comes from a unique native class.

This is a comparison by period evaluations. No de Rham, Hodge,
Néron--Severi, or Chern-class identification is asserted.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusCohomology

open FirstHurewicz SingularMayerVietoris SingularCohomologyFree
open PeriodTorusHigherHomologyPontryagin PeriodTorusTypeOneOne
open SpecialPeriods UpperHalfPlane

/-- The real tangent form recovered from a genuine native cohomology class. -/
def cohomologyRealForm (p : PeriodDomain) (a : SingularCohomology p.Torus 2) : RealForm :=
  tangentForm p ((coefficientClassEquiv p).symm a)

@[simp] theorem cohomologyRealForm_coefficientClass (p : PeriodDomain) (E : Fin 6 → ℤ) :
    cohomologyRealForm p (coefficientClass p E) = tangentForm p E := by
  simp only [cohomologyRealForm, coefficientClass, LinearEquiv.symm_apply_apply]

/-- The associated form is genuinely alternating on the covering tangent space. -/
theorem cohomologyRealForm_self (p : PeriodDomain) (a : SingularCohomology p.Torus 2)
    (x : ComplexPlane₂) : cohomologyRealForm p a x x = 0 :=
  tangentForm_self p _ x

theorem cohomologyRealForm_swap (p : PeriodDomain) (a : SingularCohomology p.Torus 2)
    (x y : ComplexPlane₂) : cohomologyRealForm p a x y = -cohomologyRealForm p a y x :=
  tangentForm_swap p _ x y

/-- Integrality concerns the actual lattice, not only the chosen basis. -/
theorem cohomologyRealForm_integral (p : PeriodDomain) (a : SingularCohomology p.Torus 2) :
    IntegralOnPeriodLattice p (cohomologyRealForm p a) :=
  tangentForm_integral p _

/-- Exact evaluation on every ordered product of genuine positive period loops. -/
theorem cohomologyRealForm_real_periods (p : PeriodDomain)
    (a : SingularCohomology p.Torus 2) (x y : Lattice) :
    (singularEvaluation p.Torus 2 a
      (product11 p.Torus (loopHomologyClass (p.periodLoop x))
        (loopHomologyClass (p.periodLoop y))) : ℝ) =
      cohomologyRealForm p a (periodEquiv p (fun i => (x i : ℝ)))
        (periodEquiv p (fun i => (y i : ℝ))) := by
  obtain ⟨E, rfl⟩ := (coefficientClassEquiv p).surjective a
  simpa only [cohomologyRealForm, coefficientClass, LinearEquiv.symm_apply_apply] using
    coefficientClass_real_periods p E x y

/-- The same evaluation equality uses the already defined actual period-vector map. -/
theorem cohomologyRealForm_periodVector (p : PeriodDomain)
    (a : SingularCohomology p.Torus 2) (x y : Lattice) :
    (singularEvaluation p.Torus 2 a
      (product11 p.Torus (loopHomologyClass (p.periodLoop x))
        (loopHomologyClass (p.periodLoop y))) : ℝ) =
      cohomologyRealForm p a (p.periodVector x) (p.periodVector y) := by
  simpa only [periodEquiv_integer_eq_periodVector] using
    cohomologyRealForm_real_periods p a x y

/-- The associated real form loses no information about the native integral class. -/
theorem cohomologyRealForm_injective (p : PeriodDomain) :
    Function.Injective (cohomologyRealForm p) := by
  intro a b h
  exact (coefficientClassEquiv p).symm.injective (tangentForm_injective p h)

@[simp] theorem cohomologyRealForm_zero (p : PeriodDomain) :
    cohomologyRealForm p 0 = 0 := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp [cohomologyRealForm, tangentForm_apply, coordinateForm_apply, coordinateValue]

@[simp] theorem cohomologyRealForm_eq_zero_iff (p : PeriodDomain)
    (a : SingularCohomology p.Torus 2) : cohomologyRealForm p a = 0 ↔ a = 0 := by
  rw [← cohomologyRealForm_zero p, (cohomologyRealForm_injective p).eq_iff]

@[simp] theorem cohomologyRealForm_add (p : PeriodDomain)
    (a b : SingularCohomology p.Torus 2) :
    cohomologyRealForm p (a + b) = cohomologyRealForm p a + cohomologyRealForm p b := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  simp only [cohomologyRealForm, map_add, tangentForm_apply, coordinateForm_apply,
    coordinateValue, Pi.add_apply, Int.cast_add, LinearMap.add_apply]
  ring

/-- Integer scaling of the native class scales its actual real tangent form. -/
theorem cohomologyRealForm_zsmul (p : PeriodDomain) (n : ℤ)
    (a : SingularCohomology p.Torus 2) :
    cohomologyRealForm p (n • a) = (n : ℝ) • cohomologyRealForm p a := by
  unfold cohomologyRealForm
  rw [map_zsmul, tangentForm_zsmul]

/-- Existence and uniqueness require only actual alternation and lattice-integrality. -/
theorem existsUnique_cohomologyRealForm_of_integral (p : PeriodDomain) (B : RealForm)
    (hAlt : ∀ x, B x x = 0) (hIntegral : IntegralOnPeriodLattice p B) :
    ∃! a : SingularCohomology p.Torus 2, cohomologyRealForm p a = B := by
  obtain ⟨E, hE, _⟩ := existsUnique_tangentForm_of_integral p B hAlt hIntegral
  refine ⟨coefficientClass p E, ?_, ?_⟩
  · simpa only [cohomologyRealForm_coefficientClass] using hE
  · intro a ha
    apply cohomologyRealForm_injective p
    simpa only [cohomologyRealForm_coefficientClass] using ha.trans hE.symm

theorem existsUnique_cohomologyRealForm_iff (p : PeriodDomain) (B : RealForm) :
    (∃! a : SingularCohomology p.Torus 2, cohomologyRealForm p a = B) ↔
      (∀ x, B x x = 0) ∧ IntegralOnPeriodLattice p B := by
  constructor
  · rintro ⟨a, rfl, _⟩
    exact ⟨cohomologyRealForm_self p a, cohomologyRealForm_integral p a⟩
  · rintro ⟨hAlt, hIntegral⟩
    exact existsUnique_cohomologyRealForm_of_integral p B hAlt hIntegral

/-- All actual real forms having the two intrinsic period-form properties. -/
abbrev IntegralAlternatingRealForm (p : PeriodDomain) :=
  {B : RealForm // (∀ x, B x x = 0) ∧ IntegralOnPeriodLattice p B}

/-- The canonical comparison, with codomain restricted to actual integral alternating forms. -/
def cohomologyIntegralAlternatingForm (p : PeriodDomain)
    (a : SingularCohomology p.Torus 2) : IntegralAlternatingRealForm p :=
  ⟨cohomologyRealForm p a, cohomologyRealForm_self p a, cohomologyRealForm_integral p a⟩

@[simp] theorem cohomologyIntegralAlternatingForm_coe (p : PeriodDomain)
    (a : SingularCohomology p.Torus 2) :
    (cohomologyIntegralAlternatingForm p a : RealForm) = cohomologyRealForm p a := rfl

theorem cohomologyIntegralAlternatingForm_bijective (p : PeriodDomain) :
    Function.Bijective (cohomologyIntegralAlternatingForm p) := by
  constructor
  · intro a b h
    exact cohomologyRealForm_injective p (congrArg Subtype.val h)
  · intro B
    obtain ⟨a, ha, _⟩ := existsUnique_cohomologyRealForm_of_integral p B.val B.property.1
      B.property.2
    exact ⟨a, Subtype.ext ha⟩

/-- A genuine bijection with all intrinsic integral alternating real tangent forms. -/
def cohomologyIntegralAlternatingEquiv (p : PeriodDomain) :
    SingularCohomology p.Torus 2 ≃ IntegralAlternatingRealForm p :=
  Equiv.ofBijective _ (cohomologyIntegralAlternatingForm_bijective p)

@[simp] theorem cohomologyIntegralAlternatingEquiv_coe (p : PeriodDomain)
    (a : SingularCohomology p.Torus 2) :
    (cohomologyIntegralAlternatingEquiv p a : RealForm) = cohomologyRealForm p a := rfl

@[simp] theorem cohomologyIntegralAlternatingEquiv_symm_form (p : PeriodDomain)
    (B : IntegralAlternatingRealForm p) :
    cohomologyRealForm p ((cohomologyIntegralAlternatingEquiv p).symm B) = B.val :=
  congrArg Subtype.val ((cohomologyIntegralAlternatingEquiv p).apply_symm_apply B)

/-- The inverse comparison is characterized directly by evaluations on actual period cycles. -/
theorem existsUnique_cohomologyClass_real_periods (p : PeriodDomain) (B : RealForm)
    (hAlt : ∀ x, B x x = 0) (hIntegral : IntegralOnPeriodLattice p B) :
    ∃! a : SingularCohomology p.Torus 2, ∀ x y : Lattice,
      (singularEvaluation p.Torus 2 a
        (product11 p.Torus (loopHomologyClass (p.periodLoop x))
          (loopHomologyClass (p.periodLoop y))) : ℝ) =
        B (p.periodVector x) (p.periodVector y) := by
  obtain ⟨a, ha, _⟩ := existsUnique_cohomologyRealForm_of_integral p B hAlt hIntegral
  have he (x y : Lattice) :
      (singularEvaluation p.Torus 2 a
        (product11 p.Torus (loopHomologyClass (p.periodLoop x))
          (loopHomologyClass (p.periodLoop y))) : ℝ) =
        B (p.periodVector x) (p.periodVector y) := by
    rw [cohomologyRealForm_periodVector, ha]
  refine ⟨a, he, ?_⟩
  intro b hb
  apply cohomology_ext_periodLoops p
  intro x y
  exact_mod_cast (hb x y).trans (he x y).symm

@[simp] theorem cohomologyRealForm_etaClass (p : PeriodDomain) :
    cohomologyRealForm p (etaClass p) = etaTangent p :=
  cohomologyRealForm_coefficientClass p periodRelationEta

/-- Outside the proved countable exceptional set, the associated form is of type `(1,1)`
exactly for native integer multiples of the positively normalized distinguished class. -/
theorem cohomologyRealForm_typeOneOne_iff_of_not_exceptional (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet)
    (a : SingularCohomology (specialPeriodMap.point z).Torus 2) :
    IsTypeOneOne (cohomologyRealForm (specialPeriodMap.point z) a) ↔
      ∃ n : ℤ, a = n • etaClass (specialPeriodMap.point z) := by
  have h (n : ℤ) :
      cohomologyRealForm (specialPeriodMap.point z) a =
          (n : ℝ) • etaTangent (specialPeriodMap.point z) ↔
        a = n • etaClass (specialPeriodMap.point z) := by
    rw [← cohomologyRealForm_etaClass, ← cohomologyRealForm_zsmul]
    exact (cohomologyRealForm_injective _).eq_iff
  rw [typeOneOne_integral_iff_of_not_exceptional z hz _
    (cohomologyRealForm_self _ _) (cohomologyRealForm_integral _ _)]
  simp_rw [h]

/-- The integer in the native class classification is unique, without a Hodge comparison. -/
theorem cohomologyRealForm_typeOneOne_iff_existsUnique_eta (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet)
    (a : SingularCohomology (specialPeriodMap.point z).Torus 2) :
    IsTypeOneOne (cohomologyRealForm (specialPeriodMap.point z) a) ↔
      ∃! n : ℤ, a = n • etaClass (specialPeriodMap.point z) := by
  have h (n : ℤ) :
      cohomologyRealForm (specialPeriodMap.point z) a =
          (n : ℝ) • etaTangent (specialPeriodMap.point z) ↔
        a = n • etaClass (specialPeriodMap.point z) := by
    rw [← cohomologyRealForm_etaClass, ← cohomologyRealForm_zsmul]
    exact (cohomologyRealForm_injective _).eq_iff
  rw [typeOneOne_integral_iff_existsUnique_etaMultiple z hz _
    (cohomologyRealForm_self _ _) (cohomologyRealForm_integral _ _)]
  simp_rw [h]

end Wikipedia.HopfProblem.PeriodTorusCohomology
