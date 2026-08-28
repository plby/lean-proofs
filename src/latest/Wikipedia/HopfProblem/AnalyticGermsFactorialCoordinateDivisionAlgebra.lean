import Wikipedia.HopfProblem.AnalyticGermsFactorialOneVariable
import Wikipedia.HopfProblem.AnalyticGermsFactorialCoordinateDivision
import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The coordinate quotient of actual two-variable analytic germs

Restriction to the second coordinate axis is a split surjective map of actual
analytic-germ rings. Analytic division by the first coordinate identifies its
kernel with the principal coordinate ideal. The quotient is therefore the
one-variable analytic-germ ring, and the first coordinate is a prime element.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.CuspNormalization.Germs.CoordinateDivision

/-- Actual two-variable analytic germs at the origin. -/
abbrev O₂ := AnalyticGerm (0 : ℂ × ℂ)

/-- Actual one-variable analytic germs at the origin. -/
abbrev O₁ := AnalyticGerm (0 : ℂ)

/-- The actual germ of the first coordinate function. -/
def firstCoordinateGerm : O₂ := ofAnalytic Prod.fst analyticAt_fst

/-- Restriction of actual germs to the axis on which the first coordinate is zero. -/
def axisRestriction : O₂ →+* O₁ :=
  pullbackAt (fun w : ℂ => (0, w)) (analyticAt_const.prod analyticAt_id) rfl

/-- Extension of a one-variable germ by making it independent of the first coordinate. -/
def axisExtension : O₁ →+* O₂ :=
  pullbackAt (Prod.snd : ℂ × ℂ → ℂ) analyticAt_snd rfl

@[simp] theorem axisRestriction_ofAnalytic (f : ℂ × ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    axisRestriction (ofAnalytic f hf) =
      ofAnalytic (fun w : ℂ => f (0, w))
        (hf.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl) := rfl

@[simp] theorem axisExtension_ofAnalytic (f : ℂ → ℂ)
    (hf : AnalyticAt ℂ f 0) :
    axisExtension (ofAnalytic f hf) =
      ofAnalytic (fun p : ℂ × ℂ => f p.2) (hf.comp_of_eq analyticAt_snd rfl) := rfl

@[simp] theorem axisRestriction_axisExtension (φ : O₁) :
    axisRestriction (axisExtension φ) = φ := by
  obtain ⟨f, hf, rfl⟩ := exists_representative φ
  rfl

theorem axisRestriction_surjective : Function.Surjective axisRestriction :=
  fun φ => ⟨axisExtension φ, axisRestriction_axisExtension φ⟩

theorem axisExtension_injective : Function.Injective axisExtension :=
  (show Function.LeftInverse axisRestriction axisExtension from
    axisRestriction_axisExtension).injective

@[simp] theorem eval_axisRestriction (φ : O₂) :
    eval (0 : ℂ) (axisRestriction φ) = eval (0 : ℂ × ℂ) φ :=
  eval_pullbackAt _ _ _ φ

@[simp] theorem eval_axisExtension (φ : O₁) :
    eval (0 : ℂ × ℂ) (axisExtension φ) = eval (0 : ℂ) φ :=
  eval_pullbackAt _ _ _ φ

@[simp] theorem axisRestriction_constant (c : ℂ) :
    axisRestriction (constant (0 : ℂ × ℂ) c) = constant (0 : ℂ) c := rfl

@[simp] theorem axisExtension_constant (c : ℂ) :
    axisExtension (constant (0 : ℂ) c) = constant (0 : ℂ × ℂ) c := rfl

@[simp] theorem eval_firstCoordinateGerm :
    eval (0 : ℂ × ℂ) firstCoordinateGerm = 0 := rfl

@[simp] theorem axisRestriction_firstCoordinateGerm :
    axisRestriction firstCoordinateGerm = 0 := rfl

theorem firstCoordinateGerm_ne_zero : firstCoordinateGerm ≠ 0 := by
  intro h
  have hp := congrArg
    (pullbackAt (fun z : ℂ => (z, 0)) (analyticAt_id.prod analyticAt_const) rfl) h
  have he :
      pullbackAt (fun z : ℂ => (z, 0)) (analyticAt_id.prod analyticAt_const) rfl
        firstCoordinateGerm = centeredCoordinateGerm 0 := by
    apply ext
    apply Filter.Germ.coe_eq.mpr
    exact Filter.Eventually.of_forall fun z => (sub_zero z).symm
  rw [he, map_zero] at hp
  exact centeredCoordinateGerm_ne_zero 0 hp

theorem firstCoordinateGerm_not_isUnit : ¬ IsUnit firstCoordinateGerm := by
  simp only [isUnit_iff_eval_ne_zero, eval_firstCoordinateGerm, ne_eq, not_true_eq_false,
    not_false_eq_true]

/-- Vanishing on the axis is precisely divisibility by the first coordinate. -/
theorem axisRestriction_eq_zero_iff_dvd (φ : O₂) :
    axisRestriction φ = 0 ↔ firstCoordinateGerm ∣ φ := by
  constructor
  · obtain ⟨f, hf, rfl⟩ := exists_representative φ
    intro hzero
    have hz : (fun w : ℂ => f (0, w)) =ᶠ[𝓝 (0 : ℂ)] 0 :=
      (ofAnalytic_eq_zero_iff _
        (hf.comp_of_eq (analyticAt_const.prod analyticAt_id) rfl)).mp hzero
    obtain ⟨g, hg, hfg⟩ := exists_analytic_mul_fst hf hz
    refine ⟨ofAnalytic g hg, ?_⟩
    change ofAnalytic f hf = ofAnalytic (fun p : ℂ × ℂ => p.1 * g p)
      (analyticAt_fst.mul hg)
    exact (ofAnalytic_eq_iff _ _ _ _).mpr hfg
  · rintro ⟨ψ, rfl⟩
    simp

/-- Analytic coordinate division identifies the actual restriction kernel. -/
theorem ker_axisRestriction_eq_span :
    RingHom.ker axisRestriction = Ideal.span {firstCoordinateGerm} := by
  ext φ
  rw [RingHom.mem_ker, Ideal.mem_span_singleton]
  exact axisRestriction_eq_zero_iff_dvd φ

/-- The actual coordinate quotient is the actual one-variable germ ring. -/
def quotientFirstCoordinateEquiv :
    O₂ ⧸ Ideal.span {firstCoordinateGerm} ≃+* O₁ :=
  (Ideal.quotEquivOfEq ker_axisRestriction_eq_span.symm).trans
    (RingHom.quotientKerEquivOfRightInverse axisRestriction_axisExtension)

@[simp] theorem quotientFirstCoordinateEquiv_mk (φ : O₂) :
    quotientFirstCoordinateEquiv
      (Ideal.Quotient.mk (Ideal.span {firstCoordinateGerm}) φ) = axisRestriction φ := by
  simp [quotientFirstCoordinateEquiv]

@[simp] theorem quotientFirstCoordinateEquiv_symm (φ : O₁) :
    quotientFirstCoordinateEquiv.symm φ =
      Ideal.Quotient.mk (Ideal.span {firstCoordinateGerm}) (axisExtension φ) := by
  apply quotientFirstCoordinateEquiv.injective
  simp

/-- The first coordinate generates a prime ideal in the actual germ ring. -/
theorem span_firstCoordinateGerm_isPrime :
    (Ideal.span {firstCoordinateGerm}).IsPrime := by
  rw [← ker_axisRestriction_eq_span]
  exact RingHom.ker_isPrime axisRestriction

/-- The first coordinate is a prime element of the actual two-variable germ ring. -/
theorem firstCoordinateGerm_prime : Prime firstCoordinateGerm :=
  (Ideal.span_singleton_prime firstCoordinateGerm_ne_zero).mp
    span_firstCoordinateGerm_isPrime

/-- In particular, the first coordinate is irreducible. -/
theorem firstCoordinateGerm_irreducible : Irreducible firstCoordinateGerm :=
  firstCoordinateGerm_prime.irreducible

/-- The coordinate quotient is a principal ideal ring. -/
theorem quotientFirstCoordinate_isPrincipalIdealRing :
    IsPrincipalIdealRing (O₂ ⧸ Ideal.span {firstCoordinateGerm}) :=
  IsPrincipalIdealRing.of_surjective quotientFirstCoordinateEquiv.symm
    quotientFirstCoordinateEquiv.symm.surjective

end Wikipedia.HopfProblem.CuspNormalization.Germs.CoordinateDivision
