import Wikipedia.HopfProblem.PeriodFamilyHolomorphicFormsPeriodic

/-!
# The scalar coefficient calculation of Lemma 9.15

The hypotheses are the explicit coefficient identities obtained by
pulling back a form under the actual period translations. The period
points supply their genuine full lattices, and the two identity-column
periods have zero derivative. These identities force the one-, two-, and
three-covector coefficients to have the asserted base-only normal forms.
The two-form's vertical coefficient vanishes when the indicated period
derivative is nonzero on a dense subset, as for the actual special tau.
-/

noncomputable section

open Set
open scoped ContDiff Matrix

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicForms

variable {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B]

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

local instance coefficientsProductChartedSpace :
    ChartedSpace (ℂ × ComplexPlane₂) (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (B × ComplexPlane₂))

variable (point : B → PeriodDomain) (d : B → Lattice → ComplexPlane₂)
  (hd₂ : ∀ b, d b (Pi.single 2 1) = 0) (hd₃ : ∀ b, d b (Pi.single 3 1) = 0)

section OneForm

include hd₂ hd₃

/-- The one-form translation identities force both coefficients to
be independent of the fibre, and the remaining covector kills every
actual period derivative. -/
theorem oneForm_coefficients
    {a : B × ComplexPlane₂ → ℂ} {c : B × ComplexPlane₂ → ComplexPlane₂}
    (ha : ContMDiff I₃ I₁ ω a) (hc : ContMDiff I₃ I₂ ω c)
    (hcper : ∀ b ℓ ζ, c (b, ζ + (point b).periodVector ℓ) = c (b, ζ))
    (haper : ∀ b ℓ ζ, a (b, ζ + (point b).periodVector ℓ) +
      dotProduct (c (b, ζ + (point b).periodVector ℓ)) (d b ℓ) = a (b, ζ)) :
    (∀ b ζ, a (b, ζ) = baseCoefficient a b) ∧
      (∀ b ζ, c (b, ζ) = baseCoefficient c b) ∧
      ∀ b ℓ, dotProduct (baseCoefficient c b) (d b ℓ) = 0 := by
  have hcb := fibre_constant_of_periodic point hc hcper
  let q : B → Lattice → ℂ := fun b ℓ => -dotProduct (baseCoefficient c b) (d b ℓ)
  have haq : ∀ b ℓ ζ,
      a (b, ζ + (point b).periodVector ℓ) = a (b, ζ) + q b ℓ := by
    intro b ℓ ζ
    have h := haper b ℓ ζ
    rw [hcb b (ζ + (point b).periodVector ℓ)] at h
    exact (eq_sub_of_add_eq h).trans (sub_eq_add_neg _ _)
  have hq₂ : ∀ b, q b (Pi.single 2 1) = 0 := by
    intro b
    simp only [q, hd₂ b, dotProduct_zero, neg_zero]
  have hq₃ : ∀ b, q b (Pi.single 3 1) = 0 := by
    intro b
    simp only [q, hd₃ b, dotProduct_zero, neg_zero]
  have hab := fibre_constant_of_period_increment_law point ha q haq hq₂ hq₃
  refine ⟨hab, hcb, ?_⟩
  intro b ℓ
  have h := haper b ℓ 0
  rw [hab b (0 + (point b).periodVector ℓ), hcb b (0 + (point b).periodVector ℓ)] at h
  exact add_left_cancel (h.trans ((add_zero (a (b, 0))).symm))

/-- The one-form coefficients in the normal form are actual
holomorphic functions on the original base. -/
theorem oneForm_normal_form_of_period_laws
    {a : B × ComplexPlane₂ → ℂ} {c : B × ComplexPlane₂ → ComplexPlane₂}
    (ha : ContMDiff I₃ I₁ ω a) (hc : ContMDiff I₃ I₂ ω c)
    (hcper : ∀ b ℓ ζ, c (b, ζ + (point b).periodVector ℓ) = c (b, ζ))
    (haper : ∀ b ℓ ζ, a (b, ζ + (point b).periodVector ℓ) +
      dotProduct (c (b, ζ + (point b).periodVector ℓ)) (d b ℓ) = a (b, ζ)) :
    ∃ A : B → ℂ, ∃ C : B → ComplexPlane₂,
      ContMDiff I₁ I₁ ω A ∧ ContMDiff I₁ I₂ ω C ∧
      (∀ b ζ, a (b, ζ) = A b ∧ c (b, ζ) = C b) ∧
      ∀ b ℓ, dotProduct (C b) (d b ℓ) = 0 := by
  obtain ⟨hab, hcb, hd⟩ := oneForm_coefficients point d hd₂ hd₃ ha hc hcper haper
  exact ⟨baseCoefficient a, baseCoefficient c, baseCoefficient_holomorphic ha,
    baseCoefficient_holomorphic hc, fun b ζ => ⟨hab b ζ, hcb b ζ⟩, hd⟩

end OneForm

/-- The covector contributed by the vertical area form under a period shear. -/
def skewPeriod (v : ComplexPlane₂) : ComplexPlane₂ := ![-v 1, v 0]

@[simp] theorem skewPeriod_zero : skewPeriod 0 = 0 := by
  ext i
  fin_cases i <;> simp [skewPeriod]

theorem smul_skewPeriod_eq_zero_iff (a : ℂ) (v : ComplexPlane₂) :
    a • skewPeriod v = 0 ↔ a • v = 0 := by
  constructor
  · intro h
    ext i
    fin_cases i
    · exact congrFun h 1
    · have hh := congrArg Neg.neg (congrFun h 0)
      simpa [skewPeriod, mul_neg] using hh
  · intro h
    ext i
    fin_cases i
    · have hh := congrArg Neg.neg (congrFun h 1)
      simpa [skewPeriod, mul_neg] using hh
    · exact congrFun h 0

section TwoForm

include hd₂ hd₃

/-- The two-form identities force base-only coefficients, and its
vertical coefficient kills all period derivatives. -/
theorem twoForm_coefficients
    {a : B × ComplexPlane₂ → ℂ} {b : B × ComplexPlane₂ → ComplexPlane₂}
    (ha : ContMDiff I₃ I₁ ω a) (hb : ContMDiff I₃ I₂ ω b)
    (haper : ∀ z ℓ ζ, a (z, ζ + (point z).periodVector ℓ) = a (z, ζ))
    (hbper : ∀ z ℓ ζ, b (z, ζ + (point z).periodVector ℓ) +
      a (z, ζ + (point z).periodVector ℓ) • skewPeriod (d z ℓ) = b (z, ζ)) :
    (∀ z ζ, a (z, ζ) = baseCoefficient a z) ∧
      (∀ z ζ, b (z, ζ) = baseCoefficient b z) ∧
      ∀ z ℓ, baseCoefficient a z • d z ℓ = 0 := by
  have hab := fibre_constant_of_periodic point ha haper
  let q : B → Lattice → ComplexPlane₂ :=
    fun z ℓ => -(baseCoefficient a z • skewPeriod (d z ℓ))
  have hbq : ∀ z ℓ ζ,
      b (z, ζ + (point z).periodVector ℓ) = b (z, ζ) + q z ℓ := by
    intro z ℓ ζ
    have h := hbper z ℓ ζ
    rw [hab z (ζ + (point z).periodVector ℓ)] at h
    exact (eq_sub_of_add_eq h).trans (sub_eq_add_neg _ _)
  have hq₂ : ∀ z, q z (Pi.single 2 1) = 0 := by
    intro z
    simp only [q, hd₂ z, skewPeriod_zero, smul_zero, neg_zero]
  have hq₃ : ∀ z, q z (Pi.single 3 1) = 0 := by
    intro z
    simp only [q, hd₃ z, skewPeriod_zero, smul_zero, neg_zero]
  have hbb := fibre_constant_of_period_increment_law point hb q hbq hq₂ hq₃
  refine ⟨hab, hbb, ?_⟩
  intro z ℓ
  apply (smul_skewPeriod_eq_zero_iff _ _).mp
  have h := hbper z ℓ 0
  rw [hbb z (0 + (point z).periodVector ℓ), hab z (0 + (point z).periodVector ℓ)] at h
  exact add_left_cancel (h.trans ((add_zero (b (z, 0))).symm))

/-- Density of the actual noncritical tau derivative kills the
vertical coefficient everywhere, including the critical base points. -/
theorem twoForm_vertical_coefficient_zero
    {a : B × ComplexPlane₂ → ℂ} {b : B × ComplexPlane₂ → ComplexPlane₂}
    (ha : ContMDiff I₃ I₁ ω a) (hb : ContMDiff I₃ I₂ ω b)
    (haper : ∀ z ℓ ζ, a (z, ζ + (point z).periodVector ℓ) = a (z, ζ))
    (hbper : ∀ z ℓ ζ, b (z, ζ + (point z).periodVector ℓ) +
      a (z, ζ + (point z).periodVector ℓ) • skewPeriod (d z ℓ) = b (z, ζ))
    (hDense : Dense {z : B | d z (Pi.single 1 1) 0 ≠ 0}) :
    ∀ z ζ, a (z, ζ) = 0 := by
  obtain ⟨hab, _, hd⟩ := twoForm_coefficients point d hd₂ hd₃ ha hb haper hbper
  have hsub : {z : B | d z (Pi.single 1 1) 0 ≠ 0} ⊆
      {z : B | baseCoefficient a z = 0} := by
    intro z hz
    have h := congrFun (hd z (Pi.single 1 1)) 0
    exact (mul_eq_zero.mp h).resolve_right hz
  have hclosed : IsClosed {z : B | baseCoefficient a z = 0} :=
    isClosed_eq (baseCoefficient_holomorphic ha).continuous continuous_const
  have hall : (univ : Set B) ⊆ {z : B | baseCoefficient a z = 0} := by
    simpa only [hDense.closure_eq, hclosed.closure_eq] using closure_mono hsub
  intro z ζ
  exact (hab z ζ).trans (hall (mem_univ z))

/-- The two-form has only its base-wedge-covector coefficient after
the proved full-lattice and dense noncriticality calculation. -/
theorem twoForm_normal_form_of_period_laws
    {a : B × ComplexPlane₂ → ℂ} {b : B × ComplexPlane₂ → ComplexPlane₂}
    (ha : ContMDiff I₃ I₁ ω a) (hb : ContMDiff I₃ I₂ ω b)
    (haper : ∀ z ℓ ζ, a (z, ζ + (point z).periodVector ℓ) = a (z, ζ))
    (hbper : ∀ z ℓ ζ, b (z, ζ + (point z).periodVector ℓ) +
      a (z, ζ + (point z).periodVector ℓ) • skewPeriod (d z ℓ) = b (z, ζ))
    (hDense : Dense {z : B | d z (Pi.single 1 1) 0 ≠ 0}) :
    ∃ C : B → ComplexPlane₂, ContMDiff I₁ I₂ ω C ∧
      ∀ z ζ, a (z, ζ) = 0 ∧ b (z, ζ) = C z := by
  have ha0 := twoForm_vertical_coefficient_zero point d hd₂ hd₃ ha hb haper hbper hDense
  have hb0 := (twoForm_coefficients point d hd₂ hd₃ ha hb haper hbper).2.1
  exact ⟨baseCoefficient b, baseCoefficient_holomorphic hb,
    fun z ζ => ⟨ha0 z ζ, hb0 z ζ⟩⟩

end TwoForm

/-- The top-form coefficient is an actual holomorphic function of the base alone. -/
theorem threeForm_normal_form_of_period_laws {c : B × ComplexPlane₂ → ℂ}
    (hc : ContMDiff I₃ I₁ ω c)
    (hcper : ∀ b ℓ ζ, c (b, ζ + (point b).periodVector ℓ) = c (b, ζ)) :
    ∃ C : B → ℂ, ContMDiff I₁ I₁ ω C ∧ ∀ b ζ, c (b, ζ) = C b :=
  ⟨baseCoefficient c, baseCoefficient_holomorphic hc,
    fibre_constant_of_periodic point hc hcper⟩

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicForms
