import Wikipedia.HopfProblem.PeriodTori
import Mathlib.Geometry.Manifold.ContMDiff.Constructions
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Holomorphic restrictions in the covering product of a period family

These lemmas use the actual product charted space on `B × ComplexPlane₂`.
Jointly holomorphic coefficient functions restrict to holomorphic functions on
each covering fibre and on the zero section. In particular, a coefficient which
is constant in the fibre direction comes from its holomorphic zero-section
restriction. No manifold compatibility, period relation, or constancy result is
assumed or proved here beyond the hypotheses explicitly displayed.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicForms

variable {B : Type*} [TopologicalSpace B] [ChartedSpace ℂ B]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "I₂" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₃" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)
local notation "IF" => modelWithCornersSelf ℂ F

local instance coveringProductChartedSpace :
    ChartedSpace (ℂ × ComplexPlane₂) (B × ComplexPlane₂) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (B × ComplexPlane₂))

/-- Insertion of the covering fibre over an actual base point. -/
def fibreInsertion (b : B) : ComplexPlane₂ → B × ComplexPlane₂ := fun ζ => (b, ζ)

omit [TopologicalSpace B] [ChartedSpace ℂ B] in
@[simp] theorem fibreInsertion_apply (b : B) (ζ : ComplexPlane₂) :
    fibreInsertion b ζ = (b, ζ) := rfl

/-- The insertion is holomorphic in the unchanged product atlas. -/
theorem fibreInsertion_holomorphic (b : B) :
    ContMDiff I₂ I₃ ω (fibreInsertion b) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_const.prodMk contMDiff_id

/-- Insertion of the zero section in the covering product. -/
def zeroSection : B → B × ComplexPlane₂ := fun b => (b, 0)

omit [TopologicalSpace B] [ChartedSpace ℂ B] in
@[simp] theorem zeroSection_apply (b : B) : zeroSection b = (b, 0) := rfl

/-- The covering-product zero section is holomorphic without extra base assumptions. -/
theorem zeroSection_holomorphic : ContMDiff I₁ I₃ ω (zeroSection (B := B)) := by
  rw [modelWithCornersSelf_prod]
  exact contMDiff_id.prodMk contMDiff_const

/-- Joint holomorphicity restricts to the fixed covering fibre. -/
theorem fibreRestriction_holomorphic {f : B × ComplexPlane₂ → F}
    (hf : ContMDiff I₃ IF ω f) (b : B) :
    ContMDiff I₂ IF ω (fun ζ => f (b, ζ)) :=
  hf.comp (fibreInsertion_holomorphic b)

/-- In the vector-space fibre this is ordinary complex analytic regularity. -/
theorem fibreRestriction_contDiff {f : B × ComplexPlane₂ → F}
    (hf : ContMDiff I₃ IF ω f) (b : B) :
    ContDiff ℂ ω (fun ζ => f (b, ζ)) :=
  (fibreRestriction_holomorphic hf b).contDiff

/-- Joint holomorphicity restricts to the actual zero section. -/
theorem zeroSectionRestriction_holomorphic {f : B × ComplexPlane₂ → F}
    (hf : ContMDiff I₃ IF ω f) :
    ContMDiff I₁ IF ω (fun b => f (b, 0)) :=
  hf.comp zeroSection_holomorphic

/-- The base coefficient obtained by evaluating at the zero section. -/
def baseCoefficient (f : B × ComplexPlane₂ → F) : B → F := fun b => f (b, 0)

omit [TopologicalSpace B] [ChartedSpace ℂ B] [NormedAddCommGroup F] [NormedSpace ℂ F] in
@[simp] theorem baseCoefficient_apply (f : B × ComplexPlane₂ → F) (b : B) :
    baseCoefficient f b = f (b, 0) := rfl

theorem baseCoefficient_holomorphic {f : B × ComplexPlane₂ → F}
    (hf : ContMDiff I₃ IF ω f) : ContMDiff I₁ IF ω (baseCoefficient f) :=
  zeroSectionRestriction_holomorphic hf

omit [TopologicalSpace B] [ChartedSpace ℂ B] [NormedAddCommGroup F] [NormedSpace ℂ F] in
/-- Fibre independence is exactly factorization through the zero-section coefficient. -/
theorem eq_baseCoefficient_comp_fst_iff (f : B × ComplexPlane₂ → F) :
    f = baseCoefficient f ∘ Prod.fst ↔ ∀ b ζ, f (b, ζ) = f (b, 0) := by
  constructor
  · intro h b ζ
    exact congrFun h (b, ζ)
  · intro h
    funext x
    exact h x.1 x.2

/-- The factorization of a fibre-independent holomorphic coefficient is holomorphic. -/
theorem exists_holomorphic_baseCoefficient {f : B × ComplexPlane₂ → F}
    (hf : ContMDiff I₃ IF ω f) (hconst : ∀ b ζ, f (b, ζ) = f (b, 0)) :
    ∃ g : B → F, ContMDiff I₁ IF ω g ∧ f = g ∘ Prod.fst :=
  ⟨baseCoefficient f, baseCoefficient_holomorphic hf,
    (eq_baseCoefficient_comp_fst_iff f).mpr hconst⟩

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicForms
