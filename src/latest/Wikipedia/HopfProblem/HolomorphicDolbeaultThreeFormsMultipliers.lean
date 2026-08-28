import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFormsSheaf
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySmoothMultipliers

/-!
# Genuine smooth multipliers on the native antiholomorphic-form sheaf

Smooth complex-valued functions act by their original pointwise scalar
multiplication on native real cotangent covectors.  The action preserves
actual smoothness and anti-linearity, commutes with literal restriction,
and supplies the genuine complex scalar endomorphisms of the form sheaf.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Forms

open HolomorphicSheafCohomology

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Actual smooth scalar functions act on the original native fibres. -/
instance formSectionSmoothSMul (U : Opens M) :
    SMul (SmoothFunctions.Section 𝓘(ℝ, E) M U) (FormSection E M U) where
  smul g s := sectionMk E M U (fun x => g x • s x)
    (smoothSection_function_smul E M g s.val g.contMDiff (FormSection.smooth E M s))
    (fun x => (antiCovectors (E := E)).smul_mem (g x) (FormSection.anti E M s x))

@[simp] theorem function_smul_apply {U : Opens M}
    (g : SmoothFunctions.Section 𝓘(ℝ, E) M U) (s : FormSection E M U) (x : U) :
    (g • s) x = g x • s x := rfl

/-- The actual native form sections are a module over the original
smooth complex-valued section ring. -/
instance formSectionSmoothModule (U : Opens M) :
    Module (SmoothFunctions.Section 𝓘(ℝ, E) M U) (FormSection E M U) where
  one_smul s := FormSection.ext E M fun x => one_smul ℂ (s x)
  mul_smul f g s := FormSection.ext E M fun x => mul_smul (f x) (g x) (s x)
  smul_zero f := FormSection.ext E M fun x => smul_zero (f x)
  smul_add f s t := FormSection.ext E M fun x => smul_add (f x) (s x) (t x)
  add_smul f g s := FormSection.ext E M fun x => add_smul (f x) (g x) (s x)
  zero_smul s := FormSection.ext E M fun x => zero_smul ℂ (s x)

instance formSectionSmoothScalarTower (U : Opens M) :
    IsScalarTower ℂ (SmoothFunctions.Section 𝓘(ℝ, E) M U) (FormSection E M U) where
  smul_assoc c g s := FormSection.ext E M fun x => smul_assoc c (g x) (s x)

instance formSectionSmoothSMulCommClass (U : Opens M) :
    SMulCommClass ℂ (SmoothFunctions.Section 𝓘(ℝ, E) M U) (FormSection E M U) where
  smul_comm c g s := FormSection.ext E M fun x => smul_comm c (g x) (s x)

/-- Restriction uses the genuine restriction of the smooth scalar function. -/
theorem restriction_function_smul {U V : Opens M} (h : U ≤ V)
    (g : SmoothFunctions.Section 𝓘(ℝ, E) M V) (s : FormSection E M V) :
    restriction E M h (g • s) =
      (ContMDiffMap.restrictRingHom 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ℂ h g) • restriction E M h s :=
  FormSection.ext E M fun _ => rfl

/-- Literal multiplication of a native form section by a global smooth function. -/
def multiplySection (g : SmoothFunctions.GlobalFunction 𝓘(ℝ, E) M)
    (U : Opens M) (s : FormSection E M U) : FormSection E M U :=
  SmoothFunctions.globalRestriction 𝓘(ℝ, E) M g U • s

@[simp] theorem multiplySection_apply
    (g : SmoothFunctions.GlobalFunction 𝓘(ℝ, E) M)
    (U : Opens M) (s : FormSection E M U) (x : U) :
    multiplySection E M g U s x = g (x : M) • s x := rfl

/-- Multiplication by a smooth global function is complex-linear on
the original native form sections. -/
def multiplySectionLinearMap (g : SmoothFunctions.GlobalFunction 𝓘(ℝ, E) M)
    (U : Opens M) : FormSection E M U →ₗ[ℂ] FormSection E M U where
  toFun := multiplySection E M g U
  map_add' s t := FormSection.ext E M fun x => smul_add (g (x : M)) (s x) (t x)
  map_smul' c s := FormSection.ext E M fun x => smul_comm (g (x : M)) c (s x)

/-- Actual smooth multiplication is a morphism of the original form sheaf. -/
def multiplier (g : SmoothFunctions.GlobalFunction 𝓘(ℝ, E) M) :
    sheaf E M ⟶ sheaf E M where
  hom :=
    { app := fun U => AddCommGrpCat.ofHom (multiplySectionLinearMap E M g U.unop).toAddMonoidHom
      naturality := fun U V h => by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro s
        exact FormSection.ext E M fun _ => rfl }

/-- The smooth multiplier action is the actual endomorphism-ring action. -/
def multiplierRingHom :
    SmoothFunctions.GlobalFunction 𝓘(ℝ, E) M →+* End (sheaf E M) where
  toFun := multiplier E M
  map_zero' := by
    apply sheafEnd_ext E M
    intro U s x
    exact zero_smul ℂ (s x)
  map_one' := by
    apply sheafEnd_ext E M
    intro U s x
    exact one_smul ℂ (s x)
  map_add' f g := by
    apply sheafEnd_ext E M
    intro U s x
    exact add_smul (f (x : M)) (g (x : M)) (s x)
  map_mul' f g := by
    apply sheafEnd_ext E M
    intro U s x
    exact mul_smul (f (x : M)) (g (x : M)) (s x)

/-- The genuine complex scalar endomorphisms of the native form sheaf. -/
def scalarEnd : ℂ →+* End (sheaf E M) :=
  (multiplierRingHom E M).comp (SmoothFunctions.constantGlobalRingHom 𝓘(ℝ, E) M)

@[simp] theorem scalarEnd_apply (c : ℂ) (U : Opens M)
    (s : FormSection E M U) (x : U) :
    ((scalarEnd E M c).asHom.hom.app (op U) s) x = c • s x := rfl

/-- The sheaf-induced scalar map is the original pointwise complex
module action on actual native covector sections. -/
theorem scalarEnd_eq_smul (c : ℂ) (U : Opens M) (s : FormSection E M U) :
    (scalarEnd E M c).asHom.hom.app (op U) s = c • s :=
  FormSection.ext E M fun _ => rfl

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Forms
