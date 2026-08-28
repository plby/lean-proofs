import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFormsBasic
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFormsSmoothOperations

/-!
# Pointwise complex-linear operations on native antiholomorphic forms

The actual smooth anti-linear covectors are closed under the original
fibre operations.  Their section groups and complex scalar actions are
therefore the submodule structures inherited from dependent covectors,
not structures transported from a separate coefficient space.
-/

noncomputable section

open Bundle TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Forms

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Actual native form sections are a complex submodule of the original
dependent real cotangent vectors. -/
def formSubmodule (U : Opens M) : Submodule ℂ (∀ x : U, Covector E M (x : M)) where
  carrier := {a | (formLocalPredicate E M).pred a}
  zero_mem' := ⟨smoothSection_zero E M U, fun _ => (antiCovectors (E := E)).zero_mem⟩
  add_mem' := by
    intro a b ha hb
    exact ⟨smoothSection_add E M a b ha.1 hb.1,
      fun x => (antiCovectors (E := E)).add_mem (ha.2 x) (hb.2 x)⟩
  smul_mem' := by
    intro c a ha
    exact ⟨smoothSection_smul E M c a ha.1,
      fun x => (antiCovectors (E := E)).smul_mem c (ha.2 x)⟩

instance formSectionAddCommGroup (U : Opens M) : AddCommGroup (FormSection E M U) :=
  inferInstanceAs (AddCommGroup ↥(formSubmodule E M U))

instance formSectionModule (U : Opens M) : Module ℂ (FormSection E M U) :=
  inferInstanceAs (Module ℂ ↥(formSubmodule E M U))

namespace FormSection

@[simp] theorem zero_apply (U : Opens M) (x : U) :
    (0 : FormSection E M U) x = 0 := rfl

@[simp] theorem add_apply {U : Opens M} (s t : FormSection E M U) (x : U) :
    (s + t) x = s x + t x := rfl

@[simp] theorem neg_apply {U : Opens M} (s : FormSection E M U) (x : U) :
    (-s) x = -s x := rfl

@[simp] theorem sub_apply {U : Opens M} (s t : FormSection E M U) (x : U) :
    (s - t) x = s x - t x := rfl

@[simp] theorem smul_apply {U : Opens M} (c : ℂ) (s : FormSection E M U) (x : U) :
    (c • s) x = c • s x := rfl

/-- Evaluation at a point is the original complex-linear fibre map. -/
def evaluationLinearMap (U : Opens M) (x : U) :
    FormSection E M U →ₗ[ℂ] Covector E M (x : M) where
  toFun s := s x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem evaluationLinearMap_apply (U : Opens M) (x : U) (s : FormSection E M U) :
    evaluationLinearMap E M U x s = s x := rfl

end FormSection

/-- Literal native restriction is complex-linear for the actual
pointwise fibre actions. -/
def restrictionLinearMap {U V : Opens M} (h : U ≤ V) :
    FormSection E M V →ₗ[ℂ] FormSection E M U where
  toFun := restriction E M h
  map_add' _ _ := FormSection.ext E M fun _ => rfl
  map_smul' _ _ := FormSection.ext E M fun _ => rfl

@[simp] theorem restrictionLinearMap_apply {U V : Opens M} (h : U ≤ V)
    (s : FormSection E M V) :
    restrictionLinearMap E M h s = restriction E M h s := rfl

@[simp] theorem restriction_zero {U V : Opens M} (h : U ≤ V) :
    restriction E M h (0 : FormSection E M V) = 0 :=
  (restrictionLinearMap E M h).map_zero

@[simp] theorem restriction_add {U V : Opens M} (h : U ≤ V)
    (s t : FormSection E M V) :
    restriction E M h (s + t) = restriction E M h s + restriction E M h t :=
  (restrictionLinearMap E M h).map_add s t

@[simp] theorem restriction_smul {U V : Opens M} (h : U ≤ V)
    (c : ℂ) (s : FormSection E M V) :
    restriction E M h (c • s) = c • restriction E M h s :=
  (restrictionLinearMap E M h).map_smul c s

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.Forms
