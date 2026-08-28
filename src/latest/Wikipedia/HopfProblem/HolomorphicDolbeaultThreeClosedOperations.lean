import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeClosedBasic
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeClosedSmooth
import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeFormsOperations

/-!
# Complex-linear operations on the actual closed native forms

The actual native coefficient functions commute with the original fibre
operations, including the ambient zero extension.  Their ordinary real
derivatives therefore prove that the genuine closed-form equation is
preserved by addition and constant complex scaling.  The resulting
section module is the submodule of the original dependent covectors.
-/

noncomputable section

open Bundle TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.ClosedForms

variable (E M : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

@[simp] theorem extendForm_zero (U : Opens M) (x : M) :
    extendForm E M U (fun _ => 0) x = 0 := by
  classical
  simp only [extendForm]
  split <;> rfl

@[simp] theorem extendForm_add {U : Opens M}
    (a b : ∀ x : U, Forms.Covector E M (x : M)) (x : M) :
    extendForm E M U (fun y => a y + b y) x =
      extendForm E M U a x + extendForm E M U b x := by
  classical
  by_cases hx : x ∈ U
  · simp only [extendForm, dif_pos hx]
  · simp only [extendForm, dif_neg hx, add_zero]

@[simp] theorem extendForm_smul {U : Opens M} (c : ℂ)
    (a : ∀ x : U, Forms.Covector E M (x : M)) (x : M) :
    extendForm E M U (fun y => c • a y) x = c • extendForm E M U a x := by
  classical
  by_cases hx : x ∈ U
  · simp only [extendForm, dif_pos hx]
  · simp only [extendForm, dif_neg hx, smul_zero]

variable [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Even away from the actual coordinate domain, the representative is
literal precomposition by the original inverse tangent trivialization. -/
theorem coordinateForm_comp (U : Opens M)
    (a : ∀ x : U, Forms.Covector E M (x : M)) (x₀ : M) (z : E) :
    coordinateForm E M U a x₀ z =
      (extendForm E M U a ((chartAt E x₀).symm z)).comp
        ((trivializationAt E (TangentSpace 𝓘(ℝ, E)) x₀).symmL ℝ
          ((chartAt E x₀).symm z)) := by
  ext v
  simp [coordinateForm, ContinuousLinearMap.inCoordinates]

@[simp] theorem coordinateForm_zero (U : Opens M) (x₀ : M) (z : E) :
    coordinateForm E M U (fun _ => 0) x₀ z = 0 := by
  rw [coordinateForm_comp, extendForm_zero]
  ext v
  rfl

@[simp] theorem coordinateForm_add {U : Opens M}
    (a b : ∀ x : U, Forms.Covector E M (x : M)) (x₀ : M) (z : E) :
    coordinateForm E M U (fun x => a x + b x) x₀ z =
      coordinateForm E M U a x₀ z + coordinateForm E M U b x₀ z := by
  simp only [coordinateForm_comp, extendForm_add]
  ext v
  rfl

@[simp] theorem coordinateForm_smul {U : Opens M} (c : ℂ)
    (a : ∀ x : U, Forms.Covector E M (x : M)) (x₀ : M) (z : E) :
    coordinateForm E M U (fun x => c • a x) x₀ z =
      c • coordinateForm E M U a x₀ z := by
  simp only [coordinateForm_comp, extendForm_smul]
  ext v
  rfl

variable [NormedSpace ℂ E] [IsScalarTower ℝ ℂ E]

/-- The literal zero covector satisfies the native coefficient PDE. -/
theorem isClosed_zero (U : Opens M) :
    IsClosed E M U (fun _ => 0) := by
  intro x₀ z hz v w
  simp only [coordinateForm_zero, zero_apply]
  rw [dbar_zero_of_differentiableAt (differentiableAt_const (c := (0 : ℂ)))]
  rfl

/-- Native smoothness supplies the derivatives needed for additivity of
the actual differential equation, without any local primitive. -/
theorem IsClosed.add {U : Opens M} (s t : Forms.FormSection E M U)
    (hs : IsClosed E M U s.val) (ht : IsClosed E M U t.val) :
    IsClosed E M U (fun x => s x + t x) := by
  intro x₀ z hz v w
  simp only [coordinateForm_add, add_apply]
  change dbar ((fun y => coordinateForm E M U s.val x₀ y w) +
      fun y => coordinateForm E M U t.val x₀ y w) z v =
    dbar ((fun y => coordinateForm E M U s.val x₀ y v) +
      fun y => coordinateForm E M U t.val x₀ y v) z w
  rw [dbar_add (coordinateForm_apply_differentiableAt E M s x₀ z hz w)
      (coordinateForm_apply_differentiableAt E M t x₀ z hz w),
    dbar_add (coordinateForm_apply_differentiableAt E M s x₀ z hz v)
      (coordinateForm_apply_differentiableAt E M t x₀ z hz v)]
  simp only [add_apply, hs x₀ z hz v w, ht x₀ z hz v w]

/-- Constant complex scaling preserves the actual native coefficient
PDE, using the original real Fréchet derivatives. -/
theorem IsClosed.smul {U : Opens M} (c : ℂ) (s : Forms.FormSection E M U)
    (hs : IsClosed E M U s.val) : IsClosed E M U (fun x => c • s x) := by
  intro x₀ z hz v w
  simp only [coordinateForm_smul, smul_apply, smul_eq_mul]
  rw [dbar_const_mul c (coordinateForm_apply_differentiableAt E M s x₀ z hz w),
    dbar_const_mul c (coordinateForm_apply_differentiableAt E M s x₀ z hz v)]
  simp only [smul_apply, hs x₀ z hz v w]

/-- The actual smooth antiholomorphic forms satisfying the native PDE
are a complex submodule of the original dependent real covectors. -/
def closedSubmodule (U : Opens M) :
    Submodule ℂ (∀ x : U, Forms.Covector E M (x : M)) where
  carrier := {a | (closedLocalPredicate E M).pred a}
  zero_mem' := ⟨(Forms.formSubmodule E M U).zero_mem, isClosed_zero E M U⟩
  add_mem' := by
    intro a b ha hb
    exact ⟨(Forms.formSubmodule E M U).add_mem ha.1 hb.1,
      IsClosed.add E M ⟨a, ha.1⟩ ⟨b, hb.1⟩ ha.2 hb.2⟩
  smul_mem' := by
    intro c a ha
    exact ⟨(Forms.formSubmodule E M U).smul_mem c ha.1,
      IsClosed.smul E M c ⟨a, ha.1⟩ ha.2⟩

instance closedFormSectionAddCommGroup (U : Opens M) :
    AddCommGroup (ClosedFormSection E M U) :=
  inferInstanceAs (AddCommGroup ↥(closedSubmodule E M U))

instance closedFormSectionModule (U : Opens M) : Module ℂ (ClosedFormSection E M U) :=
  inferInstanceAs (Module ℂ ↥(closedSubmodule E M U))

namespace ClosedFormSection

@[simp] theorem zero_apply (U : Opens M) (x : U) :
    (0 : ClosedFormSection E M U) x = 0 := rfl

@[simp] theorem add_apply {U : Opens M} (s t : ClosedFormSection E M U) (x : U) :
    (s + t) x = s x + t x := rfl

@[simp] theorem neg_apply {U : Opens M} (s : ClosedFormSection E M U) (x : U) :
    (-s) x = -s x := rfl

@[simp] theorem sub_apply {U : Opens M} (s t : ClosedFormSection E M U) (x : U) :
    (s - t) x = s x - t x := rfl

@[simp] theorem smul_apply {U : Opens M} (c : ℂ) (s : ClosedFormSection E M U)
    (x : U) : (c • s) x = c • s x := rfl

/-- Evaluation is the original pointwise complex-linear fibre map. -/
def evaluationLinearMap (U : Opens M) (x : U) :
    ClosedFormSection E M U →ₗ[ℂ] Forms.Covector E M (x : M) where
  toFun s := s x
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem evaluationLinearMap_apply (U : Opens M) (x : U)
    (s : ClosedFormSection E M U) : evaluationLinearMap E M U x s = s x := rfl

end ClosedFormSection

/-- Forgetting only the actual PDE is linear for the literal native
pointwise operations on both spaces of covector sections. -/
def toFormLinearMap (U : Opens M) :
    ClosedFormSection E M U →ₗ[ℂ] Forms.FormSection E M U where
  toFun := ClosedFormSection.toForm E M
  map_add' _ _ := Forms.FormSection.ext E M fun _ => rfl
  map_smul' _ _ := Forms.FormSection.ext E M fun _ => rfl

@[simp] theorem toFormLinearMap_apply (U : Opens M) (s : ClosedFormSection E M U) :
    toFormLinearMap E M U s = ClosedFormSection.toForm E M s := rfl

theorem toFormLinearMap_injective (U : Opens M) :
    Function.Injective (toFormLinearMap E M U) := by
  intro s t h
  apply ClosedFormSection.ext E M
  intro x
  exact congrArg (fun a : Forms.FormSection E M U => a x) h

/-- Literal restriction of the original closed covectors is complex-linear. -/
def restrictionLinearMap {U V : Opens M} (h : U ≤ V) :
    ClosedFormSection E M V →ₗ[ℂ] ClosedFormSection E M U where
  toFun := restriction E M h
  map_add' _ _ := ClosedFormSection.ext E M fun _ => rfl
  map_smul' _ _ := ClosedFormSection.ext E M fun _ => rfl

@[simp] theorem restrictionLinearMap_apply {U V : Opens M} (h : U ≤ V)
    (s : ClosedFormSection E M V) :
    restrictionLinearMap E M h s = restriction E M h s := rfl

@[simp] theorem restriction_zero {U V : Opens M} (h : U ≤ V) :
    restriction E M h (0 : ClosedFormSection E M V) = 0 :=
  (restrictionLinearMap E M h).map_zero

@[simp] theorem restriction_add {U V : Opens M} (h : U ≤ V)
    (s t : ClosedFormSection E M V) :
    restriction E M h (s + t) = restriction E M h s + restriction E M h t :=
  (restrictionLinearMap E M h).map_add s t

@[simp] theorem restriction_smul {U V : Opens M} (h : U ≤ V)
    (c : ℂ) (s : ClosedFormSection E M V) :
    restriction E M h (c • s) = c • restriction E M h s :=
  (restrictionLinearMap E M h).map_smul c s

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.ClosedForms
