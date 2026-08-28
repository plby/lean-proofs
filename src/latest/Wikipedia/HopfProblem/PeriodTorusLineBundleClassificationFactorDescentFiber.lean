import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescentQuotient
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeIso

/-!
# The genuine fibre equivalences determined by a covering frame

In the preferred quotient lift and original native trivialization, the
fibre equivalence is multiplication by the actual nonzero frame coefficient.
The induced native total-space map is proved to be the map descended from
the covering frame, not merely to have the same base projection.
-/

noncomputable section

open Bundle Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescent

open PeriodTorusAppellHumbert PeriodTorusLineBundleClassificationNative

local notation "IC" => modelWithCornersSelf ℂ ComplexPlane₂
local notation "I₁" => modelWithCornersSelf ℂ ℂ

variable {p : PeriodDomain} {V : p.Torus → Type*}
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] [VectorBundle ℂ ℂ V]

variable (s : CoverSection p V) (hne : ∀ z, s z ≠ 0)

/-- The actual frame coefficient in the preferred lift and native chart. -/
def preferredFrameCoefficient (b : p.Torus) : ℂ :=
  coefficient s b (Core.lift p b b)

include hne in
theorem preferredFrameCoefficient_ne_zero (b : p.Torus) :
    preferredFrameCoefficient s b ≠ 0 := by
  apply coefficient_ne_zero s hne b (Core.lift p b b)
  rw [Core.lift_project p b (Core.mem_baseSet p b)]
  exact FiberBundle.mem_baseSet_trivializationAt ℂ V b

variable (F : FactorOfAutomorphy p)

/-- A complex-linear equivalence between the actual core fibre and the
independently given native fibre at the same base point. -/
def frameFiberEquiv (b : p.Torus) : (Core.data F).core.Fiber b ≃ₗ[ℂ] V b :=
  (LinearEquiv.smulOfNeZero ℂ ℂ (preferredFrameCoefficient s b)
    (preferredFrameCoefficient_ne_zero s hne b)).trans
      ((nativeTriv V b).linearEquivAt ℂ b
        (FiberBundle.mem_baseSet_trivializationAt ℂ V b)).symm

theorem frameFiberEquiv_apply (b : p.Torus) (c : (Core.data F).core.Fiber b) :
    frameFiberEquiv s hne F b c = (nativeTriv V b).symm b
      (preferredFrameCoefficient s b * id (α := ℂ) c) := rfl

/-- The native map induced by these actual fibre equivalences. -/
def frameCoreToNative (u : (Core.data F).core.TotalSpace) : TotalSpace ℂ V :=
  ⟨u.proj, frameFiberEquiv s hne F u.proj u.2⟩

/-- The fibrewise inverse into the actual cocycle bundle. -/
def frameNativeToCore (v : TotalSpace ℂ V) : (Core.data F).core.TotalSpace :=
  ⟨v.proj, (frameFiberEquiv s hne F v.proj).symm v.2⟩

@[simp] theorem frameCoreToNative_proj (u : (Core.data F).core.TotalSpace) :
    (frameCoreToNative s hne F u).proj = u.proj := rfl

@[simp] theorem frameNativeToCore_proj (v : TotalSpace ℂ V) :
    (frameNativeToCore s hne F v).proj = v.proj := rfl

@[simp] theorem frameCoreToNative_frameNativeToCore (v : TotalSpace ℂ V) :
    frameCoreToNative s hne F (frameNativeToCore s hne F v) = v := by
  cases v with
  | mk b v =>
      exact congrArg (TotalSpace.mk b)
        ((frameFiberEquiv s hne F b).apply_symm_apply v)

@[simp] theorem frameNativeToCore_frameCoreToNative (u : (Core.data F).core.TotalSpace) :
    frameNativeToCore s hne F (frameCoreToNative s hne F u) = u := by
  cases u with
  | mk b u =>
      exact congrArg (TotalSpace.mk b)
        ((frameFiberEquiv s hne F b).symm_apply_apply u)

variable (hrel : ∀ (l : p.lattice) (z : ComplexPlane₂) (c : ℂ),
    coverScalarMap s (z + l, (F.factor l z : ℂ) * c) = coverScalarMap s (z, c))

include hrel

/-- Equality with the genuine descended quotient map. The comparison is in
the original native chart, so no casts or replacement topology are hidden. -/
theorem frameCoreToNative_eq_quotient :
    frameCoreToNative s hne F = frameQuotientMap F s hrel ∘ Core.toAssociated F := by
  funext u
  let b := u.proj
  let e := nativeTriv V b
  have hb : b ∈ e.baseSet := FiberBundle.mem_baseSet_trivializationAt ℂ V b
  have hl : p.lattice.mkQ (Core.lift p b b) = b :=
    Core.lift_project p b (Core.mem_baseSet p b)
  change (⟨b, frameFiberEquiv s hne F b u.2⟩ : TotalSpace ℂ V) =
    coverScalarMap s (Core.lift p b b, id (α := ℂ) u.2)
  apply e.toOpenPartialHomeomorph.injOn
  · exact e.mem_source.mpr hb
  · apply e.mem_source.mpr
    change p.lattice.mkQ (Core.lift p b b) ∈ e.baseSet
    rwa [hl]
  change nativeTriv V b ⟨b, frameFiberEquiv s hne F b u.2⟩ =
    nativeTriv V b (coverScalarMap s (Core.lift p b b, id (α := ℂ) u.2))
  rw [frameFiberEquiv_apply, (nativeTriv V b).apply_mk_symm hb]
  rw [coverScalarMap_localTriv s b _ (by simpa only [hl] using hb), hl]
  apply Prod.ext
  · rfl
  · exact mul_comm _ _

variable [ContMDiffVectorBundle ω ℂ V IC] in
theorem frameCoreToNative_contMDiff :
    ContMDiff ((IC).prod I₁) ((IC).prod I₁) ω (frameCoreToNative s hne F) := by
  let := associatedChartedSpace F
  rw [frameCoreToNative_eq_quotient s hne F hrel]
  exact (frameQuotientMap_contMDiff F s hrel).comp (Core.toAssociated_holomorphic F)

/-- The map on actual quotient representatives is exactly scalar
multiplication of the supplied frame in the original native bundle. -/
theorem frameCoreToNative_fromAssociated (z : ComplexPlane₂) (c : ℂ) :
    frameCoreToNative s hne F (Core.fromAssociated F (associatedMap F (z, c))) =
      coverScalarMap s (z, c) := by
  rw [frameCoreToNative_eq_quotient s hne F hrel]
  simp only [Function.comp_apply, Core.toAssociated_fromAssociated,
    frameQuotientMap_associatedMap]

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFactorDescent
