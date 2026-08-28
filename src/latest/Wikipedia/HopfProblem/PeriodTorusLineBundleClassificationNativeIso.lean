import Wikipedia.HopfProblem.HolomorphicCharacterBundleCore
import Mathlib.Geometry.Manifold.Diffeomorph

/-!
# Analytic isomorphisms of native complex line bundles

The objects in this file use the original native bundle topologies and atlases.
An isomorphism consists of an analytic diffeomorphism of total spaces together
with its actual complex-linear equivalences on the fibres. In particular, no
global frame, factor of automorphy, or classification statement occurs in the
definition.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNative

variable {M E H : Type*} [TopologicalSpace M] [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace H] [ChartedSpace H M]
    (I : ModelWithCorners ℂ E H)

local notation "I₁" => modelWithCornersSelf ℂ ℂ

/-- A genuine analytic, fibrewise complex-linear isomorphism of native bundles.
The compatibility field refers to the actual total-space map, not to a chosen
scalar gauge or to a hypothetical global trivialization. -/
structure AnalyticBundleIso (V W : M → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, TopologicalSpace (W x)]
    [TopologicalSpace (TotalSpace ℂ V)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ V] [FiberBundle ℂ W] where
  diffeomorph : Diffeomorph (I.prod I₁) (I.prod I₁)
    (TotalSpace ℂ V) (TotalSpace ℂ W) ω
  fiberEquiv : ∀ x, V x ≃ₗ[ℂ] W x
  map_fiber : ∀ x v, diffeomorph ⟨x, v⟩ = ⟨x, fiberEquiv x v⟩

namespace AnalyticBundleIso

variable {I} {V W U : M → Type*}
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, AddCommMonoid (U x)] [∀ x, Module ℂ (U x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, TopologicalSpace (W x)]
    [∀ x, TopologicalSpace (U x)]
    [TopologicalSpace (TotalSpace ℂ V)] [TopologicalSpace (TotalSpace ℂ W)]
    [TopologicalSpace (TotalSpace ℂ U)]
    [FiberBundle ℂ V] [FiberBundle ℂ W] [FiberBundle ℂ U]

@[simp] theorem preserves_base (e : AnalyticBundleIso I V W) (v : TotalSpace ℂ V) :
    (e.diffeomorph v).proj = v.proj := by
  cases v with
  | mk x v => rw [e.map_fiber]

@[simp] theorem symm_map_fiber (e : AnalyticBundleIso I V W) (x : M) (w : W x) :
    e.diffeomorph.symm ⟨x, w⟩ = ⟨x, (e.fiberEquiv x).symm w⟩ := by
  apply e.diffeomorph.injective
  change e.diffeomorph (e.diffeomorph.symm ⟨x, w⟩) =
    e.diffeomorph ⟨x, (e.fiberEquiv x).symm w⟩
  rw [e.diffeomorph.apply_symm_apply, e.map_fiber, LinearEquiv.apply_symm_apply]

@[simp] theorem symm_preserves_base (e : AnalyticBundleIso I V W) (w : TotalSpace ℂ W) :
    (e.diffeomorph.symm w).proj = w.proj := by
  cases w with
  | mk x w => rw [e.symm_map_fiber]

/-- The inverse uses the inverse of the original analytic total-space map. -/
protected def symm (e : AnalyticBundleIso I V W) : AnalyticBundleIso I W V where
  diffeomorph := e.diffeomorph.symm
  fiberEquiv x := (e.fiberEquiv x).symm
  map_fiber := e.symm_map_fiber

/-- Composition preserves the actual native bundle maps. -/
protected def trans (e : AnalyticBundleIso I V W) (f : AnalyticBundleIso I W U) :
    AnalyticBundleIso I V U where
  diffeomorph := e.diffeomorph.trans f.diffeomorph
  fiberEquiv x := (e.fiberEquiv x).trans (f.fiberEquiv x)
  map_fiber x v := by
    change f.diffeomorph (e.diffeomorph ⟨x, v⟩) = _
    rw [e.map_fiber, f.map_fiber]
    rfl

/-- The identity native bundle isomorphism. -/
protected def refl (V : M → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] : AnalyticBundleIso I V V where
  diffeomorph := Diffeomorph.refl (I.prod I₁) (TotalSpace ℂ V) ω
  fiberEquiv _ := LinearEquiv.refl ℂ _
  map_fiber _ _ := rfl

/-- Construct an analytic bundle isomorphism from fibre equivalences only
after proving that both induced maps on the original total spaces are analytic. -/
def ofFiberEquiv (e : ∀ x, V x ≃ₗ[ℂ] W x)
    (he : ContMDiff (I.prod I₁) (I.prod I₁) ω
      (fun v : TotalSpace ℂ V => (⟨v.proj, e v.proj v.2⟩ : TotalSpace ℂ W)))
    (hei : ContMDiff (I.prod I₁) (I.prod I₁) ω
      (fun w : TotalSpace ℂ W => (⟨w.proj, (e w.proj).symm w.2⟩ : TotalSpace ℂ V))) :
    AnalyticBundleIso I V W where
  diffeomorph :=
    { toFun := fun v => ⟨v.proj, e v.proj v.2⟩
      invFun := fun w => ⟨w.proj, (e w.proj).symm w.2⟩
      left_inv := by
        rintro ⟨x, v⟩
        simp only [LinearEquiv.symm_apply_apply]
      right_inv := by
        rintro ⟨x, w⟩
        simp only [LinearEquiv.apply_symm_apply]
      contMDiff_toFun := he
      contMDiff_invFun := hei }
  fiberEquiv := e
  map_fiber _ _ := rfl

@[simp] theorem ofFiberEquiv_apply (e : ∀ x, V x ≃ₗ[ℂ] W x) (he hei)
    (v : TotalSpace ℂ V) :
    (ofFiberEquiv (I := I) e he hei).diffeomorph v = ⟨v.proj, e v.proj v.2⟩ := rfl

end AnalyticBundleIso

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNative
