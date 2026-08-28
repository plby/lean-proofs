import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNativeIso

/-!
# Continuous trivializations of native complex line bundles

A continuous trivialization is a homeomorphism from the original total space
to the product with `ℂ`, together with its actual complex-linear maps on the
fibres. Neither the total-space topology nor the fibre modules are replaced.
An analytic bundle isomorphism transports such a trivialization by composing
the original total-space homeomorphisms.
-/

noncomputable section

open Bundle

namespace Wikipedia.HopfProblem.HolomorphicPicard

variable {M : Type*} [TopologicalSpace M]

/-- A continuous, fibrewise complex-linear trivialization for the original
total-space topology of a native family of complex modules. -/
structure ContinuousTrivialization (V : M → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [TopologicalSpace (TotalSpace ℂ V)] where
  homeomorph : TotalSpace ℂ V ≃ₜ M × ℂ
  fiberEquiv : ∀ x, V x ≃ₗ[ℂ] ℂ
  map_fiber : ∀ x v, homeomorph ⟨x, v⟩ = (x, fiberEquiv x v)

namespace ContinuousTrivialization

variable {V : M → Type*}
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [TopologicalSpace (TotalSpace ℂ V)]

/-- The actual homeomorphism lies over the identity of the base. -/
@[simp] theorem preserves_base (t : ContinuousTrivialization V) (v : TotalSpace ℂ V) :
    (t.homeomorph v).1 = v.proj := by
  cases v with
  | mk x v => rw [t.map_fiber]

/-- The inverse homeomorphism uses the inverse of the original fibre map. -/
@[simp] theorem symm_map_fiber (t : ContinuousTrivialization V) (x : M) (z : ℂ) :
    t.homeomorph.symm (x, z) = ⟨x, (t.fiberEquiv x).symm z⟩ := by
  apply t.homeomorph.injective
  rw [t.homeomorph.apply_symm_apply, t.map_fiber, LinearEquiv.apply_symm_apply]

/-- The actual inverse homeomorphism also lies over the identity of the base. -/
@[simp] theorem symm_preserves_base (t : ContinuousTrivialization V) (u : M × ℂ) :
    (t.homeomorph.symm u).proj = u.1 := by
  rcases u with ⟨x, z⟩
  rw [t.symm_map_fiber]

section AnalyticTransport

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] [ChartedSpace H M]
    {I : ModelWithCorners ℂ E H} {W : M → Type*}
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, TopologicalSpace (W x)]
    [TopologicalSpace (TotalSpace ℂ W)] [FiberBundle ℂ V] [FiberBundle ℂ W]

/-- Transport a continuous trivialization along the genuine analytic
isomorphism of the original native total spaces and fibre modules. -/
def ofAnalyticBundleIso
    (e : PeriodTorusLineBundleClassificationNative.AnalyticBundleIso I V W)
    (t : ContinuousTrivialization W) : ContinuousTrivialization V where
  homeomorph := e.diffeomorph.toHomeomorph.trans t.homeomorph
  fiberEquiv x := (e.fiberEquiv x).trans (t.fiberEquiv x)
  map_fiber x v := by
    change t.homeomorph (e.diffeomorph ⟨x, v⟩) = _
    rw [e.map_fiber, t.map_fiber]
    rfl

@[simp] theorem ofAnalyticBundleIso_homeomorph_apply
    (e : PeriodTorusLineBundleClassificationNative.AnalyticBundleIso I V W)
    (t : ContinuousTrivialization W) (v : TotalSpace ℂ V) :
    (ofAnalyticBundleIso e t).homeomorph v = t.homeomorph (e.diffeomorph v) := rfl

@[simp] theorem ofAnalyticBundleIso_fiberEquiv_apply
    (e : PeriodTorusLineBundleClassificationNative.AnalyticBundleIso I V W)
    (t : ContinuousTrivialization W) (x : M) (v : V x) :
    (ofAnalyticBundleIso e t).fiberEquiv x v = t.fiberEquiv x (e.fiberEquiv x v) := rfl

end AnalyticTransport

end ContinuousTrivialization

end Wikipedia.HopfProblem.HolomorphicPicard
