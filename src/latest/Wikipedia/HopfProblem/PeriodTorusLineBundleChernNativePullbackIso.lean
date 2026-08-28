import Wikipedia.HopfProblem.PeriodTorusLineBundleChernNativePullbackIsoAnalytic

/-!
# Pullback of actual analytic native bundle isomorphisms

An analytic isomorphism of native complex line bundles pulls back along
an analytic base map to an analytic, fibrewise complex-linear isomorphism
of Mathlib's actual pullback bundles.  The maps on fibres and the native
total-space lift diagram are literal.  Identity, composition, and inverse
are preserved.  No factor of automorphy or presentation is an input.
-/

noncomputable section

open Bundle
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNative.AnalyticBundleIso

section Ext

variable {M E H : Type*} [TopologicalSpace M] [NormedAddCommGroup E]
    [NormedSpace ℂ E] [TopologicalSpace H] [ChartedSpace H M]
    {I : ModelWithCorners ℂ E H} {V W : M → Type*}
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, TopologicalSpace (W x)]
    [TopologicalSpace (TotalSpace ℂ V)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ V] [FiberBundle ℂ W]

/-- The genuine total-space map determines every part of an analytic bundle isomorphism. -/
@[ext] theorem ext {e g : AnalyticBundleIso I V W}
    (h : ∀ v, e.diffeomorph v = g.diffeomorph v) : e = g := by
  obtain ⟨d, l, hl⟩ := e
  obtain ⟨d', l', hl'⟩ := g
  have hd : d = d' := Diffeomorph.ext h
  have he : l = l' := by
    funext x
    apply LinearEquiv.ext
    intro v
    have hv : (⟨x, l x v⟩ : TotalSpace ℂ W) = ⟨x, l' x v⟩ :=
      (hl x v).symm.trans ((h ⟨x, v⟩).trans (hl' x v))
    exact TotalSpace.mk_injective x hv
  cases hd
  cases he
  rfl

end Ext

variable {M N E H E' H' : Type*}
    [TopologicalSpace M] [TopologicalSpace N]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [TopologicalSpace H]
    [NormedAddCommGroup E'] [NormedSpace ℂ E'] [TopologicalSpace H']
    [ChartedSpace H M] [ChartedSpace H' N]
    {I : ModelWithCorners ℂ E H} {J : ModelWithCorners ℂ E' H'}
    {V W U : N → Type*}
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, AddCommMonoid (U x)] [∀ x, Module ℂ (U x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, TopologicalSpace (W x)]
    [∀ x, TopologicalSpace (U x)]
    [TopologicalSpace (TotalSpace ℂ V)] [TopologicalSpace (TotalSpace ℂ W)]
    [TopologicalSpace (TotalSpace ℂ U)]
    [FiberBundle ℂ V] [FiberBundle ℂ W] [FiberBundle ℂ U]

/-- Pull back the actual native isomorphism, using proved analyticity in both directions. -/
def pullback (e : AnalyticBundleIso J V W) (f : ContMDiffMap I J M N ω) :
    AnalyticBundleIso I ((f : M → N) *ᵖ V) ((f : M → N) *ᵖ W) :=
  ofFiberEquiv (fun x => e.fiberEquiv (f x))
    (pullbackTotalMap_holomorphic e f) (pullbackTotalMap_holomorphic e.symm f)

@[simp] theorem pullback_fiberEquiv (e : AnalyticBundleIso J V W)
    (f : ContMDiffMap I J M N ω) (x : M) :
    (e.pullback f).fiberEquiv x = e.fiberEquiv (f x) := rfl

/-- The induced map on the genuine native pullback total spaces. -/
@[simp] theorem pullback_apply (e : AnalyticBundleIso J V W)
    (f : ContMDiffMap I J M N ω) (v : TotalSpace ℂ ((f : M → N) *ᵖ V)) :
    (e.pullback f).diffeomorph v = ⟨v.proj, e.fiberEquiv (f v.proj) v.2⟩ := rfl

@[simp] theorem pullback_symm_apply (e : AnalyticBundleIso J V W)
    (f : ContMDiffMap I J M N ω) (w : TotalSpace ℂ ((f : M → N) *ᵖ W)) :
    (e.pullback f).diffeomorph.symm w = ⟨w.proj, (e.fiberEquiv (f w.proj)).symm w.2⟩ := rfl

/-- The full native pullback diagram commutes pointwise. -/
theorem pullback_lift (e : AnalyticBundleIso J V W)
    (f : ContMDiffMap I J M N ω) (v : TotalSpace ℂ ((f : M → N) *ᵖ V)) :
    Pullback.lift (f : M → N) ((e.pullback f).diffeomorph v) =
      e.diffeomorph (Pullback.lift (f : M → N) v) :=
  pullbackTotalMap_lift e f v

theorem pullback_lift_comp (e : AnalyticBundleIso J V W)
    (f : ContMDiffMap I J M N ω) :
    Pullback.lift (f : M → N) ∘ (e.pullback f).diffeomorph =
      e.diffeomorph ∘ Pullback.lift (f : M → N) := by
  funext v
  exact pullback_lift e f v

/-- The inverse has the corresponding genuine total-space diagram. -/
theorem pullback_symm_lift (e : AnalyticBundleIso J V W)
    (f : ContMDiffMap I J M N ω) (w : TotalSpace ℂ ((f : M → N) *ᵖ W)) :
    Pullback.lift (f : M → N) ((e.pullback f).diffeomorph.symm w) =
      e.diffeomorph.symm (Pullback.lift (f : M → N) w) :=
  pullbackTotalMap_lift e.symm f w

/-- Pullback preserves the actual identity bundle isomorphism. -/
@[simp] theorem pullback_refl (V : N → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, TopologicalSpace (V x)] [TopologicalSpace (TotalSpace ℂ V)]
    [FiberBundle ℂ V] (f : ContMDiffMap I J M N ω) :
    (AnalyticBundleIso.refl (I := J) V).pullback f =
      AnalyticBundleIso.refl (I := I) ((f : M → N) *ᵖ V) := by
  apply ext
  intro v
  rfl

/-- Pullback respects composition of actual native bundle isomorphisms. -/
theorem pullback_trans (e : AnalyticBundleIso J V W) (g : AnalyticBundleIso J W U)
    (f : ContMDiffMap I J M N ω) :
    (e.trans g).pullback f = (e.pullback f).trans (g.pullback f) := by
  apply ext
  intro v
  rfl

/-- Pullback respects the actual inverse bundle isomorphism. -/
@[simp] theorem pullback_symm (e : AnalyticBundleIso J V W)
    (f : ContMDiffMap I J M N ω) :
    e.symm.pullback f = (e.pullback f).symm := by
  apply ext
  intro v
  rfl

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationNative.AnalyticBundleIso
