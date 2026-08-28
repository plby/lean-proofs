import Wikipedia.HopfProblem.HolomorphicPicardNativeIsoGaugeBasic

/-!
# The extracted native isomorphism coordinates are actual holomorphic units

Holomorphicity is proved by composing the original source inverse chart,
the given analytic total-space isomorphism, and the original target chart.
The resulting nowhere-zero scalar is then bundled as an actual unit of the
holomorphic section ring on the common original cover.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicPicardNative

open PeriodTorusLineBundleClassificationNative HolomorphicExponentialSheaf

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]
    (V W : M → Type*)
    [∀ x, TopologicalSpace (V x)] [∀ x, TopologicalSpace (W x)]
    [TopologicalSpace (TotalSpace ℂ V)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ V] [FiberBundle ℂ W]
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [VectorBundle ℂ ℂ V] [VectorBundle ℂ ℂ W]
    [ContMDiffVectorBundle ω ℂ V I] [ContMDiffVectorBundle ω ℂ W I]

/-- The actual scalar extracted in original native charts is holomorphic. -/
theorem isoGaugeValue_contMDiff (e : AnalyticBundleIso I V W) (a : M × M) :
    ContMDiff I 𝓘(ℂ) ω (isoGaugeValue I M V W e a) := by
  intro x
  let tv := nativeTriv V a.1
  let tw := nativeTriv W a.2
  have hxv : ((x : M), (1 : ℂ)) ∈ tv.target := tv.mem_target.mpr x.property.1
  have hs : ContMDiffAt (I.prod 𝓘(ℂ)) (I.prod 𝓘(ℂ)) ω
      tv.toOpenPartialHomeomorph.symm ((x : M), (1 : ℂ)) :=
    tv.contMDiffOn_symm.contMDiffAt (tv.open_target.mem_nhds hxv)
  have hv : ContMDiff I I ω (Subtype.val : isoGaugeCover M V W a → M) :=
    contMDiff_subtype_val
  have hp : ContMDiffAt I (I.prod 𝓘(ℂ)) ω
      (fun y : isoGaugeCover M V W a => ((y : M), (1 : ℂ))) x :=
    hv.contMDiffAt.prodMk contMDiffAt_const
  have hlift : ContMDiffAt I (I.prod 𝓘(ℂ)) ω
      (fun y : isoGaugeCover M V W a =>
        tv.toOpenPartialHomeomorph.symm ((y : M), (1 : ℂ))) x := hs.comp x hp
  have he : ContMDiffAt I (I.prod 𝓘(ℂ)) ω
      (fun y : isoGaugeCover M V W a =>
        e.diffeomorph (tv.toOpenPartialHomeomorph.symm ((y : M), (1 : ℂ)))) x :=
    e.diffeomorph.contMDiff.contMDiffAt.comp x hlift
  have hxw : e.diffeomorph (tv.toOpenPartialHomeomorph.symm ((x : M), (1 : ℂ))) ∈
      tw.source := by
    rw [tw.mem_source, e.preserves_base, tv.proj_symm_apply' x.property.1]
    exact x.property.2
  have hw : ContMDiffAt (I.prod 𝓘(ℂ)) (I.prod 𝓘(ℂ)) ω tw
      (e.diffeomorph (tv.toOpenPartialHomeomorph.symm ((x : M), (1 : ℂ)))) :=
    tw.contMDiffOn.contMDiffAt (tw.open_source.mem_nhds hxw)
  exact (hw.comp x he).snd

/-- The actual scalar as an actual holomorphic section on the common patch. -/
def isoGaugeSection (e : AnalyticBundleIso I V W) (a : M × M) :
    HolomorphicFunctionSheaf.Section I M (isoGaugeCover M V W a) :=
  ⟨isoGaugeValue I M V W e a, isoGaugeValue_contMDiff I M V W e a⟩

@[simp] theorem isoGaugeSection_apply (e : AnalyticBundleIso I V W) (a : M × M)
    (x : isoGaugeCover M V W a) :
    isoGaugeSection I M V W e a x = isoGaugeValue I M V W e a x := rfl

/-- The unit is constructed from the proved nonvanishing of the actual
holomorphic coefficient of the original isomorphism. -/
def isoGaugeUnit (e : AnalyticBundleIso I V W) (a : M × M) :
    UnitSection I M (isoGaugeCover M V W a) :=
  unitSectionOfNonvanishing (isoGaugeSection I M V W e a)
    (isoGaugeValue_ne_zero I M V W e a)

@[simp] theorem isoGaugeUnit_eval (e : AnalyticBundleIso I V W) (a : M × M)
    (x : isoGaugeCover M V W a) :
    unitSectionEval (isoGaugeUnit I M V W e a) x = isoGaugeValue I M V W e a x := rfl

end Wikipedia.HopfProblem.HolomorphicPicardNative
