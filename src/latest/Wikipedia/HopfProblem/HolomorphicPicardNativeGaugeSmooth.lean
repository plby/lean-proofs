import Wikipedia.HopfProblem.HolomorphicPicardNativeGaugeBasic

/-!
# A genuine holomorphic gauge gives analytic maps of original total spaces

On each member of the actual common covering family the forward map has
the given holomorphic scalar coefficient, and the inverse has its actual
unit inverse. The original native charts therefore prove both maps analytic.
-/

noncomputable section

open Bundle Set Topology TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicPicardNative.NativeGauge

open HolomorphicExponentialSheaf PeriodTorusLineBundleClassificationNative

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]

/-- An ambient function agreeing with an actual unit section on its open
domain. No regularity outside that domain is asserted or used. -/
def unitValueOnBase {U : Opens M} (b : UnitSection I M U) (x : M) : ℂ := by
  classical
  exact if hx : x ∈ U then unitSectionEval b ⟨x, hx⟩ else 1

@[simp] theorem unitValueOnBase_of_mem {U : Opens M} (b : UnitSection I M U)
    (x : M) (hx : x ∈ U) :
    unitValueOnBase I M b x = unitSectionEval b ⟨x, hx⟩ := by
  classical
  exact dif_pos hx

theorem unitValueOnBase_holomorphicAt {U : Opens M} (b : UnitSection I M U)
    (x : M) (hx : x ∈ U) :
    ContMDiffAt I 𝓘(ℂ) ω (unitValueOnBase I M b) x := by
  apply (contMDiffAt_subtype_iff (f := unitValueOnBase I M b) (x := ⟨x, hx⟩)).mp
  have heq : (fun y : U => unitValueOnBase I M b y) = unitSectionVal b := by
    funext y
    exact unitValueOnBase_of_mem I M b y y.property
  rw [heq]
  exact (unitSectionVal b).contMDiff.contMDiffAt

variable (V W : M → Type*)
    [∀ x, AddCommMonoid (V x)] [∀ x, Module ℂ (V x)]
    [∀ x, AddCommMonoid (W x)] [∀ x, Module ℂ (W x)]
    [∀ x, TopologicalSpace (V x)] [∀ x, TopologicalSpace (W x)]
    [TopologicalSpace (TotalSpace ℂ V)] [TopologicalSpace (TotalSpace ℂ W)]
    [FiberBundle ℂ V] [FiberBundle ℂ W] [VectorBundle ℂ ℂ V] [VectorBundle ℂ ℂ W]
    [ContMDiffVectorBundle ω ℂ V I] [ContMDiffVectorBundle ω ℂ W I]
    {ι : Type} (U : ι → Opens M) (r s : ι → M)
    (hV : ∀ i, U i ≤ nativeCover M V (r i))
    (hW : ∀ i, U i ≤ nativeCover M W (s i))
    (b : ∀ i, UnitSection I M (U i))
    (hpoint : ∀ i j x (hi : x ∈ U i) (hj : x ∈ U j),
      unitSectionEval (b j) ⟨x, hj⟩ * (scalarTransition V (r i) (r j) x : ℂ) =
        (scalarTransition W (s i) (s j) x : ℂ) * unitSectionEval (b i) ⟨x, hi⟩)
    (hcover : ∀ x : M, ∃ i, x ∈ U i)

include hpoint in
theorem toBundle_holomorphic : ContMDiff (I.prod 𝓘(ℂ)) (I.prod 𝓘(ℂ)) ω
    (toBundle I M V W U r s hV hW b hcover) := by
  intro v
  obtain ⟨i, hi⟩ := hcover v.proj
  let ev := nativeTriv V (r i)
  let ew := nativeTriv W (s i)
  have hw : toBundle I M V W U r s hV hW b hcover v ∈ ew.source :=
    ew.mem_source.mpr (hW i hi)
  apply (ew.contMDiffAt_iff hw).mpr
  constructor
  · exact Bundle.contMDiffAt_proj V
  · have hv : v ∈ ev.source := ev.mem_source.mpr (hV i hi)
    have he : ContMDiffAt (I.prod 𝓘(ℂ)) (I.prod 𝓘(ℂ)) ω ev v :=
      ev.contMDiffOn.contMDiffAt (ev.open_source.mem_nhds hv)
    have hb : ContMDiffAt I 𝓘(ℂ) ω (unitValueOnBase I M (b i)) v.proj :=
      unitValueOnBase_holomorphicAt I M (b i) v.proj hi
    have hp : ContMDiffAt (I.prod 𝓘(ℂ)) I ω (π ℂ V) v := Bundle.contMDiffAt_proj V
    apply ((hb.comp v hp).mul he.snd).congr_of_eventuallyEq
    have hn : {w : TotalSpace ℂ V | w.proj ∈ U i} ∈ 𝓝 v :=
      ((U i).isOpen.preimage (FiberBundle.continuous_proj ℂ V)).mem_nhds hi
    filter_upwards [hn] with w hw
    change (ew (toBundle I M V W U r s hV hW b hcover w)).2 =
      unitValueOnBase I M (b i) w.proj * (ev w).2
    rw [unitValueOnBase_of_mem I M (b i) w.proj hw]
    exact fiberEquiv_coordinate I M V W U r s hV hW b hpoint hcover i w.proj hw w.2

include hpoint in
theorem fromBundle_holomorphic : ContMDiff (I.prod 𝓘(ℂ)) (I.prod 𝓘(ℂ)) ω
    (fromBundle I M V W U r s hV hW b hcover) := by
  intro w
  obtain ⟨i, hi⟩ := hcover w.proj
  let ev := nativeTriv V (r i)
  let ew := nativeTriv W (s i)
  have hv : fromBundle I M V W U r s hV hW b hcover w ∈ ev.source :=
    ev.mem_source.mpr (hV i hi)
  apply (ev.contMDiffAt_iff hv).mpr
  constructor
  · exact Bundle.contMDiffAt_proj W
  · have hw : w ∈ ew.source := ew.mem_source.mpr (hW i hi)
    have he : ContMDiffAt (I.prod 𝓘(ℂ)) (I.prod 𝓘(ℂ)) ω ew w :=
      ew.contMDiffOn.contMDiffAt (ew.open_source.mem_nhds hw)
    have hb : ContMDiffAt I 𝓘(ℂ) ω (unitValueOnBase I M (-b i)) w.proj :=
      unitValueOnBase_holomorphicAt I M (-b i) w.proj hi
    have hp : ContMDiffAt (I.prod 𝓘(ℂ)) I ω (π ℂ W) w := Bundle.contMDiffAt_proj W
    apply ((hb.comp w hp).mul he.snd).congr_of_eventuallyEq
    have hn : {v : TotalSpace ℂ W | v.proj ∈ U i} ∈ 𝓝 w :=
      ((U i).isOpen.preimage (FiberBundle.continuous_proj ℂ W)).mem_nhds hi
    filter_upwards [hn] with v hv
    change (ev (fromBundle I M V W U r s hV hW b hcover v)).2 =
      unitValueOnBase I M (-b i) v.proj * (ew v).2
    rw [unitValueOnBase_of_mem I M (-b i) v.proj hv]
    exact fiberEquiv_symm_coordinate I M V W U r s hV hW b hpoint hcover i v.proj hv v.2

/-- A genuine holomorphic gauge on an actual common refinement induces an
actual analytic, fibrewise complex-linear isomorphism of the original
native bundles. -/
def analyticBundleIso : AnalyticBundleIso I V W :=
  AnalyticBundleIso.ofFiberEquiv (fiberEquiv I M V W U r s hV hW b hcover)
    (toBundle_holomorphic I M V W U r s hV hW b hpoint hcover)
    (fromBundle_holomorphic I M V W U r s hV hW b hpoint hcover)

theorem analyticBundleIso_coordinate (i : ι) (x : M) (hx : x ∈ U i) (v : V x) :
    (nativeTriv W (s i)
      ((analyticBundleIso I M V W U r s hV hW b hpoint hcover).diffeomorph ⟨x, v⟩)).2 =
      unitSectionEval (b i) ⟨x, hx⟩ * (nativeTriv V (r i) ⟨x, v⟩).2 :=
  fiberEquiv_coordinate I M V W U r s hV hW b hpoint hcover i x hx v

end Wikipedia.HopfProblem.HolomorphicPicardNative.NativeGauge
