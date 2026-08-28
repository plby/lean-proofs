import Wikipedia.HopfProblem.DegreeCollapseBeltCircleForwardSection
import Wikipedia.HopfProblem.DegreeCollapseNativeTransversePostcomposition

/-!
# The middle belt loop with its actual transverse forward-basin sheet

Whole flow cylinders retain the orbit formula on the entire open crossing
domain. Thus the original belt supplies a native smooth local sheet in the
middle level, lying in the actual forward basin. Its transversality to the
constructed loop is transported through the genuine partial diffeomorphism.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.exists_transverse_middle_belt_loop
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6)
    (p q : criticalPoints E f) (hp : nativeMorseIndex E f p = 0)
    (hq : nativeMorseIndex E f q = 1)
    [Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 4 + 1)]
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hbranches : ∀ w : sphere (0 : (S.data q).chart.NegativeCoordinates) 1,
      Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere w).val) atTop (𝓝 p.val))
    {a : ℝ} (hqa : S.toSurgeryWindows.upper q ≤ a)
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hlow : ∀ z : criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 2) :
    let _ := RegularLevel.chartedSpace hf ha
    ∃ δ : C(Hemisphere.Sphere 1, {y : M // f y = a}),
      ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ δ ∧ Injective δ ∧
      (∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) δ z)) ∧
      ∃ (z₀ : Hemisphere.Sphere 1) (v : sphere (0 : (S.data q).chart.PositiveCoordinates) 1)
        (β : sphere (0 : (S.data q).chart.PositiveCoordinates) 1 → {y : M // f y = a}),
        MDifferentiableAt (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) β v ∧ β v = δ z₀ ∧
        NativeTransversality.At (𝓡 1) (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) δ β z₀ v ∧
        (∀ᶠ w in 𝓝 v, Tendsto (fun t => S.flow t (β w).val) atTop (𝓝 q.val)) ∧
        (∀ z, Tendsto (fun t => S.flow t (δ z).val) atTop (𝓝 q.val) ↔ z = z₀) ∧
        ∀ z, Tendsto (fun t => S.flow t (δ z).val) atTop (𝓝 p.val) ∨
          Tendsto (fun t => S.flow t (δ z).val) atTop (𝓝 q.val) := by
  let _ := RegularLevel.chartedSpace hf (S.data q).upper_regular
  let _ := RegularLevel.chartedSpace hf ha
  let _ := RegularLevel.isManifold hf (S.data q).upper_regular
  let _ := RegularLevel.isManifold hf ha
  obtain ⟨v, γ, hγ, hγi, hγd, hreach, z₀, hsingle, htrans, hendpoints⟩ :=
    S.exists_transverse_belt_circle_reaching_level_with_endpoints hf p q hp hq 4 u hbranches hqa ha hlow
      (by omega) (by omega) (by omega)
  obtain ⟨t₀, ht₀⟩ := hreach z₀
  let za : {y : M // f y = a} := ⟨S.flow t₀ (γ z₀).val, ht₀⟩
  obtain ⟨D, hsource, -, horbit⟩ :=
    S.exists_native_level_basin_transport hf (S.data q).upper_regular ha (γ z₀) za
  have hγsource (z : Circle) : γ z ∈ D.source := hsource.symm ▸ hreach z
  have hΓsmooth : ContMDiff (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) ∞ (D ∘ γ) := by
    intro z
    exact (D.contMDiffOn_toFun.contMDiffAt (D.open_source.mem_nhds (hγsource z))).comp z
      hγ.contMDiffAt
  let Γ : C(Circle, {y : M // f y = a}) := ⟨D ∘ γ, hΓsmooth.continuous⟩
  have hΓi : Injective Γ := by
    intro z w hzw
    exact hγi (D.toPartialEquiv.injOn (hγsource z) (hγsource w) hzw)
  have hΓd : ∀ z, Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) Γ z) := by
    intro z
    change Injective (mfderiv (𝓡 1) 𝓘(ℝ, RegularLevel.Model E) (D ∘ γ) z)
    rw [mfderiv_comp z (D.mdifferentiableAt (by simp) (hγsource z))
      (hγ.mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv D (hγsource z)).1.comp (hγd z)
  have hcross : (S.data q).surgery.beltSphere v = γ z₀ :=
    ((hsingle z₀ v).mpr ⟨rfl, rfl⟩).symm
  have hvsource : (S.data q).surgery.beltSphere v ∈ D.source := hcross.symm ▸ hγsource z₀
  let β := D ∘ (S.data q).surgery.beltSphere
  have hβ : MDifferentiableAt (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) β v :=
    (D.mdifferentiableAt (by simp) hvsource).comp v
      (((S.data q).belt_smooth hf 4).mdifferentiableAt (by simp))
  have hβcross : β v = Γ z₀ := congrArg D hcross
  have hΓtrans : NativeTransversality.At (𝓡 1) (𝓡 4)
      𝓘(ℝ, RegularLevel.Model E) Γ β z₀ v :=
    (TransverseGerms.native_transversality_partial_diffeomorph_iff D
      (hγ.mdifferentiableAt (by simp))
      (((S.data q).belt_smooth hf 4).mdifferentiableAt (by simp)) hcross (hγsource z₀)).mp
        (fun _ => htrans)
  have hβbasin : ∀ᶠ w in 𝓝 v, Tendsto (fun t => S.flow t (β w).val) atTop (𝓝 q.val) := by
    have hnear := (((S.data q).belt_smooth hf 4).continuous.tendsto v)
      (D.open_source.mem_nhds hvsource)
    filter_upwards [hnear] with w hw
    obtain ⟨t, ht⟩ := horbit ((S.data q).surgery.beltSphere w) hw
    change S.flow t ((S.data q).surgery.beltSphere w).val = (β w).val at ht
    rw [← ht]
    exact (flow_time_atTop_limit_iff S.flow t _ q.val).mpr
      ((S.belt_basin_iff hf q ((S.data q).surgery.beltSphere w)).mpr ⟨w, rfl⟩)
  have hforward (z : Circle) :
      Tendsto (fun t => S.flow t (Γ z).val) atTop (𝓝 q.val) ↔ z = z₀ := by
    obtain ⟨t, ht⟩ := horbit (γ z) (hγsource z)
    change S.flow t (γ z).val = (Γ z).val at ht
    have hbasin : Tendsto (fun s => S.flow s (Γ z).val) atTop (𝓝 q.val) ↔
        γ z ∈ range (S.data q).surgery.beltSphere := by
      rw [← ht]
      exact (flow_time_atTop_limit_iff S.flow t (γ z).val q.val).trans
        (S.belt_basin_iff hf q (γ z))
    rw [hbasin]
    constructor
    · rintro ⟨w, hw⟩
      exact ((hsingle z w).mp hw.symm).1
    · intro hz
      exact ⟨v, ((hsingle z v).mpr ⟨hz, rfl⟩).symm⟩
  have hΓends (z : Circle) : Tendsto (fun t => S.flow t (Γ z).val) atTop (𝓝 p.val) ∨
      Tendsto (fun t => S.flow t (Γ z).val) atTop (𝓝 q.val) := by
    obtain ⟨t, ht⟩ := horbit (γ z) (hγsource z)
    change S.flow t (γ z).val = (Γ z).val at ht
    rw [← ht]
    exact (hendpoints z).imp ((flow_time_atTop_limit_iff S.flow t _ p.val).mpr)
      ((flow_time_atTop_limit_iff S.flow t _ q.val).mpr)
  let δ : C(Hemisphere.Sphere 1, {y : M // f y = a}) :=
    ⟨Γ ∘ standardCircleParametrization, Γ.continuous.comp standardCircleParametrization.continuous⟩
  let z := standardCircleParametrization.symm z₀
  have hz : standardCircleParametrization z = z₀ := standardCircleParametrization.apply_symm_apply z₀
  have hδcross : β v = δ z := by
    change β v = Γ (standardCircleParametrization z)
    rw [hz]
    exact hβcross
  have hδtrans : NativeTransversality.At (𝓡 1) (𝓡 4)
      𝓘(ℝ, RegularLevel.Model E) δ β z v := by
    intro _
    let B : EuclideanSpace ℝ (Fin 4) →L[ℝ] RegularLevel.Model E :=
      mfderiv (𝓡 4) 𝓘(ℝ, RegularLevel.Model E) β v
    apply transverse_comp_standardCircle hΓsmooth B z
    rw [hz]
    exact hΓtrans hβcross
  refine ⟨δ, contMDiff_comp_standardCircle hΓsmooth, injective_comp_standardCircle hΓi,
    injective_derivative_comp_standardCircle hΓsmooth hΓd, z, v, β, hβ, hδcross,
      hδtrans, hβbasin, ?_, fun w => hΓends (standardCircleParametrization w)⟩
  intro w
  change Tendsto (fun t => S.flow t (Γ (standardCircleParametrization w)).val)
    atTop (𝓝 q.val) ↔ _
  rw [hforward]
  exact ⟨fun hw => standardCircleParametrization.injective (hw.trans hz.symm),
    fun hw => hw ▸ hz⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
