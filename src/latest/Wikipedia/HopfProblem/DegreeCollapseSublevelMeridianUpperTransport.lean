import Wikipedia.HopfProblem.DegreeCollapseSublevelEmbeddedMeridian
import Wikipedia.HopfProblem.DegreeCollapseNativeTransversePostcomposition

/-!
# Transport the dual meridian and its native transverse basin germ

The whole constructed sphere reaches the higher level. The original flow
cylinder gives a native partial diffeomorphism on that full image. It
retains embedding, immersion, the transverse belt germ, and both actual
forward endpoint labels without any new level identification.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization MorseCancellation

variable {B : Type} [TopologicalSpace B] (S : CollaredSevenState B)
  {g : S.Space → ℝ} (hg : ContMDiff (𝓡 7) 𝓘(ℝ, ℝ) ∞ g)

theorem exists_transverse_sublevel_meridian_at_higher_cut
    (A : AdaptedSurgeryWindows (Vector 7) g)
    {c : ℝ} (m q : criticalPoints (Vector 7) g)
    (hi : nativeMorseIndex (Vector 7) g q = 2)
    [Fact (Module.finrank ℝ (A.data q).chart.PositiveCoordinates = 4 + 1)]
    (hqc : g q < c)
    (hbefore : ∀ p : criticalPoints (Vector 7) g,
      g p < g q → nativeMorseIndex (Vector 7) g p = 0)
    (hminimum : ∀ p : criticalPoints (Vector 7) g, g p < c →
      nativeMorseIndex (Vector 7) g p = 0 → p = m)
    {a : ℝ} (hupper : A.toSurgeryWindows.upper q ≤ a)
    (ha : ∀ y, g y = a → y ∉ criticalPoints (Vector 7) g)
    (hlow : ∀ p : criticalPoints (Vector 7) g,
      g p ≤ a → nativeMorseIndex (Vector 7) g p ≤ 3) :
    let _ := RegularLevel.chartedSpace hg ha
    ∃ δ : C(Hemisphere.Sphere 2, {y : S.Space // g y = a}),
      ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ δ ∧ IsClosedEmbedding δ ∧
      (∀ z, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) δ z)) ∧
      ∃ (v : sphere (0 : (A.data q).chart.PositiveCoordinates) 1)
        (β : sphere (0 : (A.data q).chart.PositiveCoordinates) 1 →
          {y : S.Space // g y = a}),
        MDifferentiableAt (𝓡 4) 𝓘(ℝ, RegularLevel.Model (Vector 7)) β v ∧
        β v = δ BeltMeridianSphere.pole ∧
        NativeTransversality.At (𝓡 2) (𝓡 4) 𝓘(ℝ, RegularLevel.Model (Vector 7))
          δ β BeltMeridianSphere.pole v ∧
        (∀ᶠ w in 𝓝 v, Tendsto (fun t => A.flow t (β w).val) atTop (𝓝 q.val)) ∧
        (∀ z, Tendsto (fun t => A.flow t (δ z).val) atTop (𝓝 q.val) ↔
          z = BeltMeridianSphere.pole) ∧
        ∀ z, Tendsto (fun t => A.flow t (δ z).val) atTop (𝓝 m.val) ∨
          Tendsto (fun t => A.flow t (δ z).val) atTop (𝓝 q.val) := by
  let _ := RegularLevel.chartedSpace hg (A.data q).upper_regular
  let _ := RegularLevel.chartedSpace hg ha
  let _ := RegularLevel.isManifold hg (A.data q).upper_regular
  let _ := RegularLevel.isManifold hg ha
  obtain ⟨v, s, hs, hs0, L, γ, hγ, hγi, hγd, _, hcount, htrans, hreach, hforward, hendpoints⟩ :=
    S.exists_embedded_transverse_sublevel_meridian hg A m q hi hqc hbefore hminimum
      hupper ha hlow
  obtain ⟨t₀, ht₀⟩ := hreach BeltMeridianSphere.pole
  let za : {y : S.Space // g y = a} :=
    ⟨A.flow t₀ (γ BeltMeridianSphere.pole).val, ht₀⟩
  obtain ⟨D, hsource, _, horbit⟩ := A.exists_native_level_basin_transport hg
    (A.data q).upper_regular ha (γ BeltMeridianSphere.pole) za
  have hγsource (z : Hemisphere.Sphere 2) : γ z ∈ D.source := hsource.symm ▸ hreach z
  have hδsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ (D ∘ γ) := by
    intro z
    exact (D.contMDiffOn_toFun.contMDiffAt (D.open_source.mem_nhds (hγsource z))).comp z
      hγ.contMDiffAt
  let δ : C(Hemisphere.Sphere 2, {y : S.Space // g y = a}) :=
    ⟨D ∘ γ, hδsmooth.continuous⟩
  have hδi : Injective δ := by
    intro z w hzw
    exact hγi.injective (D.toPartialEquiv.injOn (hγsource z) (hγsource w) hzw)
  have hδd (z : Hemisphere.Sphere 2) :
      Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) δ z) := by
    change Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) (D ∘ γ) z)
    rw [mfderiv_comp z (D.mdifferentiableAt (by simp) (hγsource z))
      (hγ.mdifferentiableAt (by simp))]
    exact (PartialChart.bijective_mfderiv D (hγsource z)).1.comp (hγd z)
  have hcross : (A.data q).surgery.beltSphere v = γ BeltMeridianSphere.pole :=
    ((hcount BeltMeridianSphere.pole v).mpr ⟨rfl, rfl⟩).symm
  have hvsource : (A.data q).surgery.beltSphere v ∈ D.source :=
    hcross.symm ▸ hγsource BeltMeridianSphere.pole
  let β := D ∘ (A.data q).surgery.beltSphere
  have hβ : MDifferentiableAt (𝓡 4) 𝓘(ℝ, RegularLevel.Model (Vector 7)) β v :=
    (D.mdifferentiableAt (by simp) hvsource).comp v
      (((A.data q).belt_smooth hg 4).mdifferentiableAt (by simp))
  have hβcross : β v = δ BeltMeridianSphere.pole := congrArg D hcross
  have hδtrans : NativeTransversality.At (𝓡 2) (𝓡 4)
      𝓘(ℝ, RegularLevel.Model (Vector 7)) δ β BeltMeridianSphere.pole v :=
    (TransverseGerms.native_transversality_partial_diffeomorph_iff D
      (hγ.mdifferentiableAt (by simp))
      (((A.data q).belt_smooth hg 4).mdifferentiableAt (by simp)) hcross
      (hγsource BeltMeridianSphere.pole)).mp (fun _ => htrans)
  have hβbasin : ∀ᶠ w in 𝓝 v, Tendsto (fun t => A.flow t (β w).val) atTop (𝓝 q.val) := by
    have hnear := (((A.data q).belt_smooth hg 4).continuous.tendsto v)
      (D.open_source.mem_nhds hvsource)
    filter_upwards [hnear] with w hw
    obtain ⟨t, ht⟩ := horbit ((A.data q).surgery.beltSphere w) hw
    change A.flow t ((A.data q).surgery.beltSphere w).val = (β w).val at ht
    rw [← ht]
    exact (flow_time_atTop_limit_iff A.flow t _ q.val).mpr
      ((A.belt_basin_iff hg q ((A.data q).surgery.beltSphere w)).mpr ⟨w, rfl⟩)
  have hδforward (z : Hemisphere.Sphere 2) :
      Tendsto (fun t => A.flow t (δ z).val) atTop (𝓝 q.val) ↔
        z = BeltMeridianSphere.pole := by
    obtain ⟨t, ht⟩ := horbit (γ z) (hγsource z)
    change A.flow t (γ z).val = (δ z).val at ht
    rw [← ht]
    exact (flow_time_atTop_limit_iff A.flow t (γ z).val q.val).trans (hforward z)
  refine ⟨δ, hδsmooth, δ.continuous.isClosedEmbedding hδi, hδd, v, β, hβ, hβcross,
    hδtrans, hβbasin, hδforward, ?_⟩
  intro z
  obtain ⟨t, ht⟩ := horbit (γ z) (hγsource z)
  change A.flow t (γ z).val = (δ z).val at ht
  rw [← ht]
  exact (hendpoints z).imp ((flow_time_atTop_limit_iff A.flow t _ m.val).mpr)
    ((flow_time_atTop_limit_iff A.flow t _ q.val).mpr)

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
