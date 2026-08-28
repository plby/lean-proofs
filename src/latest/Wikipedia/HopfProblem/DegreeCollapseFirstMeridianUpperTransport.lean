import Wikipedia.HopfProblem.DegreeCollapseFirstMeridianBetweenCuts
import Wikipedia.HopfProblem.DegreeCollapseNativeTransversePostcomposition

/-!
# The actual embedded meridian and transverse basin sheet in the higher native level

The original whole-level flow cylinder transports the constructed sphere
point by point. Its native derivative is an isomorphism, so embedding,
immersion, and the original belt transversality survive. The transported
belt germ lies in the actual complete forward basin. Every other sphere
point still crosses the original zero level.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation

variable {B : Type} [TopologicalSpace B] [SimplyConnectedSpace B] {S : CollaredSevenState B}
  (P : S.ExcellentMorsePresentation)

theorem exists_transverse_first_meridian_at_higher_cut
    (A : AdaptedSurgeryWindows (Vector 7) P.function)
    (q : criticalPoints (Vector 7) P.function)
    (hi : nativeMorseIndex (Vector 7) P.function q = 2)
    [Fact (Module.finrank ℝ (A.data q).chart.PositiveCoordinates = 4 + 1)]
    (hfirst : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
      P.function q ≤ P.function p)
    (hlower : 0 ≤ A.toSurgeryWindows.lower q)
    {a : ℝ} (hupper : A.toSurgeryWindows.upper q ≤ a)
    (ha : ∀ y, P.function y = a → y ∉ criticalPoints (Vector 7) P.function)
    (hlow : ∀ p : criticalPoints (Vector 7) P.function, 0 < P.function p →
      P.function p ≤ a → nativeMorseIndex (Vector 7) P.function p ≤ 3) :
    let _ := RegularLevel.chartedSpace P.smooth ha
    ∃ δ : C(Hemisphere.Sphere 2, {y : S.Space // P.function y = a}),
      ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ δ ∧ IsClosedEmbedding δ ∧
      (∀ z, Injective (mfderiv (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) δ z)) ∧
      ∃ (v : sphere (0 : (A.data q).chart.PositiveCoordinates) 1)
        (β : sphere (0 : (A.data q).chart.PositiveCoordinates) 1 →
          {y : S.Space // P.function y = a}),
        MDifferentiableAt (𝓡 4) 𝓘(ℝ, RegularLevel.Model (Vector 7)) β v ∧
        β v = δ BeltMeridianSphere.pole ∧
        NativeTransversality.At (𝓡 2) (𝓡 4) 𝓘(ℝ, RegularLevel.Model (Vector 7))
          δ β BeltMeridianSphere.pole v ∧
        (∀ᶠ w in 𝓝 v, Tendsto (fun t => A.flow t (β w).val) atTop (𝓝 q.val)) ∧
        (∀ z, Tendsto (fun t => A.flow t (δ z).val) atTop (𝓝 q.val) ↔
          z = BeltMeridianSphere.pole) ∧
        (∀ z, (δ z).val ∈ FlowCancellation.levelBasin A.flow P.function 0 ↔
          z ≠ BeltMeridianSphere.pole) ∧
        ∀ z, ∀ r : criticalPoints (Vector 7) P.function, 0 ≤ P.function r →
          Tendsto (fun t => A.flow t (δ z).val) atTop (𝓝 r.val) → r = q := by
  let _ := RegularLevel.chartedSpace P.smooth (A.data q).upper_regular
  let _ := RegularLevel.chartedSpace P.smooth ha
  let _ := RegularLevel.isManifold P.smooth (A.data q).upper_regular
  let _ := RegularLevel.isManifold P.smooth ha
  obtain ⟨v, s, hs, hs0, L, γ, hγ, hγi, hγd, _, hcount, htrans, hreach, hforward, hzero⟩ :=
    P.exists_embedded_transverse_first_meridian_between_cuts A q hi hfirst hlower hupper ha hlow
  obtain ⟨t₀, ht₀⟩ := hreach BeltMeridianSphere.pole
  let za : {y : S.Space // P.function y = a} :=
    ⟨A.flow t₀ (γ BeltMeridianSphere.pole).val, ht₀⟩
  obtain ⟨D, hsource, _, horbit⟩ := A.exists_native_level_basin_transport P.smooth
    (A.data q).upper_regular ha (γ BeltMeridianSphere.pole) za
  have hγsource (z : Hemisphere.Sphere 2) : γ z ∈ D.source := hsource.symm ▸ hreach z
  have hδsmooth : ContMDiff (𝓡 2) 𝓘(ℝ, RegularLevel.Model (Vector 7)) ∞ (D ∘ γ) := by
    intro z
    exact (D.contMDiffOn_toFun.contMDiffAt (D.open_source.mem_nhds (hγsource z))).comp z
      hγ.contMDiffAt
  let δ : C(Hemisphere.Sphere 2, {y : S.Space // P.function y = a}) :=
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
      (((A.data q).belt_smooth P.smooth 4).mdifferentiableAt (by simp))
  have hβcross : β v = δ BeltMeridianSphere.pole := congrArg D hcross
  have hδtrans : NativeTransversality.At (𝓡 2) (𝓡 4)
      𝓘(ℝ, RegularLevel.Model (Vector 7)) δ β BeltMeridianSphere.pole v :=
    (TransverseGerms.native_transversality_partial_diffeomorph_iff D
      (hγ.mdifferentiableAt (by simp))
      (((A.data q).belt_smooth P.smooth 4).mdifferentiableAt (by simp)) hcross
      (hγsource BeltMeridianSphere.pole)).mp (fun _ => htrans)
  have hβbasin : ∀ᶠ w in 𝓝 v, Tendsto (fun t => A.flow t (β w).val) atTop (𝓝 q.val) := by
    have hnear := (((A.data q).belt_smooth P.smooth 4).continuous.tendsto v)
      (D.open_source.mem_nhds hvsource)
    filter_upwards [hnear] with w hw
    obtain ⟨t, ht⟩ := horbit ((A.data q).surgery.beltSphere w) hw
    change A.flow t ((A.data q).surgery.beltSphere w).val = (β w).val at ht
    rw [← ht]
    exact (flow_time_atTop_limit_iff A.flow t _ q.val).mpr
      ((A.belt_basin_iff P.smooth q ((A.data q).surgery.beltSphere w)).mpr ⟨w, rfl⟩)
  have hδforward (z : Hemisphere.Sphere 2) :
      Tendsto (fun t => A.flow t (δ z).val) atTop (𝓝 q.val) ↔
        z = BeltMeridianSphere.pole := by
    obtain ⟨t, ht⟩ := horbit (γ z) (hγsource z)
    change A.flow t (γ z).val = (δ z).val at ht
    rw [← ht]
    exact (flow_time_atTop_limit_iff A.flow t (γ z).val q.val).trans (hforward z)
  have hδzero (z : Hemisphere.Sphere 2) :
      (δ z).val ∈ FlowCancellation.levelBasin A.flow P.function 0 ↔
        z ≠ BeltMeridianSphere.pole := by
    obtain ⟨t, ht⟩ := horbit (γ z) (hγsource z)
    change A.flow t (γ z).val = (δ z).val at ht
    rw [← ht]
    exact (FlowCancellation.levelBasin_flow_iff A.flow P.function 0 t (γ z).val).trans (hzero z)
  refine ⟨δ, hδsmooth, δ.continuous.isClosedEmbedding hδi, hδd, v, β, hβ, hβcross,
    hδtrans, hβbasin, hδforward, hδzero, ?_⟩
  intro z r hr hlim
  by_cases hz : z = BeltMeridianSphere.pole
  · exact Subtype.ext (tendsto_nhds_unique hlim ((hδforward z).mpr hz))
  · have hbad : (δ z).val ∈ (FlowCancellation.levelBasin A.flow P.function 0)ᶜ := by
      rw [levelBasin_compl_eq_endpoint_obstruction A P.smooth
        (RegularTimeMorse.regular_zero_not_critical P.regular)]
      exact Or.inl ⟨r, hr, hlim⟩
    exact (hbad ((hδzero z).mpr hz)).elim

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
