import Wikipedia.HopfProblem.DegreeCollapseSurgeryFlowBandBridge
import Wikipedia.HopfProblem.DegreeCollapseSurgeryPairBands
import Wikipedia.HopfProblem.DegreeCollapseNativeLevelIsotopyRealization
import Wikipedia.HopfProblem.DegreeCollapseWholeLevelConnectionRealization
import Wikipedia.SmoothSixDPoincare.MorseBeltIntersectionReduction

/-!
# Removing every actual connection at zero signed attaching count

Finite Whitney reduction makes the actual attaching and belt images disjoint.
The corresponding native level isotopy is realized in the common complete
flow. Whole basin identities then exclude every complete trajectory from
the selected upper critical point to the lower one. The original function,
critical points, strict descent, and all critical field germs are retained.
Rearranging their critical values is a separate, still outstanding step.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.remove_connections_of_zero_count
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hdim : Module.finrank ℝ E = 6) (p q : criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (hindex : Module.finrank ℝ (S.data p).chart.NegativeCoordinates = 2)
    (hindex' : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 3)
    (hnull : ∀ γ : C(Hemisphere.Sphere 1, (S.data p).LowerLevel),
      ∃ z, γ.Homotopic (ContinuousMap.const _ z))
    (r : (ℝ × (S.data p).chart.NegativeCoordinates) ≃L[ℝ] Hemisphere.Ambient 3) :
    letI := RegularLevel.chartedSpace hf (S.data p).upper_regular
    letI := RegularLevel.chartedSpace hf (S.data q).lower_regular
    letI : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) := ⟨hindex'⟩
    ∀ b : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        (S.data p).UpperLevel (S.data q).LowerLevel ∞,
      (∀ x : (S.data p).UpperLevel, ∃ t, S.flow t x = (b x : M)) →
      ∀ e₀ : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
          (S.data p).UpperLevel (S.data p).UpperLevel ∞,
        IsotopicToIdentity e₀ → ∀ g₀ : C(Hemisphere.Sphere 2, (S.data p).UpperLevel),
          (∀ x, g₀ x = e₀ ((S.data p).transportedAttachingSphere (S.data q) 2 b.toHomeomorph x)) →
          ∀ hgood : (S.data p).IsTransverseBeltSphere hf hdim hindex g₀,
            (S.data p).beltIntersectionCount 2 r g₀
              ((S.data p).finite_points_of_isTransverseBeltSphere hf hdim hindex hgood) = 0 →
            ∃ (V : (z : M) → TangentSpace 𝓘(ℝ, E) z) (G : Flow ℝ M),
              ContMDiff 𝓘(ℝ, E) (𝓘(ℝ, E).tangent) ∞
                (fun z => (⟨z, V z⟩ : TangentBundle 𝓘(ℝ, E) M)) ∧
              (∀ z, IsMIntegralCurve (fun t => G t z) V) ∧
              (∀ z ∈ criticalPoints E f, V z = 0) ∧
              (∀ z, z ∉ criticalPoints E f → mvfderiv 𝓘(ℝ, E) f z (V z) < 0) ∧
              (∀ z ∈ criticalPoints E f, ∀ᶠ y in 𝓝 z, V y = S.field y) ∧
              ∀ z, ¬(Tendsto (fun t => G t z) atBot (𝓝 q.val) ∧
                Tendsto (fun t => G t z) atTop (𝓝 p.val)) := by
  let _ := RegularLevel.chartedSpace hf (S.data p).upper_regular
  let _ := RegularLevel.chartedSpace hf (S.data q).lower_regular
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 2 + 1) := ⟨hindex'⟩
  intro b horbit e₀ he₀ g₀ heq₀ hgood hcount
  obtain ⟨e₁, g₁, he₁, heq₁, -, hdisjoint⟩ :=
    (S.data p).exists_disjoint_belt_sphere_of_zero_count hf hdim hindex hnull r g₀ hgood hcount
  let e := e₀.trans e₁
  have he : IsotopicToIdentity e := he₀.trans he₁
  have heq (u : Hemisphere.Sphere 2) : g₁ u =
      e ((S.data p).transportedAttachingSphere (S.data q) 2 b.toHomeomorph u) :=
    (heq₁ u).trans (congrArg e₁ (heq₀ u))
  have hbasins : ∀ x : (S.data p).UpperLevel,
      ¬(Tendsto (fun t => S.flow t x) atBot (𝓝 q.val) ∧
        Tendsto (fun t => S.flow t (e x)) atTop (𝓝 p.val)) := by
    rintro x ⟨hxq, hxp⟩
    obtain ⟨v, hv⟩ :=
      (S.transported_attaching_basin_iff hf p q 2 b.toHomeomorph horbit x).mp hxq
    have hB := (S.belt_basin_iff hf p (e x)).mp hxp
    have hg : e x ∈ range g₁ := ⟨v, (heq v).trans (congrArg e hv)⟩
    exact Set.disjoint_left.mp hdisjoint hg hB
  have hpc : f p < f p + (S.data p).radius ^ 2 := S.toSurgeryWindows.value_lt_upper p
  have hqc : f p + (S.data p).radius ^ 2 < f q :=
    (S.separated p q hpq).trans (S.toSurgeryWindows.lower_lt_value q)
  obtain ⟨a, hpa, hac⟩ := exists_between hpc
  obtain ⟨b', hcb, hbq⟩ := exists_between hqc
  let z : (S.data p).UpperLevel := g₀ (Classical.arbitrary (Hemisphere.Sphere 2))
  obtain ⟨_, _, _, V, H, G, -, -, -, -, -, -, hgeometry, hV, hG,
      hzeros, hneg, hgerms, -, hend, -, hleft, hright⟩ :=
    FlowSuspension.exists_native_regular_level_isotopy_realization hf S.smooth S.descent
      S.flow S.integral hac hcb
      (surgery_pair_inner_band_regular S.toSurgeryWindows p q hconsecutive hpa hbq)
      (S.data p).upper_regular z e he
  obtain ⟨hback, hforward⟩ := FlowSuspension.whole_level_basins_of_holonomy S.flow H G
    Subtype.val e (fun x => (hgeometry x).2.1) (fun x => (hgeometry x).2.2)
    hend hleft hright
  refine ⟨V, G, hV, hG, fun x hx => (hzeros x).mpr (S.zero x hx), hneg, hgerms, ?_⟩
  exact FlowSuspension.no_connection_of_level_basin_disjointness S.flow G hf.continuous hqc hpc e
    (fun x => hback x q.val) (fun x => hforward x p.val) hbasins

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
