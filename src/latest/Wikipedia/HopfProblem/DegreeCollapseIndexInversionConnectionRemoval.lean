import Wikipedia.HopfProblem.DegreeCollapseAmbientDimensionalAvoidance
import Wikipedia.HopfProblem.DegreeCollapseZeroCountConnectionRemoval
import Wikipedia.SmoothSixDPoincare.MorseAttachingTransport

/-!
# Removing connections for a nonincreasing critical-index pair

For nonempty attaching and belt spheres, the index inequality makes their
total dimension strictly smaller than the actual regular level. Constructed
ambient avoidance and native level-isotopy realization then remove every
selected connection. No signed count or lower-level circle contraction is
needed. The original function and every critical field germ are retained.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.remove_connections_of_index_le
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p q : criticalPoints E f) (hpq : f p < f q)
    (hconsecutive : ∀ r : criticalPoints E f, ¬(f p < f r ∧ f r < f q))
    (n m : ℕ)
    (hqindex : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = n + 1)
    (hppos : Module.finrank ℝ (S.data p).chart.PositiveCoordinates = m + 1)
    (hle : Module.finrank ℝ (S.data q).chart.NegativeCoordinates ≤
      Module.finrank ℝ (S.data p).chart.NegativeCoordinates) :
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
  let _ := RegularLevel.isManifold hf (S.data p).upper_regular
  let _ : CompactSpace (S.data p).UpperLevel :=
    isCompact_iff_compactSpace.mp (isClosed_eq hf.continuous continuous_const).isCompact
  let _ : Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = n + 1) := ⟨hqindex⟩
  let _ : Fact (Module.finrank ℝ (S.data p).chart.PositiveCoordinates = m + 1) := ⟨hppos⟩
  obtain ⟨D, b, -, hb, horbit⟩ := S.exists_orbit_bandBridge hf p q hpq hconsecutive
  have horbit' (x : (S.data p).UpperLevel) : ∃ t, S.flow t x = (b x : M) := by
    obtain ⟨t, ht⟩ := horbit x
    exact ⟨t, ht.trans (hb x).symm⟩
  let α := (S.data p).transportedAttachingSphere (S.data q) n b.toHomeomorph
  have hα : ContMDiff (𝓡 n) 𝓘(ℝ, RegularLevel.Model E) ∞ α :=
    (S.data p).transportedAttachingSphere_smooth (S.data q) hf n b
  have hB := (S.data p).belt_smooth hf m
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) +
      Module.finrank ℝ (EuclideanSpace ℝ (Fin m)) < Module.finrank ℝ (RegularLevel.Model E) := by
    simp only [RegularLevel.Model, finrank_euclideanSpace, Fintype.card_fin]
    have hh := (S.data p).chart.finrank_negative_add_positive
    omega
  obtain ⟨e, he, hdisjoint⟩ :=
    MorseRearrangement.exists_ambient_disjoint_diffeomorph_of_dimension hα hB hdim
  have hbasins : ∀ x : (S.data p).UpperLevel,
      ¬(Tendsto (fun t => S.flow t x) atBot (𝓝 q.val) ∧
        Tendsto (fun t => S.flow t (e x)) atTop (𝓝 p.val)) := by
    rintro x ⟨hxq, hxp⟩
    obtain ⟨v, hv⟩ :=
      (S.transported_attaching_basin_iff hf p q n b.toHomeomorph horbit' x).mp hxq
    have hB := (S.belt_basin_iff hf p (e x)).mp hxp
    have hαx : e x ∈ range (e ∘ α) := ⟨v, congrArg e hv⟩
    exact disjoint_left.mp hdisjoint hαx hB
  have hpc : f p < f p + (S.data p).radius ^ 2 := S.toSurgeryWindows.value_lt_upper p
  have hqc : f p + (S.data p).radius ^ 2 < f q :=
    (S.separated p q hpq).trans (S.toSurgeryWindows.lower_lt_value q)
  obtain ⟨a, hpa, hac⟩ := exists_between hpc
  obtain ⟨b', hcb, hbq⟩ := exists_between hqc
  let z : (S.data p).UpperLevel := α (Classical.arbitrary (Hemisphere.Sphere n))
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
