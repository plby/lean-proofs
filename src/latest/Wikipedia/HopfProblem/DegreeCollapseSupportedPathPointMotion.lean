import Wikipedia.HopfProblem.DegreeCollapseSupportedIsotopyAlgebra
import Wikipedia.HopfProblem.DegreeCollapseLinearTimeBumpIsotopy
import Wikipedia.HopfProblem.DegreeCollapsePathPointIsotopy

/-!
# Native point transport along a path with uniform compact support

Local cutoff translations retain one compact support for their whole
real-time family. The resulting orbit and its complement are open in the
prescribed region. Preconnectedness then transports points along any path
inside that region, retaining a supported smooth isotopy.
-/

noncomputable section

open Set Function Filter Metric
open scoped ContDiff Manifold Topology
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  [J.Boundaryless] [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold J ∞ M] [T2Space M]

theorem exists_open_compactly_supported_point_motion
    {U : Set M} (hU : IsOpen U) {x : M} (hx : x ∈ U) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∀ y ∈ V,
      ∃ (d : Diffeomorph J J M M ∞) (K : Set M),
        IsCompact K ∧ K ⊆ U ∧ Nonempty (SupportedRelativeIsotopy d K ∅) ∧ d x = y := by
  let c := NoExoticSixSphere.modelChartPartialDiffeomorph (I := J) x
  let Φ := PartialChart.restrictTarget c.symm hU
  have hxc : x ∈ c.source := mem_extChartAt_source x
  have hcx : c.symm (c x) = x := c.left_inv' hxc
  have hxΦ : c x ∈ Φ.source := by
    refine ⟨c.map_source' hxc, ?_⟩
    change c.symm (c x) ∈ U
    rw [hcx]
    exact hx
  have hΦx : Φ (c x) = x := hcx
  obtain ⟨β, hβsupport, hβcompact, hβsmooth, -, hβx⟩ :=
    exists_contDiff_tsupport_subset (n := ⊤) (Φ.open_source.mem_nhds hxΦ)
  obtain ⟨δ, hδ, hmove⟩ :=
    exists_small_linear_time_bump_isotopy Φ hβsmooth hβcompact hβsupport
  obtain ⟨ρ, hρ, hρsource⟩ := Metric.mem_nhds_iff.mp (Φ.open_source.mem_nhds hxΦ)
  let ε := min δ ρ
  have hε : 0 < ε := lt_min hδ hρ
  have hball : ball (c x) ε ⊆ Φ.source :=
    (ball_subset_ball (min_le_right _ _)).trans hρsource
  refine ⟨Φ '' ball (c x) ε,
    Φ.toOpenPartialHomeomorph.isOpen_image_of_subset_source isOpen_ball hball,
    ⟨c x, mem_ball_self hε, hΦx⟩, ?_, ?_⟩
  · rintro _ ⟨v, hv, rfl⟩
    exact (Φ.map_source' (hball hv)).2
  · rintro _ ⟨v, hv, rfl⟩
    have hnear : ‖v - c x‖ < δ := by
      simpa only [dist_eq_norm] using
        (show dist v (c x) < min δ ρ from hv).trans_le (min_le_left _ _)
    obtain ⟨A, K, hK, hKt, hA, hzero, hdiff, hfix, -, hformula⟩ :=
      hmove (v - c x) hnear
    obtain ⟨d, hd⟩ := hdiff 1
    refine ⟨d, K, hK, fun z hz => (hKt hz).2, ⟨{
      family := A
      smooth := hA
      zero := hzero
      one := fun z => (hd z).symm
      slices := hdiff
      fixedOutside := hfix
      fixedOn := fun _ _ hz => False.elim hz }⟩, ?_⟩
    have hend := hformula 1 (right_mem_Icc.mpr zero_le_one) (c x) hxΦ
    rw [hβx, one_mul, one_smul] at hend
    have hsum : c x + (v - c x) = v := by abel
    rw [hsum, hΦx] at hend
    exact (hd x).trans hend

def supportedPointOrbit (J : ModelWithCorners ℝ E H) (U : Set M) (x : M) : Set M :=
  {y | y ∈ U ∧ ∃ (d : Diffeomorph J J M M ∞) (K : Set M),
    IsCompact K ∧ K ⊆ U ∧ Nonempty (SupportedRelativeIsotopy d K ∅) ∧ d x = y}

theorem isOpen_supportedPointOrbit {U : Set M} (hU : IsOpen U) (x : M) :
    IsOpen (supportedPointOrbit J U x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyU, d, K, hK, hKU, ⟨A⟩, hdx⟩
  obtain ⟨V, hV, hyV, hVU, hmove⟩ :=
    exists_open_compactly_supported_point_motion (J := J) hU hyU
  apply mem_of_superset (hV.mem_nhds hyV)
  intro z hz
  obtain ⟨e, L, hL, hLU, ⟨B⟩, hey⟩ := hmove z hz
  refine ⟨hVU hz, d.trans e, K ∪ L, hK.union hL, union_subset hKU hLU,
    ⟨SupportedGerms.compose_supported_relative_isotopies A B⟩, ?_⟩
  change e (d x) = z
  rw [hdx, hey]

theorem isOpen_sdiff_supportedPointOrbit {U : Set M} (hU : IsOpen U) (x : M) :
    IsOpen (U \ supportedPointOrbit J U x) := by
  rw [isOpen_iff_mem_nhds]
  rintro y ⟨hyU, hyOrbit⟩
  obtain ⟨V, hV, hyV, hVU, hmove⟩ :=
    exists_open_compactly_supported_point_motion (J := J) hU hyU
  apply mem_of_superset (hV.mem_nhds hyV)
  intro z hz
  refine ⟨hVU hz, ?_⟩
  rintro ⟨_, d, K, hK, hKU, ⟨A⟩, hdx⟩
  obtain ⟨e, L, hL, hLU, ⟨B⟩, hey⟩ := hmove z hz
  apply hyOrbit
  refine ⟨hyU, d.trans e.symm, K ∪ L, hK.union hL, union_subset hKU hLU,
    ⟨SupportedGerms.compose_supported_relative_isotopies A
      (SupportedGerms.inverse_supported_relative_isotopy B)⟩, ?_⟩
  change e.symm (d x) = y
  rw [hdx, ← hey, e.symm_apply_apply]

theorem exists_compactly_supported_point_motion_of_preconnected
    {U A : Set M} (hU : IsOpen U) (hA : IsPreconnected A) (hAU : A ⊆ U)
    {x y : M} (hx : x ∈ A) (hy : y ∈ A) :
    ∃ (d : Diffeomorph J J M M ∞) (K : Set M),
      IsCompact K ∧ K ⊆ U ∧ Nonempty (SupportedRelativeIsotopy d K ∅) ∧ d x = y := by
  have hxOrbit : x ∈ supportedPointOrbit J U x := by
    refine ⟨hAU hx, Diffeomorph.refl J M ∞, ∅, isCompact_empty, empty_subset _, ⟨{
      family := Prod.snd
      smooth := contMDiff_snd
      zero := fun _ => rfl
      one := fun _ => rfl
      slices := fun _ => ⟨Diffeomorph.refl J M ∞, fun _ => rfl⟩
      fixedOutside := fun _ _ _ => rfl
      fixedOn := fun _ _ _ => rfl }⟩, rfl⟩
  have hcover : A ⊆ supportedPointOrbit J U x ∪ (U \ supportedPointOrbit J U x) := by
    intro z hz
    by_cases hh : z ∈ supportedPointOrbit J U x
    · exact Or.inl hh
    · exact Or.inr ⟨hAU hz, hh⟩
  have hdisjoint : Disjoint (supportedPointOrbit J U x) (U \ supportedPointOrbit J U x) := by
    rw [Set.disjoint_left]
    exact fun _ hz hw => hw.2 hz
  have hsub := hA.subset_left_of_subset_union (isOpen_supportedPointOrbit hU x)
    (isOpen_sdiff_supportedPointOrbit hU x) hdisjoint hcover ⟨x, hx, hxOrbit⟩
  exact (hsub hy).2

theorem exists_compactly_supported_point_motion_of_path {U : Set M} (hU : IsOpen U)
    {x y : M} (γ : Path x y) (hγ : ∀ t, γ t ∈ U) :
    ∃ (d : Diffeomorph J J M M ∞) (K : Set M),
      IsCompact K ∧ K ⊆ U ∧ Nonempty (SupportedRelativeIsotopy d K ∅) ∧ d x = y := by
  apply exists_compactly_supported_point_motion_of_preconnected (J := J) hU
    (isConnected_range γ.continuous).isPreconnected
    (show range γ ⊆ U from by rintro _ ⟨t, rfl⟩; exact hγ t)
  · exact ⟨0, γ.source⟩
  · exact ⟨1, γ.target⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
