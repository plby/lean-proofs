import Wikipedia.HopfProblem.DegreeCollapseSmoothTransitionDerivative
import Wikipedia.SmoothSixDPoincare.SupportedIsotopyExtension

/-!
# Constructed supported motion along the whole native tube

The scalar profile, transverse cutoff, compact support, crossing time, and
global native isotopy are constructed from the actual open tube source.
Every real-time slice is a diffeomorphism. The chart formula and source
preservation hold for all real times, including the unique transverse
passage of the center through longitudinal coordinate one.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {V E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]

structure LongitudinalTubeMotion
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞) where
  profile : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞
  cutoff : V → ℝ
  cutoff_smooth : ContDiff ℝ ∞ cutoff
  cutoff_germ : cutoff =ᶠ[𝓝 (0 : V)] fun _ => 1
  cutoff_zero : cutoff 0 = 1
  destination : ℝ
  destination_gt_one : 1 < destination
  profile_zero : profile 0 = destination
  profile_germ : (profile : ℝ → ℝ) =ᶠ[𝓝 (0 : ℝ)] fun s => s + destination
  time : ℝ
  time_mem : time ∈ Ioo (0 : ℝ) 1
  time_value : Real.smoothTransition time * destination = 1
  time_rate : 0 < deriv Real.smoothTransition time * destination
  unique_time : ∀ t ∈ Icc (0 : ℝ) 1,
    Real.smoothTransition t * destination = 1 ↔ t = time
  family : ℝ × M → M
  support : Set M
  compact_support : IsCompact support
  support_subset : support ⊆ Φ.target
  smooth : ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ family
  zero : ∀ y, family (0, y) = y
  slices : ∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, d y = family (t, y)
  fixedOutside : ∀ t y, y ∉ support → family (t, y) = y
  model_source : ∀ t z, z ∈ Φ.source →
    longitudinalBlend profile cutoff Real.smoothTransition (t, z) ∈ Φ.source
  formula : ∀ t z, z ∈ Φ.source →
    family (t, Φ z) = Φ (longitudinalBlend profile cutoff Real.smoothTransition (t, z))

variable [FiniteDimensional ℝ V] [T2Space M]

theorem nonempty_longitudinalTubeMotion
    (Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞)
    (haxis : Icc (0 : ℝ) 1 ×ˢ {(0 : V)} ⊆ Φ.source) :
    Nonempty (LongitudinalTubeMotion Φ) := by
  obtain ⟨l, u, r, hl, hu, hr, hbox⟩ := exists_tube_support_box Φ haxis
  let c : ℝ := (1 + u) / 2
  have hc : 1 < c := by dsimp only [c]; linarith
  have hcpos : 0 < c := zero_lt_one.trans hc
  have hcu : c < u := by dsimp only [c]; linarith
  have h0I : (0 : ℝ) ∈ Ioo l u := ⟨hl, zero_lt_one.trans hu⟩
  have hcI : c ∈ Ioo l u := ⟨hl.trans hcpos, hcu⟩
  obtain ⟨D, hDfix, hDgerm, hD0, -, hDpos⟩ :=
    MorseRearrangement.exists_increasing_interval_translation h0I hcI
  let β : ContDiffBump (0 : V) := {
    rIn := r / 2
    rOut := r
    rIn_pos := half_pos hr
    rIn_lt_rOut := half_lt_self hr }
  have hβgerm : (β : V → ℝ) =ᶠ[𝓝 (0 : V)] fun _ => 1 := by
    filter_upwards [ball_mem_nhds (0 : V) β.rIn_pos] with z hz
    exact β.one_of_mem_closedBall (ball_subset_closedBall hz)
  have hβrange : ∀ z : V, β z ∈ Icc (0 : ℝ) 1 := fun _ => ⟨β.nonneg, β.le_one⟩
  have hηrange : ∀ t : ℝ, Real.smoothTransition t ∈ Icc (0 : ℝ) 1 :=
    fun t => ⟨Real.smoothTransition.nonneg t, Real.smoothTransition.le_one t⟩
  have hmodel := longitudinalBlend_smooth D.contMDiff.contDiff β.contDiff
    (Real.smoothTransition.contDiff (n := ⊤))
  have hsource : Icc l u ×ˢ tsupport (β : V → ℝ) ⊆ Φ.source := by
    rw [β.tsupport_eq]
    exact hbox
  obtain ⟨F, K, hK, hKΦ, hF, hF0, hFd, hFfix, hsrc, hformula⟩ :=
    exists_supported_isotopy_extension Φ hmodel
      (longitudinalBlend_zero Real.smoothTransition.zero)
      (longitudinalBlend_slices D.contMDiff.contDiff β.contDiff β.hasCompactSupport
        hDpos hDfix hβrange hηrange)
      (isCompact_Icc.prod β.hasCompactSupport.isCompact) hsource
      (longitudinalBlend_fixed_outside Real.smoothTransition hDfix)
  have hcInv : 1 / c ∈ Ioo (0 : ℝ) 1 :=
    ⟨one_div_pos.mpr hcpos, (div_lt_one hcpos).mpr hc⟩
  obtain ⟨τ, hτ, hτvalue, hτrate, hτunique⟩ := exists_unique_smoothTransition_time hcInv
  refine ⟨{
    profile := D
    cutoff := β
    cutoff_smooth := β.contDiff
    cutoff_germ := hβgerm
    cutoff_zero := hβgerm.self_of_nhds
    destination := c
    destination_gt_one := hc
    profile_zero := hD0
    profile_germ := by simpa only [sub_zero] using hDgerm
    time := τ
    time_mem := hτ
    time_value := (eq_div_iff hcpos.ne').mp hτvalue
    time_rate := mul_pos hτrate hcpos
    unique_time := ?_
    family := F
    support := K
    compact_support := hK
    support_subset := hKΦ
    smooth := hF
    zero := hF0
    slices := hFd
    fixedOutside := hFfix
    model_source := hsrc
    formula := hformula }⟩
  intro t ht
  rw [← eq_div_iff hcpos.ne']
  exact hτunique t ht

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
