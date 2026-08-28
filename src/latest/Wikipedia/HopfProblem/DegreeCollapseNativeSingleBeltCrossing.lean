import Wikipedia.HopfProblem.DegreeCollapseSingleBeltCrossingModel

/-!
# Construct a supported native isotopy with one transverse belt crossing

The cutoff, positive sheet height, global native diffeomorphisms, and
compact support are constructed inside any native chart about the belt
point. The entire moving sheet meets the local belt exactly once, at time
one half; the actual native time trace is transverse at that crossing.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {A B E H M : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]
  [FiniteDimensional ℝ A] [NormedAddCommGroup B] [NormedSpace ℝ B]
  [FiniteDimensional ℝ B] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {J : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [T2Space M]

theorem exists_native_single_belt_crossing
    (Φ : PartialDiffeomorph 𝓘(ℝ, (ℝ × A) × B) J ((ℝ × A) × B) M ∞)
    (h0 : (0 : (ℝ × A) × B) ∈ Φ.source) :
    ∃ a : ℝ, 0 < a ∧ beltCrossingSheet a (0 : A) ∈ Φ.source ∧
      ∃ (F : ℝ × M → M) (K : Set M),
        IsCompact K ∧ K ⊆ Φ.target ∧ ContMDiff (𝓘(ℝ, ℝ).prod J) J ∞ F ∧
        (∀ y, F (0, y) = y) ∧
        (∀ t, ∃ d : Diffeomorph J J M M ∞, ∀ y, d y = F (t, y)) ∧
        (∀ t y, y ∉ K → F (t, y) = y) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, ∀ w : A, ∀ y : B,
          beltCrossingSheet a w ∈ Φ.source → beltCrossingBelt y ∈ Φ.source →
          (F (t, Φ (beltCrossingSheet a w)) = Φ (beltCrossingBelt y) ↔
            t = 1 / 2 ∧ w = 0 ∧ y = 0)) ∧
        ContMDiffAt 𝓘(ℝ, ℝ × A) J ∞
          (fun p : ℝ × A => F (p.1, Φ (beltCrossingSheet a p.2))) (1 / 2, 0) ∧
        ContMDiffAt 𝓘(ℝ, B) J ∞ (Φ ∘ beltCrossingBelt) 0 ∧
        NativeTransversality.At 𝓘(ℝ, ℝ × A) 𝓘(ℝ, B) J
          (fun p : ℝ × A => F (p.1, Φ (beltCrossingSheet a p.2)))
          (Φ ∘ beltCrossingBelt) (1 / 2, 0) 0 := by
  let V := (ℝ × A) × B
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (Φ.open_source.mem_nhds h0)
  let β : ContDiffBump (0 : V) := {
    rIn := r / 4
    rOut := r / 2
    rIn_pos := by positivity
    rIn_lt_rOut := by linarith }
  have hβsource : tsupport (β : V → ℝ) ⊆ Φ.source := by
    intro z hz
    rw [β.tsupport_eq, mem_closedBall_zero_iff] at hz
    apply hball
    rw [mem_ball_zero_iff]
    change ‖z‖ ≤ r / 2 at hz
    linarith
  obtain ⟨ε, hε, hmove⟩ := exists_small_linear_time_bump_isotopy Φ β.contDiff
    β.hasCompactSupport hβsource
  let a := min (r / 8) (ε / 4)
  have ha : 0 < a := lt_min (by positivity) (by positivity)
  have har : a ≤ r / 8 := min_le_left _ _
  have haε : a ≤ ε / 4 := min_le_right _ _
  have hsheetnorm : ‖(beltCrossingSheet a (0 : A) : V)‖ = a := by
    simp [beltCrossingSheet, Prod.norm_def, Real.norm_eq_abs, abs_of_pos ha, ha.le]
  have hplateau : beltCrossingSheet a (0 : A) ∈ ball (0 : V) (r / 4) := by
    rw [mem_ball_zero_iff, hsheetnorm]
    linarith
  have hsheet : beltCrossingSheet a (0 : A) ∈ Φ.source :=
    hball ((ball_subset_ball (show r / 4 ≤ r by linarith)) hplateau)
  have hβgerm : (β : V → ℝ) =ᶠ[𝓝 (beltCrossingSheet a (0 : A))] (fun _ => (1 : ℝ)) := by
    filter_upwards [isOpen_ball.mem_nhds hplateau] with z hz
    exact β.one_of_mem_closedBall (ball_subset_closedBall hz)
  have hβone : β (beltCrossingSheet a (0 : A)) = 1 := hβgerm.self_of_nhds
  have hdisplacement : ‖beltCrossingDisplacement (A := A) (B := B) a‖ < ε := by
    have hh : ‖beltCrossingDisplacement (A := A) (B := B) a‖ = 2 * a := by
      simp [beltCrossingDisplacement, Prod.norm_def, Real.norm_eq_abs,
        abs_of_pos ha, ha.le]
    rw [hh]
    linarith
  obtain ⟨F, K, hK, hKΦ, hF, hF0, hFd, hFfix, hsource, hformula⟩ :=
    hmove (beltCrossingDisplacement a) hdisplacement
  have htrackPoint : beltCrossingTrack (β : V → ℝ) a ((1 / 2 : ℝ), (0 : A)) =
      beltCrossingBelt (A := A) (0 : B) :=
    (beltCrossingTrack_eq_belt_iff β ha hβone (1 / 2) 0 0).mpr ⟨rfl, rfl, rfl⟩
  have htrackSource : beltCrossingTrack (β : V → ℝ) a ((1 / 2 : ℝ), (0 : A)) ∈ Φ.source := by
    rw [htrackPoint]
    exact h0
  have hpointFamily : Continuous (fun p : ℝ × A => beltCrossingSheet (B := B) a p.2) :=
    (beltCrossingSheet_smooth a).continuous.comp continuous_snd
  have hgerm : (fun p : ℝ × A => F (p.1, Φ (beltCrossingSheet a p.2))) =ᶠ[
      𝓝 ((1 / 2 : ℝ), (0 : A))] (Φ ∘ beltCrossingTrack (β : V → ℝ) a) := by
    have ht : ∀ᶠ p : ℝ × A in 𝓝 ((1 / 2 : ℝ), (0 : A)), p.1 ∈ Ioo (0 : ℝ) 1 :=
      continuous_fst.continuousAt.preimage_mem_nhds
        (Ioo_mem_nhds (by norm_num) (by norm_num))
    have hw := (hpointFamily.continuousAt (x := ((1 / 2 : ℝ), (0 : A)))).preimage_mem_nhds
      (Φ.open_source.mem_nhds hsheet)
    filter_upwards [ht, hw] with p hp hwp
    exact hformula p.1 ⟨hp.1.le, hp.2.le⟩ (beltCrossingSheet a p.2) hwp
  have hT : ContMDiffAt 𝓘(ℝ, ℝ × A) 𝓘(ℝ, V) ∞
      (beltCrossingTrack (β : V → ℝ) a) ((1 / 2 : ℝ), (0 : A)) :=
    (beltCrossingTrack_smooth β.contDiff a).contMDiff.contMDiffAt
  have hB : ContMDiffAt 𝓘(ℝ, B) 𝓘(ℝ, V) ∞ beltCrossingBelt (0 : B) :=
    beltCrossingBelt_smooth.contMDiff.contMDiffAt
  have hnative := (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds htrackSource)).comp
    ((1 / 2 : ℝ), (0 : A)) hT
  have hnativeB := (Φ.contMDiffOn_toFun.contMDiffAt (Φ.open_source.mem_nhds h0)).comp (0 : B) hB
  have htrans := (TransverseGerms.native_transversality_partial_diffeomorph_iff Φ
    (hT.mdifferentiableAt (by simp)) (hB.mdifferentiableAt (by simp))
    htrackPoint.symm htrackSource).mp (beltCrossingTrack_transverse β ha hβgerm)
  refine ⟨a, ha, hsheet, F, K, hK, hKΦ, hF, hF0, hFd, hFfix, ?_,
    hnative.congr_of_eventuallyEq hgerm, hnativeB, ?_⟩
  · intro t ht w y hw hy
    rw [hformula t ht (beltCrossingSheet a w) hw]
    have hnew := hsource t ht (beltCrossingSheet a w) hw
    constructor
    · intro he
      exact (beltCrossingTrack_eq_belt_iff β ha hβone t w y).mp
        (Φ.toPartialEquiv.injOn hnew hy he)
    · intro he
      exact congrArg Φ ((beltCrossingTrack_eq_belt_iff β ha hβone t w y).mpr he)
  · intro _
    rw [hgerm.mfderiv_eq]
    exact htrans (congrArg Φ htrackPoint.symm)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
