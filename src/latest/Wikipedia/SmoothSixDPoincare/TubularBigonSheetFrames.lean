import Wikipedia.SmoothSixDPoincare.NativeStripBoundaryFrame
import Wikipedia.SmoothSixDPoincare.TwoSheetTubularBigon
import Wikipedia.SmoothSixDPoincare.BigonStripImmersion
import Wikipedia.SmoothSixDPoincare.FrameFieldComplement

/-!
# Constructed smooth sheet frames along both tubular-bigon edges

The retained strip chart and transverse derivative produce the actual sheet
directions in the disk's actual tubular normal coordinate of arbitrary rank. These
fields are smooth near the entire closed parameter interval and injective
at both endpoints as well as in the interior. They describe the two sheets;
they do not yet join into the Whitney boundary framing.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.TubularBigon

open WhitneyPairModel

variable {E M A B : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  {S T : Set M} {a b : ℝ → M} {k₀ k₁ : (ℝ × ℝ) → M} {h : ℝ}

/-- The lower sheet contributes a genuine full-rank field in the actual tubular normal model. -/
theorem lower_sheetFrame {k : CleanStripPatch (E := E) S T a k₀ k₁} {l : (ℝ × ℝ) → M}
    {n : ℕ} (tube : TubularBigon (E := E) S T a b k.map l h n)
    (d : StripNormalData A B (E := E) S k.map) :
    (∃ U : Set ℝ, IsOpen U ∧ Icc (0 : ℝ) 1 ⊆ U ∧
      ContDiffOn ℝ ∞ (d.normalFrame tube.chart) U) ∧
    ∀ t ∈ Icc (0 : ℝ) 1, Injective (d.normalFrame tube.chart t) := by
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1, (2 * t - 1, 0) ∈ bigon h := by
    intro t ht
    have hf : (2 * t - 1, 0) ∈ frontier (bigon h) :=
      (mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr ⟨t, ht, Or.inl rfl⟩
    exact ((mem_frontier_bigon_iff h _).mp hf).1
  have hsource : ∀ t ∈ Icc (0 : ℝ) 1, ((2 * t - 1, 0), 0) ∈ tube.chart.source :=
    fun t ht => tube.source_contains ⟨hpoint t ht, Metric.mem_closedBall_self tube.radius_pos.le⟩
  constructor
  · apply d.exists_open_normalFrame_domain tube.chart
    intro t ht
    have hp := tube.chart.map_source' (hsource t ht)
    rw [tube.zero_section, tube.lower t ht] at hp
    rw [← d.center t, k.center t ht]
    exact hp
  · intro t ht
    have hkt : (t, (0 : ℝ)) ∈ k.domain :=
      k.contains_strip ⟨ht, ⟨neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩⟩
    have hcs : Surjective (fderiv ℝ (lowerStripCoordinates h) (2 * t - 1, 0)) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
        (injective_fderiv_lowerStripCoordinates tube.height_pos.ne' (2 * t - 1))
    exact d.injective_normalFrame_of_strip_germ tube.chart ht
      (k.smooth.contMDiffAt (k.open_domain.mem_nhds hkt)) tube.zero_section (hsource t ht)
      (contDiff_lowerStripCoordinates tube.height_pos.ne').contDiffAt
      (lowerStripCoordinates_lower h t) hcs (tube.lower_germ t ht)

/-- The upper sheet likewise gives its actual full-rank normal-image field, including corners. -/
theorem upper_sheetFrame {l : CleanStripPatch (E := E) T S b k₀ k₁} {k : (ℝ × ℝ) → M}
    {n : ℕ} (tube : TubularBigon (E := E) S T a b k l.map h n)
    (d : StripNormalData A B (E := E) T l.map) :
    (∃ U : Set ℝ, IsOpen U ∧ Icc (0 : ℝ) 1 ⊆ U ∧
      ContDiffOn ℝ ∞ (d.normalFrame tube.chart) U) ∧
    ∀ t ∈ Icc (0 : ℝ) 1, Injective (d.normalFrame tube.chart t) := by
  have hpoint : ∀ t ∈ Icc (0 : ℝ) 1,
      (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ bigon h := by
    intro t ht
    have hf : (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ frontier (bigon h) :=
      (mem_frontier_bigon_iff_exists_time tube.height_pos _).mpr ⟨t, ht, Or.inr rfl⟩
    exact ((mem_frontier_bigon_iff h _).mp hf).1
  have hsource : ∀ t ∈ Icc (0 : ℝ) 1,
      ((2 * t - 1, h * (1 - (2 * t - 1) ^ 2)), 0) ∈ tube.chart.source :=
    fun t ht => tube.source_contains ⟨hpoint t ht, Metric.mem_closedBall_self tube.radius_pos.le⟩
  constructor
  · apply d.exists_open_normalFrame_domain tube.chart
    intro t ht
    have hp := tube.chart.map_source' (hsource t ht)
    rw [tube.zero_section, tube.upper t ht] at hp
    rw [← d.center t, l.center t ht]
    exact hp
  · intro t ht
    have hlt : (t, (0 : ℝ)) ∈ l.domain :=
      l.contains_strip ⟨ht, ⟨neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩⟩
    have hcs : Surjective
        (fderiv ℝ (upperStripCoordinates h) (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) :=
      (LinearMap.injective_iff_surjective_of_finrank_eq_finrank rfl).mp
        (injective_fderiv_upperStripCoordinates tube.height_pos.ne' (2 * t - 1))
    exact d.injective_normalFrame_of_strip_germ tube.chart ht
      (l.smooth.contMDiffAt (l.open_domain.mem_nhds hlt)) tube.zero_section (hsource t ht)
      (contDiff_upperStripCoordinates tube.height_pos.ne').contDiffAt
      (upperStripCoordinates_upper h t) hcs (tube.upper_germ t ht)

/-- Construct a smoothly varying complement of the actual upper sheet field near the whole arc. -/
theorem upper_sheetFrame_complement_of_finrank [FiniteDimensional ℝ A]
    {l : CleanStripPatch (E := E) T S b k₀ k₁} {k : (ℝ × ℝ) → M}
    {n : ℕ} (tube : TubularBigon (E := E) S T a b k l.map h n)
    (d : StripNormalData A B (E := E) T l.map)
    (m : ℕ) (hdim : Module.finrank ℝ A + m = n) :
    ∃ V : Set ℝ, IsOpen V ∧ Icc (0 : ℝ) 1 ⊆ V ∧
      ContDiffOn ℝ ∞ (d.normalFrame tube.chart) V ∧
      ∃ C : ℝ → (EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin n)),
        ContDiffOn ℝ ∞ C V ∧
        (∀ t ∈ Icc (0 : ℝ) 1, (C t).range = (d.normalFrame tube.chart t).rangeᗮ) ∧
        ∀ t ∈ V, Bijective ((d.normalFrame tube.chart t).coprod (C t)) := by
  obtain ⟨⟨U, hU, hIU, hs⟩, hi⟩ := tube.upper_sheetFrame d
  have hstar : StarConvex ℝ (0 : ℝ) (Icc (0 : ℝ) 1) :=
    (convex_Icc (0 : ℝ) 1).starConvex (by simp)
  have hdim' : Module.finrank ℝ A + m = Module.finrank ℝ (EuclideanSpace ℝ (Fin n)) := by
    simpa only [finrank_euclideanSpace_fin] using hdim
  obtain ⟨W, hW, hIW, C, hC, hr, hc⟩ :=
    FrameField.exists_smooth_complement_near_starConvex_on hU hs isCompact_Icc
      hstar (by simp) hIU hi m hdim'
  exact ⟨W ∩ U, hW.inter hU, fun t ht => ⟨hIW ht, hIU ht⟩,
    hs.mono inter_subset_right, C, hC.mono inter_subset_left, hr, fun t ht => hc t ht.1⟩

/-- The two-plus-two complement specialization in the original rank-four normal model. -/
theorem upper_sheetFrame_complement
    {l : CleanStripPatch (E := E) T S b k₀ k₁} {k : (ℝ × ℝ) → M}
    (tube : TubularBigon (E := E) S T a b k l.map h)
    (d : StripNormalData (EuclideanSpace ℝ (Fin 2)) B (E := E) T l.map) :
    ∃ V : Set ℝ, IsOpen V ∧ Icc (0 : ℝ) 1 ⊆ V ∧
      ContDiffOn ℝ ∞ (d.normalFrame tube.chart) V ∧
      ∃ C : ℝ → (EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 4)),
        ContDiffOn ℝ ∞ C V ∧
        (∀ t ∈ Icc (0 : ℝ) 1, (C t).range = (d.normalFrame tube.chart t).rangeᗮ) ∧
        ∀ t ∈ V, Bijective ((d.normalFrame tube.chart t).coprod (C t)) :=
  upper_sheetFrame_complement_of_finrank tube d 2 (by simp only [finrank_euclideanSpace_fin])

end Wikipedia.SmoothSixDPoincare.TubularBigon
