import Wikipedia.HopfProblem.DegreeCollapseSheetPassageChartGerm

/-!
# Put the constructed passages at one common crossing time

The clock is an actual increasing smooth diffeomorphism fixing zero and
one. Its germ at one half is a translation, so the positive longitudinal
crossing rate is retained. Comparing two passages can therefore use the
same radial parameter chart at the same source point.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

theorem exists_centered_passage_clock {τ : ℝ} (hτ : τ ∈ Ioo (0 : ℝ) 1) :
    ∃ D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      D 0 = 0 ∧ D 1 = 1 ∧ D (1 / 2) = τ ∧ StrictMono D ∧
      MapsTo D (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
      ((D : ℝ → ℝ) =ᶠ[𝓝 (1 / 2 : ℝ)] fun t => t + (τ - 1 / 2)) ∧
      HasDerivAt (D : ℝ → ℝ) 1 (1 / 2) := by
  obtain ⟨D, hfix, hgerm, hpoint, hmono, -⟩ :=
    MorseRearrangement.exists_increasing_interval_translation
      (show (1 / 2 : ℝ) ∈ Ioo (0 : ℝ) 1 by constructor <;> norm_num) hτ
  have h0 : D 0 = 0 := hfix 0 (by simp)
  have h1 : D 1 = 1 := hfix 1 (by simp)
  refine ⟨D, h0, h1, hpoint, hmono, ?_, hgerm, ?_⟩
  · intro t ht
    exact ⟨h0 ▸ hmono.monotone ht.1, h1 ▸ hmono.monotone ht.2⟩
  · exact ((hasDerivAt_id (1 / 2 : ℝ)).add_const (τ - 1 / 2)).congr_of_eventuallyEq hgerm

variable {V E H M : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {J : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  {Φ : PartialDiffeomorph 𝓘(ℝ, ℝ × V) J (ℝ × V) M ∞}

theorem LongitudinalTubeMotion.exists_centered_clock (A : LongitudinalTubeMotion Φ) :
    ∃ D : Diffeomorph 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) ℝ ℝ ∞,
      D 0 = 0 ∧ D 1 = 1 ∧ D (1 / 2) = A.time ∧
      MapsTo D (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) ∧
      (∀ t ∈ Icc (0 : ℝ) 1,
        Real.smoothTransition (D t) * A.destination = 1 ↔ t = 1 / 2) ∧
      HasDerivAt (fun t : ℝ => Real.smoothTransition (D t) * A.destination)
        (deriv Real.smoothTransition A.time * A.destination) (1 / 2) := by
  obtain ⟨D, h0, h1, hpoint, -, hinterval, -, hder⟩ :=
    exists_centered_passage_clock A.time_mem
  refine ⟨D, h0, h1, hpoint, hinterval, ?_, ?_⟩
  · intro t ht
    rw [A.unique_time (D t) (hinterval ht), ← hpoint]
    exact D.injective.eq_iff
  · have htransition :=
      ((Real.smoothTransition.contDiff (n := ⊤)).differentiable (by simp) A.time).hasDerivAt
    have htransition' : HasDerivAt Real.smoothTransition
        (deriv Real.smoothTransition A.time) (D (1 / 2)) := by
      rw [hpoint]
      exact htransition
    convert! ((htransition'.comp (1 / 2) hder).mul_const A.destination) using 1
    rw [mul_one]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
