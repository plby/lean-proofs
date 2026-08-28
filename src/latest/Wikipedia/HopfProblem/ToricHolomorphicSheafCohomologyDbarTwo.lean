import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDbarTwoSequence
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationCousinDifferential

/-!
# Genuine global top-degree antiholomorphic solvability on the affine plane

The constructed strip corrections stabilize exactly on an exhausting
sequence of closed bidiscs. Their pointwise stabilized values therefore
agree locally with actual globally smooth stages. This gives an actual
global smooth `(0,1)` form whose top-degree antiholomorphic derivative is
the prescribed arbitrary smooth `(0,2)` coefficient.

No compact support, approximation, cohomology vanishing, or global
solvability premise is assumed. This analytic theorem is separate from
the later comparison with genuine Ext-defined sheaf cohomology.
-/

noncomputable section

open Set Metric Filter Topology
open scoped ContDiff

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DbarTwo

open PeriodTorusLineBundleClassification PeriodTorusLineBundleClassificationCousin

/-- The open bidiscs on which stabilized values are smooth. -/
def openBidisc (n : ℕ) : Set (ℂ × ℂ) :=
  ball 0 (radius n) ×ˢ ball 0 (radius n)

theorem openBidisc_isOpen (n : ℕ) : IsOpen (openBidisc n) :=
  isOpen_ball.prod isOpen_ball

theorem openBidisc_subset_closedBidisc (n : ℕ) : openBidisc n ⊆ closedBidisc n :=
  fun _ hq => ⟨ball_subset_closedBall hq.1, ball_subset_closedBall hq.2⟩

theorem exists_mem_openBidisc (q : ℂ × ℂ) : ∃ n : ℕ, q ∈ openBidisc n := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max ‖q.1‖ ‖q.2‖)
  have hnr : (n : ℝ) < radius n := by
    dsimp [radius]
    linarith
  refine ⟨n, ?_, ?_⟩
  · simpa only [mem_ball, dist_zero_right] using
      ((le_max_left ‖q.1‖ ‖q.2‖).trans_lt hn).trans hnr
  · simpa only [mem_ball, dist_zero_right] using
      ((le_max_right ‖q.1‖ ‖q.2‖).trans_lt hn).trans hnr

/-- An index of an actual open bidisc containing the selected point. -/
def coveringIndex (q : ℂ × ℂ) : ℕ := Classical.choose (exists_mem_openBidisc q)

theorem mem_coveringIndex (q : ℂ × ℂ) : q ∈ openBidisc (coveringIndex q) :=
  Classical.choose_spec (exists_mem_openBidisc q)

/-- The actual stabilized smooth pair, defined by the already proved
exhaustion and not by choosing a solution to the differential equation. -/
def primitive (w : ℂ × ℂ → ℂ) (q : ℂ × ℂ) : ℂ × ℂ :=
  stage w (coveringIndex q) q

theorem primitive_eq_stage {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w)
    (n : ℕ) (q : ℂ × ℂ) (hq : q ∈ openBidisc n) :
    primitive w q = stage w n q := by
  have hq' := openBidisc_subset_closedBidisc (coveringIndex q) (mem_coveringIndex q)
  have hn := openBidisc_subset_closedBidisc n hq
  exact (stage_compatible hw (le_max_left (coveringIndex q) n) q hq').symm.trans
    (stage_compatible hw (le_max_right (coveringIndex q) n) q hn)

/-- Stabilization holds on a neighborhood, so actual derivatives agree. -/
theorem primitive_eventuallyEq_stage {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w)
    (n : ℕ) {q : ℂ × ℂ} (hq : q ∈ openBidisc n) :
    primitive w =ᶠ[𝓝 q] stage w n := by
  filter_upwards [(openBidisc_isOpen n).mem_nhds hq] with x hx
  exact primitive_eq_stage hw n x hx

theorem primitive_smooth {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (primitive w) := by
  rw [contDiff_iff_contDiffAt]
  intro q
  obtain ⟨n, hn⟩ := exists_mem_openBidisc q
  exact (stage_smooth hw n).contDiffAt.congr_of_eventuallyEq
    (primitive_eventuallyEq_stage hw n hn)

/-- The first genuine coefficient of the global primitive. -/
def primitiveFirst (w : ℂ × ℂ → ℂ) (q : ℂ × ℂ) : ℂ := (primitive w q).1

/-- The second genuine coefficient of the global primitive. -/
def primitiveSecond (w : ℂ × ℂ → ℂ) (q : ℂ × ℂ) : ℂ := (primitive w q).2

theorem primitiveFirst_smooth {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (primitiveFirst w) :=
  contDiff_fst.comp (primitive_smooth hw)

theorem primitiveSecond_smooth {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w) :
    ContDiff ℝ ∞ (primitiveSecond w) :=
  contDiff_snd.comp (primitive_smooth hw)

/-- The actual top-degree equation, everywhere on the affine plane. -/
theorem primitive_equation {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w) (q : ℂ × ℂ) :
    dbarFirst (primitiveSecond w) q - dbarSecond (primitiveFirst w) q = w q := by
  obtain ⟨n, hn⟩ := exists_mem_openBidisc q
  have he := primitive_eventuallyEq_stage hw n hn
  have hfirst : primitiveFirst w =ᶠ[𝓝 q] firstStage w n :=
    he.mono fun x hx => congrArg Prod.fst hx
  have hsecond : primitiveSecond w =ᶠ[𝓝 q] secondStage w n :=
    he.mono fun x hx => congrArg Prod.snd hx
  rw [dbarFirst_congr hsecond, dbarSecond_congr hfirst]
  exact stage_equation hw n q (ball_subset_closedBall hn.2)

/-- Every genuine smooth `(0,2)` coefficient on `ℂ²` has a genuine
global smooth `(0,1)` primitive, without any extra premise. -/
theorem exists_smooth_top_primitive {w : ℂ × ℂ → ℂ} (hw : ContDiff ℝ ∞ w) :
    ∃ a b : ℂ × ℂ → ℂ, ContDiff ℝ ∞ a ∧ ContDiff ℝ ∞ b ∧
      ∀ q, dbarFirst b q - dbarSecond a q = w q :=
  ⟨primitiveFirst w, primitiveSecond w, primitiveFirst_smooth hw,
    primitiveSecond_smooth hw, primitive_equation hw⟩

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DbarTwo
