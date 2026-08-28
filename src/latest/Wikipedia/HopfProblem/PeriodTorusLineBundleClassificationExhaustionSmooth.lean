import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationExhaustionSeries

/-!
# Gluing actual primitives by their convergent analytic corrections

The infinite sum is locally the sum of one smooth stage and a proved
analytic tail.  Thus it is smooth, and both antiholomorphic derivatives
are exactly those of that stage.  The existence of an appropriate sequence
is constructed separately from local primitives and polynomial approximation.
-/

noncomputable section

open Set
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusLineBundleClassification

theorem correctionLimit_contDiff {u : ℕ → ℂ × ℂ → ℂ} {U : ℕ → Set (ℂ × ℂ)}
    (hU : ∀ n, IsOpen (U n)) (hmono : Monotone U) (hcover : ∀ q, ∃ N, q ∈ U N)
    (hu : ∀ n, ContDiff ℝ ∞ (u n))
    (hhol : ∀ n, AnalyticOnNhd ℂ (correctionDifference u n) (U n))
    (hb : ∀ n, ∀ q ∈ U n, ‖correctionDifference u n q‖ ≤ (1 / 2 : ℝ) ^ n) :
    ContDiff ℝ ∞ (correctionLimit u) := by
  apply contDiff_iff_contDiffAt.mpr
  intro q
  obtain ⟨N, hN⟩ := hcover q
  have he : correctionLimit u = fun x => u N x + correctionTail u N x :=
    funext (correctionLimit_eq_stage_add_tail hmono hcover hb N)
  rw [he]
  have ht : ContDiffAt ℂ ∞ (correctionTail u N) q :=
    (correctionTail_analyticOnNhd hU hmono hhol hb N q hN).contDiffAt
  exact (hu N).contDiffAt.add (ht.restrict_scalars ℝ)

/-- Each actual antiholomorphic derivative agrees with the finite stage on
the corresponding member of the exhaustion. -/
theorem correctionLimit_coordinate_dbar {u : ℕ → ℂ × ℂ → ℂ}
    {U : ℕ → Set (ℂ × ℂ)}
    (hU : ∀ n, IsOpen (U n)) (hmono : Monotone U) (hcover : ∀ q, ∃ N, q ∈ U N)
    (hu : ∀ n, ContDiff ℝ ∞ (u n))
    (hhol : ∀ n, AnalyticOnNhd ℂ (correctionDifference u n) (U n))
    (hb : ∀ n, ∀ q ∈ U n, ‖correctionDifference u n q‖ ≤ (1 / 2 : ℝ) ^ n)
    (N : ℕ) (q : ℂ × ℂ) (hq : q ∈ U N) :
    dbarFirst (correctionLimit u) q = dbarFirst (u N) q ∧
      dbarSecond (correctionLimit u) q = dbarSecond (u N) q := by
  have he : correctionLimit u = fun x => u N x + correctionTail u N x :=
    funext (correctionLimit_eq_stage_add_tail hmono hcover hb N)
  have ha := correctionTail_analyticOnNhd hU hmono hhol hb N q hq
  have hs : DifferentiableAt ℝ (u N) q := (hu N).differentiable (by simp) q
  have ht : DifferentiableAt ℝ (correctionTail u N) q :=
    ha.differentiableAt.restrictScalars ℝ
  have hz := coordinate_dbar_zero_of_analyticAt ha
  rw [he]
  constructor
  · rw [dbarFirst_add hs ht, hz.1, add_zero]
  · rw [dbarSecond_add hs ht, hz.2, add_zero]

/-- An actual geometrically compatible sequence of smooth primitives has
a global smooth primitive as its explicitly defined infinite-sum limit. -/
theorem exists_smooth_primitive_of_exhaustion {f g : ℂ × ℂ → ℂ}
    {u : ℕ → ℂ × ℂ → ℂ} {U : ℕ → Set (ℂ × ℂ)}
    (hU : ∀ n, IsOpen (U n)) (hmono : Monotone U) (hcover : ∀ q, ∃ N, q ∈ U N)
    (hu : ∀ n, ContDiff ℝ ∞ (u n))
    (hstage : ∀ n, ∀ q ∈ U n, dbarFirst (u n) q = f q ∧ dbarSecond (u n) q = g q)
    (hb : ∀ n, ∀ q ∈ U n, ‖correctionDifference u n q‖ ≤ (1 / 2 : ℝ) ^ n) :
    ∃ v : ℂ × ℂ → ℂ, ContDiff ℝ ∞ v ∧
      (∀ q, dbarFirst v q = f q) ∧ ∀ q, dbarSecond v q = g q := by
  have hh : ∀ n, AnalyticOnNhd ℂ (correctionDifference u n) (U n) := by
    intro n
    apply analyticOnNhd_sub_of_coordinate_dbar_eq (hU n)
      ((hu (n + 1)).differentiable (by simp)).differentiableOn
      ((hu n).differentiable (by simp)).differentiableOn
    · intro q hq
      exact (hstage (n + 1) q (hmono (Nat.le_succ n) hq)).1.trans
        (hstage n q hq).1.symm
    · intro q hq
      exact (hstage (n + 1) q (hmono (Nat.le_succ n) hq)).2.trans
        (hstage n q hq).2.symm
  refine ⟨correctionLimit u, correctionLimit_contDiff hU hmono hcover hu hh hb, ?_, ?_⟩
  · intro q
    obtain ⟨N, hN⟩ := hcover q
    exact (correctionLimit_coordinate_dbar hU hmono hcover hu hh hb N q hN).1.trans
      (hstage N q hN).1
  · intro q
    obtain ⟨N, hN⟩ := hcover q
    exact (correctionLimit_coordinate_dbar hU hmono hcover hu hh hb N q hN).2.trans
      (hstage N q hN).2

end Wikipedia.HopfProblem.PeriodTorusLineBundleClassification
