import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyDbarLocalOneCutoff
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationExhaustionSeries

/-!
# Actual analytic-tail gluing on an arbitrary open domain

The infinite-sum limit agrees locally with a smooth finite stage plus a
proved analytic tail. The exhaustion need cover only the specified open
domain, and the finite stages need be smooth only there.
-/

noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarOne

open PeriodTorusLineBundleClassification

theorem correctionLimit_eq_stage_add_tail_on {Ω : Set (ℂ × ℂ)} {u : ℕ → ℂ × ℂ → ℂ}
    {U : ℕ → Set (ℂ × ℂ)} (hmono : Monotone U)
    (hcover : ∀ q ∈ Ω, ∃ N, q ∈ U N)
    (hb : ∀ n, ∀ q ∈ U n, ‖correctionDifference u n q‖ ≤ (1 / 2 : ℝ) ^ n)
    (N : ℕ) (q : ℂ × ℂ) (hq : q ∈ Ω) :
    correctionLimit u q = u N q + correctionTail u N q := by
  obtain ⟨M, hM⟩ := hcover q hq
  have hs : Summable (fun n => correctionDifference u n q) :=
    Summable.comp_nat_add (f := fun n => correctionDifference u n q) (k := M)
      (correction_tail_summable hmono hb M q hM)
  have ht := hs.sum_add_tsum_nat_add N
  rw [sum_correctionDifference] at ht
  unfold correctionLimit correctionTail
  rw [← ht]
  ring

theorem correctionLimit_eventuallyEq_stage_add_tail {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {u : ℕ → ℂ × ℂ → ℂ} {U : ℕ → Set (ℂ × ℂ)} (hmono : Monotone U)
    (hcover : ∀ q ∈ Ω, ∃ N, q ∈ U N)
    (hb : ∀ n, ∀ q ∈ U n, ‖correctionDifference u n q‖ ≤ (1 / 2 : ℝ) ^ n)
    (N : ℕ) (q : ℂ × ℂ) (hq : q ∈ Ω) :
    correctionLimit u =ᶠ[𝓝 q] (fun x => u N x + correctionTail u N x) := by
  filter_upwards [hΩ.mem_nhds hq] with x hx
  exact correctionLimit_eq_stage_add_tail_on hmono hcover hb N x hx

theorem correctionLimit_contDiffOn {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {u : ℕ → ℂ × ℂ → ℂ} {U : ℕ → Set (ℂ × ℂ)}
    (hU : ∀ n, IsOpen (U n)) (hmono : Monotone U)
    (hcover : ∀ q ∈ Ω, ∃ N, q ∈ U N) (hu : ∀ n, ContDiffOn ℝ ∞ (u n) Ω)
    (hhol : ∀ n, AnalyticOnNhd ℂ (correctionDifference u n) (U n))
    (hb : ∀ n, ∀ q ∈ U n, ‖correctionDifference u n q‖ ≤ (1 / 2 : ℝ) ^ n) :
    ContDiffOn ℝ ∞ (correctionLimit u) Ω := by
  intro q hq
  obtain ⟨N, hN⟩ := hcover q hq
  have he := correctionLimit_eventuallyEq_stage_add_tail hΩ hmono hcover hb N q hq
  have hs : ContDiffAt ℝ ∞ (u N) q := (hu N q hq).contDiffAt (hΩ.mem_nhds hq)
  have ht : ContDiffAt ℝ ∞ (correctionTail u N) q :=
    (correctionTail_analyticOnNhd hU hmono hhol hb N q hN).contDiffAt.restrict_scalars ℝ
  exact ((hs.add ht).congr_of_eventuallyEq he).contDiffWithinAt

theorem correctionLimit_coordinate_dbar_on {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {u : ℕ → ℂ × ℂ → ℂ} {U : ℕ → Set (ℂ × ℂ)}
    (hU : ∀ n, IsOpen (U n)) (hmono : Monotone U)
    (hsub : ∀ n, U n ⊆ Ω) (hcover : ∀ q ∈ Ω, ∃ N, q ∈ U N)
    (hu : ∀ n, ContDiffOn ℝ ∞ (u n) Ω)
    (hhol : ∀ n, AnalyticOnNhd ℂ (correctionDifference u n) (U n))
    (hb : ∀ n, ∀ q ∈ U n, ‖correctionDifference u n q‖ ≤ (1 / 2 : ℝ) ^ n)
    (N : ℕ) (q : ℂ × ℂ) (hq : q ∈ U N) :
    dbarFirst (correctionLimit u) q = dbarFirst (u N) q ∧
      dbarSecond (correctionLimit u) q = dbarSecond (u N) q := by
  have hqd := hsub N hq
  have he := correctionLimit_eventuallyEq_stage_add_tail hΩ hmono hcover hb N q hqd
  have ha := correctionTail_analyticOnNhd hU hmono hhol hb N q hq
  have hs : DifferentiableAt ℝ (u N) q :=
    ((hu N).differentiableOn (by simp) q hqd).differentiableAt (hΩ.mem_nhds hqd)
  have ht : DifferentiableAt ℝ (correctionTail u N) q :=
    ha.differentiableAt.restrictScalars ℝ
  have hz := coordinate_dbar_zero_of_analyticAt ha
  constructor
  · rw [DbarLocalOne.dbarFirst_eq_of_eventuallyEq he, dbarFirst_add hs ht, hz.1, add_zero]
  · rw [DbarLocalOne.dbarSecond_eq_of_eventuallyEq he, dbarSecond_add hs ht, hz.2, add_zero]

theorem exists_smoothOn_primitive_of_exhaustion {Ω : Set (ℂ × ℂ)} (hΩ : IsOpen Ω)
    {f g : ℂ × ℂ → ℂ} {u : ℕ → ℂ × ℂ → ℂ} {U : ℕ → Set (ℂ × ℂ)}
    (hU : ∀ n, IsOpen (U n)) (hmono : Monotone U) (hsub : ∀ n, U n ⊆ Ω)
    (hcover : ∀ q ∈ Ω, ∃ N, q ∈ U N) (hu : ∀ n, ContDiffOn ℝ ∞ (u n) Ω)
    (hstage : ∀ n, ∀ q ∈ U n, dbarFirst (u n) q = f q ∧ dbarSecond (u n) q = g q)
    (hb : ∀ n, ∀ q ∈ U n, ‖correctionDifference u n q‖ ≤ (1 / 2 : ℝ) ^ n) :
    ∃ v : ℂ × ℂ → ℂ, ContDiffOn ℝ ∞ v Ω ∧
      ∀ q ∈ Ω, dbarFirst v q = f q ∧ dbarSecond v q = g q := by
  have hh : ∀ n, AnalyticOnNhd ℂ (correctionDifference u n) (U n) := by
    intro n
    apply analyticOnNhd_sub_of_coordinate_dbar_eq (hU n)
      (((hu (n + 1)).differentiableOn (by simp)).mono (hsub n))
      (((hu n).differentiableOn (by simp)).mono (hsub n))
    · intro q hq
      exact (hstage (n + 1) q (hmono (Nat.le_succ n) hq)).1.trans (hstage n q hq).1.symm
    · intro q hq
      exact (hstage (n + 1) q (hmono (Nat.le_succ n) hq)).2.trans (hstage n q hq).2.symm
  refine ⟨correctionLimit u, correctionLimit_contDiffOn hΩ hU hmono hcover hu hh hb, ?_⟩
  intro q hq
  obtain ⟨N, hN⟩ := hcover q hq
  have hd := correctionLimit_coordinate_dbar_on hΩ hU hmono hsub hcover hu hh hb N q hN
  exact ⟨hd.1.trans (hstage N q hN).1, hd.2.trans (hstage N q hN).2⟩

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.DoublePuncturedDbarOne
