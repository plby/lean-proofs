import ErdosProblems.Erdos1165.PreStoppingFiber
import ErdosProblems.Erdos1165.Recurrence

open Filter MeasureTheory ProbabilityTheory Set
open scoped ENNReal

namespace Erdos1165.PreStoppingFiber

open StoppedInsertion

/-!
# Removing the cutoff from the pre-stopping fibre

This file separates the deterministic cutoff limit from the finite fibre.
The `WithTop` limit is unconditional: when the threshold is never reached,
the capped clock is exactly the cutoff and hence tends to `⊤`.  A natural-
valued limit requires precisely the almost-sure reachability hypothesis made
explicit below.  The recurrence theorem currently available in the project
discharges that hypothesis for `k = 1`.
-/

/-- The unbounded level clock on increment space, with value `⊤` when the
threshold is never reached. -/
noncomputable def unboundedLevelTime (m k : ℕ) (ω : StepPath) : WithTop ℕ :=
  thresholdTime (trajectory ω) m k

/-- A natural-valued representative used only on the finite/reaching event.
The fallback value is deliberately `0`; theorems using this definition and a
finite limit always assume `ReachesThreshold`. -/
noncomputable def unboundedLevelTimeNat (m k : ℕ) (ω : StepPath) : ℕ := by
  classical
  exact if h : ReachesThreshold (trajectory ω) m k then Nat.find h else 0

theorem truncatedLevelTime_eq_min_find (m k cutoff : ℕ) (ω : StepPath)
    (h : ReachesThreshold (trajectory ω) m k) :
    truncatedLevelTime m k cutoff ω = min (Nat.find h) cutoff := by
  simp [truncatedLevelTime, h]

theorem truncatedLevelTime_eq_cutoff_of_not_reaches (m k cutoff : ℕ) (ω : StepPath)
    (h : ¬ReachesThreshold (trajectory ω) m k) :
    truncatedLevelTime m k cutoff ω = cutoff := by
  simp [truncatedLevelTime, h]

theorem unboundedLevelTime_eq_coe_of_reaches (m k : ℕ) (ω : StepPath)
    (h : ReachesThreshold (trajectory ω) m k) :
    unboundedLevelTime m k ω = (Nat.find h : WithTop ℕ) := by
  exact thresholdTime_eq_coe (trajectory ω) m k h

theorem unboundedLevelTime_eq_top_of_not_reaches (m k : ℕ) (ω : StepPath)
    (h : ¬ReachesThreshold (trajectory ω) m k) :
    unboundedLevelTime m k ω = ⊤ := by
  exact (thresholdTime_eq_top_iff (trajectory ω) m k).2 h

theorem unboundedLevelTimeNat_eq_find (m k : ℕ) (ω : StepPath)
    (h : ReachesThreshold (trajectory ω) m k) :
    unboundedLevelTimeNat m k ω = Nat.find h := by
  simp [unboundedLevelTimeNat, h]

@[simp] theorem thresholdCount_trajectory_zero_time (m : ℕ) (ω : StepPath) :
    thresholdCount (trajectory ω) 0 m = if m ≤ 1 then 1 else 0 := by
  have hvisited : visitedSites (trajectory ω) 0 = {(0, 0)} := by
    ext x
    simp [visitedSites, visitedPrefix, pathPrefix, trajectory_zero]
  have hlocal : localTime (trajectory ω) 0 (0, 0) = 1 := by
    simp [localTime, localTimePrefix, pathPrefix, trajectory_zero]
  rw [thresholdCount, thresholdSites, hvisited, Finset.filter_singleton, hlocal]
  split <;> simp_all

/-- Exact characterization of the exceptional empty shifted prefix for the
one-site clock, on every path on which the unbounded clock is finite. -/
theorem unboundedLevelTimeNat_one_eq_zero_iff (m : ℕ) (ω : StepPath)
    (h : ReachesThreshold (trajectory ω) m 1) :
    unboundedLevelTimeNat m 1 ω = 0 ↔ m ≤ 1 := by
  rw [unboundedLevelTimeNat_eq_find m 1 ω h]
  unfold ReachesThreshold at h
  rw [Nat.find_eq_zero, thresholdCount_trajectory_zero_time]
  split <;> simp_all

theorem monotone_truncatedLevelTime_cutoff (m k : ℕ) (ω : StepPath) :
    Monotone fun cutoff => truncatedLevelTime m k cutoff ω := by
  classical
  by_cases h : ReachesThreshold (trajectory ω) m k
  · intro a b hab
    change truncatedLevelTime m k a ω ≤ truncatedLevelTime m k b ω
    rw [truncatedLevelTime_eq_min_find m k a ω h,
      truncatedLevelTime_eq_min_find m k b ω h]
    exact min_le_min_left _ hab
  · intro a b hab
    change truncatedLevelTime m k a ω ≤ truncatedLevelTime m k b ω
    simpa [truncatedLevelTime_eq_cutoff_of_not_reaches m k a ω h,
      truncatedLevelTime_eq_cutoff_of_not_reaches m k b ω h]

theorem eventually_truncatedLevelTime_eq_find (m k : ℕ) (ω : StepPath)
    (h : ReachesThreshold (trajectory ω) m k) :
    ∀ᶠ cutoff in atTop, truncatedLevelTime m k cutoff ω = Nat.find h := by
  filter_upwards [eventually_ge_atTop (Nat.find h)] with cutoff hcut
  rw [truncatedLevelTime_eq_min_find m k cutoff ω h, min_eq_left hcut]

theorem eventually_truncatedLevelTime_eq_unboundedNat (m k : ℕ) (ω : StepPath)
    (h : ReachesThreshold (trajectory ω) m k) :
    ∀ᶠ cutoff in atTop,
      truncatedLevelTime m k cutoff ω = unboundedLevelTimeNat m k ω := by
  simpa [unboundedLevelTimeNat_eq_find m k ω h] using
    eventually_truncatedLevelTime_eq_find m k ω h

theorem tendsto_truncatedLevelTime_nat_of_reaches (m k : ℕ) (ω : StepPath)
    (h : ReachesThreshold (trajectory ω) m k) :
    Tendsto (fun cutoff => truncatedLevelTime m k cutoff ω) atTop
      (nhds (unboundedLevelTimeNat m k ω)) := by
  exact (tendsto_congr'
    (eventually_truncatedLevelTime_eq_unboundedNat m k ω h)).2 tendsto_const_nhds

/-- The strongest pathwise cutoff-removal statement.  It does not assume that
the threshold is reached: in the complementary case the finite clock equals
the cutoff and converges to the `WithTop` value `⊤`. -/
theorem tendsto_truncatedLevelTime_withTop (m k : ℕ) (ω : StepPath) :
    Tendsto (fun cutoff => (truncatedLevelTime m k cutoff ω : WithTop ℕ)) atTop
      (nhds (unboundedLevelTime m k ω)) := by
  classical
  by_cases h : ReachesThreshold (trajectory ω) m k
  · rw [unboundedLevelTime_eq_coe_of_reaches m k ω h]
    have heq : ∀ᶠ cutoff in atTop,
        (truncatedLevelTime m k cutoff ω : WithTop ℕ) = (Nat.find h : WithTop ℕ) :=
      (eventually_truncatedLevelTime_eq_find m k ω h).mono fun _ hc => congrArg _ hc
    exact (tendsto_congr' heq).2 tendsto_const_nhds
  · rw [unboundedLevelTime_eq_top_of_not_reaches m k ω h]
    have heq : (fun cutoff => (truncatedLevelTime m k cutoff ω : WithTop ℕ)) =
        fun cutoff : ℕ => (cutoff : WithTop ℕ) := by
      funext cutoff
      rw [truncatedLevelTime_eq_cutoff_of_not_reaches m k cutoff ω h]
    rw [heq]
    exact WithTop.tendsto_coe_atTop

/-- On a reaching path, either the unbounded shifted input is genuinely empty
at time zero for every cutoff, or all sufficiently large cutoffs give the same
strictly positive stopping time. -/
theorem shifted_zero_or_eventually_positive_stable (m k : ℕ) (ω : StepPath)
    (h : ReachesThreshold (trajectory ω) m k) :
    (unboundedLevelTimeNat m k ω = 0 ∧
      ∀ cutoff, truncatedLevelTime m k cutoff ω = 0) ∨
    (0 < unboundedLevelTimeNat m k ω ∧
      ∀ᶠ cutoff in atTop,
        0 < truncatedLevelTime m k cutoff ω ∧
          truncatedLevelTime m k cutoff ω = unboundedLevelTimeNat m k ω) := by
  by_cases hzero : unboundedLevelTimeNat m k ω = 0
  · left
    refine ⟨hzero, ?_⟩
    intro cutoff
    rw [truncatedLevelTime_eq_min_find m k cutoff ω h]
    rw [unboundedLevelTimeNat_eq_find m k ω h] at hzero
    simp [hzero]
  · right
    have hpos : 0 < unboundedLevelTimeNat m k ω := Nat.pos_of_ne_zero hzero
    refine ⟨hpos, ?_⟩
    filter_upwards [eventually_truncatedLevelTime_eq_unboundedNat m k ω h]
      with cutoff hcut
    exact ⟨hcut.symm ▸ hpos, hcut⟩

/-- Abstract almost-sure cutoff removal under exactly the missing finiteness
input for an arbitrary number `k` of threshold sites. -/
theorem ae_tendsto_truncatedLevelTime_nat_of_ae_reaches (m k : ℕ)
    (hfinite : ∀ᵐ ω ∂fairSteps, ReachesThreshold (trajectory ω) m k) :
    ∀ᵐ ω ∂fairSteps,
      Tendsto (fun cutoff => truncatedLevelTime m k cutoff ω) atTop
        (nhds (unboundedLevelTimeNat m k ω)) := by
  filter_upwards [hfinite] with ω hω
  exact tendsto_truncatedLevelTime_nat_of_reaches m k ω hω

theorem ae_unboundedLevelTime_lt_top_of_ae_reaches (m k : ℕ)
    (hfinite : ∀ᵐ ω ∂fairSteps, ReachesThreshold (trajectory ω) m k) :
    ∀ᵐ ω ∂fairSteps, unboundedLevelTime m k ω < ⊤ := by
  filter_upwards [hfinite] with ω hω
  rw [unboundedLevelTime_eq_coe_of_reaches m k ω hω]
  exact WithTop.coe_lt_top _

/-- A single arbitrary-`k` wrapper exposing exactly the presently missing
probabilistic input and all three conclusions needed by the shifted fibre. -/
theorem ae_cutoff_removal_of_ae_reaches (m k : ℕ)
    (hfinite : ∀ᵐ ω ∂fairSteps, ReachesThreshold (trajectory ω) m k) :
    ∀ᵐ ω ∂fairSteps,
      Tendsto (fun cutoff => truncatedLevelTime m k cutoff ω) atTop
          (nhds (unboundedLevelTimeNat m k ω)) ∧
        unboundedLevelTime m k ω < ⊤ ∧
        ((unboundedLevelTimeNat m k ω = 0 ∧
            ∀ cutoff, truncatedLevelTime m k cutoff ω = 0) ∨
          (0 < unboundedLevelTimeNat m k ω ∧
            ∀ᶠ cutoff in atTop,
              0 < truncatedLevelTime m k cutoff ω ∧
                truncatedLevelTime m k cutoff ω = unboundedLevelTimeNat m k ω)) := by
  filter_upwards [hfinite] with ω hω
  refine ⟨tendsto_truncatedLevelTime_nat_of_reaches m k ω hω, ?_,
    shifted_zero_or_eventually_positive_stable m k ω hω⟩
  rw [unboundedLevelTime_eq_coe_of_reaches m k ω hω]
  exact WithTop.coe_lt_top _

/-! ## Cutoff removal on the actual level-favorite event -/

/-- On `M_m^k` the threshold is reached by definition; thus cutoff removal
for the conditional law needs no global recurrence input, even for arbitrary
positive `k`. -/
theorem reachesThreshold_of_levelFavorite {s : WalkPath} {m k : ℕ}
    (hk : 0 < k) (h : levelFavorite s m k) : ReachesThreshold s m k := by
  obtain ⟨n, hcount, _⟩ := (levelFavorite_iff_thresholdCounts s m k hk).mp h
  exact ⟨n, hcount.ge⟩

/-- Every path in `M_m^k` has an eventually constant capped level clock. -/
theorem eventually_truncatedLevelTime_eq_unboundedNat_of_levelFavorite
    (m k : ℕ) (ω : StepPath) (hk : 0 < k)
    (hM : levelFavorite (trajectory ω) m k) :
    ∀ᶠ cutoff in atTop,
      truncatedLevelTime m k cutoff ω = unboundedLevelTimeNat m k ω :=
  eventually_truncatedLevelTime_eq_unboundedNat m k ω
    (reachesThreshold_of_levelFavorite hk hM)

/-- Natural-valued cutoff convergence on `M_m^k`, valid for every positive
rank without an almost-sure reachability theorem. -/
theorem tendsto_truncatedLevelTime_nat_of_levelFavorite
    (m k : ℕ) (ω : StepPath) (hk : 0 < k)
    (hM : levelFavorite (trajectory ω) m k) :
    Tendsto (fun cutoff => truncatedLevelTime m k cutoff ω) atTop
      (nhds (unboundedLevelTimeNat m k ω)) :=
  tendsto_truncatedLevelTime_nat_of_reaches m k ω
    (reachesThreshold_of_levelFavorite hk hM)

/-- Infinite returns to one site suffice to make the one-site threshold clock
finite, at every level. -/
theorem reachesThreshold_one_of_frequently (s : WalkPath) (x : Point) (m : ℕ)
    (hrec : ∃ᶠ n in atTop, s n = x) : ReachesThreshold s m 1 := by
  have hlocal : ∀ᶠ n in atTop, m ≤ localTime s n x :=
    (tendsto_atTop.1 (tendsto_localTime_atTop_of_frequently s x hrec)) m
  have hvisited : ∀ᶠ n in atTop, x ∈ visitedSites s n :=
    eventually_mem_visitedSites_of_frequently s x hrec
  obtain ⟨n, hnlocal, hnvisited⟩ := (hlocal.and hvisited).exists
  refine ⟨n, ?_⟩
  change 0 < thresholdCount s n m
  rw [thresholdCount, Finset.card_pos]
  exact ⟨x, (mem_thresholdSites s n m x).2 ⟨hnvisited, hnlocal⟩⟩

/-- The recurrence theorem already in the project discharges the exact
almost-sure finiteness input for the case `k = 1`. -/
theorem fairSteps_ae_reachesThreshold_one (m : ℕ) :
    ∀ᵐ ω ∂fairSteps, ReachesThreshold (trajectory ω) m 1 := by
  filter_upwards [fairSteps_infinite_returns] with ω hrec
  exact reachesThreshold_one_of_frequently (trajectory ω) (0, 0) m hrec

theorem fairSteps_ae_tendsto_truncatedLevelTime_one (m : ℕ) :
    ∀ᵐ ω ∂fairSteps,
      Tendsto (fun cutoff => truncatedLevelTime m 1 cutoff ω) atTop
        (nhds (unboundedLevelTimeNat m 1 ω)) :=
  ae_tendsto_truncatedLevelTime_nat_of_ae_reaches m 1
    (fairSteps_ae_reachesThreshold_one m)

theorem fairSteps_ae_unboundedLevelTime_one_lt_top (m : ℕ) :
    ∀ᵐ ω ∂fairSteps, unboundedLevelTime m 1 ω < ⊤ :=
  ae_unboundedLevelTime_lt_top_of_ae_reaches m 1
    (fairSteps_ae_reachesThreshold_one m)

/-- In the shifted convention the exceptional zero-time prefix is retained
as an explicit branch, almost surely, rather than silently fed to the
positive-time insertion fibre. -/
theorem fairSteps_ae_shifted_zero_or_eventually_positive_stable_one (m : ℕ) :
    ∀ᵐ ω ∂fairSteps,
      (unboundedLevelTimeNat m 1 ω = 0 ∧
        ∀ cutoff, truncatedLevelTime m 1 cutoff ω = 0) ∨
      (0 < unboundedLevelTimeNat m 1 ω ∧
        ∀ᶠ cutoff in atTop,
          0 < truncatedLevelTime m 1 cutoff ω ∧
            truncatedLevelTime m 1 cutoff ω = unboundedLevelTimeNat m 1 ω) := by
  filter_upwards [fairSteps_ae_reachesThreshold_one m] with ω hω
  exact shifted_zero_or_eventually_positive_stable m 1 ω hω

end Erdos1165.PreStoppingFiber
