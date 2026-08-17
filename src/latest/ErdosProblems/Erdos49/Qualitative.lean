import PrimeNumberTheoremAnd.Consequences

/-!
# Qualitative scale selection for Erdős Problem 49

The prime number theorem available in `PrimeNumberTheoremAnd.Consequences` has
no explicit error term.  This file records the diagonal argument which permits
one to let every *finite* auxiliary parameter tend to infinity sufficiently
slowly.  In particular, any estimate which is eventual for each fixed value of
the parameter can be used at a parameter depending on the main variable.

This is the mechanism needed for a qualitative version of Tao's proof: first
prove the anatomy and interval estimates with a fixed complexity parameter,
then choose that parameter by `exists_slow_scale` (or its uniform version).
-/

open Filter

namespace Erdos49.Qualitative

/-- Turn arbitrary starting thresholds into a strictly increasing schedule
which also lies above the diagonal. -/
def schedule (threshold : ℕ → ℕ) : ℕ → ℕ
  | 0 => threshold 0
  | k + 1 => max (schedule threshold k + 1) (max (threshold (k + 1)) (k + 1))

lemma threshold_le_schedule (threshold : ℕ → ℕ) (k : ℕ) :
    threshold k ≤ schedule threshold k := by
  cases k with
  | zero => rfl
  | succ k =>
      exact (le_max_left _ _).trans (le_max_right _ _)

lemma index_le_schedule (threshold : ℕ → ℕ) (k : ℕ) :
    k ≤ schedule threshold k := by
  cases k with
  | zero => exact Nat.zero_le _
  | succ k =>
      exact (le_max_right _ _).trans (le_max_right _ _)

lemma schedule_succ (threshold : ℕ → ℕ) (k : ℕ) :
    schedule threshold k + 1 ≤ schedule threshold (k + 1) :=
  le_max_left _ _

lemma schedule_strictMono (threshold : ℕ → ℕ) :
    StrictMono (schedule threshold) := by
  exact strictMono_nat_of_lt_succ fun k =>
    lt_of_lt_of_le (Nat.lt_succ_self _) (schedule_succ threshold k)

/-- The largest scheduled parameter which has started by stage `n`. -/
def activeIndex (threshold : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.findGreatest (fun k => schedule threshold k ≤ n) n

lemma activeIndex_le (threshold : ℕ → ℕ) (n : ℕ) :
    activeIndex threshold n ≤ n :=
  Nat.findGreatest_le n

lemma le_activeIndex (threshold : ℕ → ℕ) {k n : ℕ}
    (hkn : k ≤ n) (hstart : schedule threshold k ≤ n) :
    k ≤ activeIndex threshold n :=
  Nat.le_findGreatest hkn hstart

lemma schedule_activeIndex_le (threshold : ℕ → ℕ) {n : ℕ}
    (hn : schedule threshold 0 ≤ n) :
    schedule threshold (activeIndex threshold n) ≤ n := by
  unfold activeIndex
  exact Nat.findGreatest_spec (P := fun k => schedule threshold k ≤ n)
    (Nat.zero_le n) hn

lemma activeIndex_mono (threshold : ℕ → ℕ) :
    Monotone (activeIndex threshold) := by
  intro m n hmn
  by_cases hm : schedule threshold 0 ≤ m
  · apply le_activeIndex threshold
    · exact (activeIndex_le threshold m).trans hmn
    · exact (schedule_activeIndex_le threshold hm).trans hmn
  · have hzero : activeIndex threshold m = 0 := by
      rw [activeIndex, Nat.findGreatest_eq_iff]
      refine ⟨Nat.zero_le _, ?_, ?_⟩
      · simp
      · intro k hk hkn hkstart
        apply hm
        exact ((schedule_strictMono threshold).monotone (Nat.zero_le k)).trans hkstart
    simp [hzero]

lemma tendsto_activeIndex (threshold : ℕ → ℕ) :
    Tendsto (activeIndex threshold) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro k
  refine ⟨max (schedule threshold k) k, ?_⟩
  intro n hn
  apply le_activeIndex threshold
  · exact (le_max_right _ _).trans hn
  · exact (le_max_left _ _).trans hn

/-- A non-quantitative diagonal principle for eventual estimates.

If `P k n` holds eventually in `n` for every fixed `k`, then it holds for a
monotone parameter `scale n` which tends to infinity and never exceeds `n`.
No monotonicity assumption on `P` is needed. -/
theorem exists_slow_scale {P : ℕ → ℕ → Prop}
    (hP : ∀ k, ∀ᶠ n in atTop, P k n) :
    ∃ scale : ℕ → ℕ,
      Monotone scale ∧ Tendsto scale atTop atTop ∧
        (∀ n, scale n ≤ n) ∧ ∀ᶠ n in atTop, P (scale n) n := by
  choose threshold hthreshold using fun k => (eventually_atTop.1 (hP k))
  refine ⟨activeIndex threshold, activeIndex_mono threshold,
    tendsto_activeIndex threshold, activeIndex_le threshold, ?_⟩
  filter_upwards [eventually_ge_atTop (schedule threshold 0)] with n hn
  apply hthreshold (activeIndex threshold n)
  exact (threshold_le_schedule threshold _).trans
    (schedule_activeIndex_le threshold hn)

/-- Uniform diagonal principle.  At stage `n`, the conclusion holds for every
fixed-complexity estimate with index at most `scale n`. -/
theorem exists_slow_scale_uniform {P : ℕ → ℕ → Prop}
    (hP : ∀ k, ∀ᶠ n in atTop, P k n) :
    ∃ scale : ℕ → ℕ,
      Monotone scale ∧ Tendsto scale atTop atTop ∧
        (∀ n, scale n ≤ n) ∧
          ∀ᶠ n in atTop, ∀ k ≤ scale n, P k n := by
  let Q : ℕ → ℕ → Prop := fun K n => ∀ k ≤ K, P k n
  have hQ : ∀ K, ∀ᶠ n in atTop, Q K n := by
    intro K
    have hall : ∀ k ∈ Finset.range (K + 1), ∀ᶠ n in atTop, P k n := by
      intro k hk
      exact hP k
    filter_upwards [(Finset.eventually_all (Finset.range (K + 1))).2 hall] with n hn
    intro k hk
    exact hn k (Finset.mem_range.2 (Nat.lt_succ_of_le hk))
  simpa [Q] using exists_slow_scale hQ

/-! ## A concrete PNT consequence -/

/-- The weak PNT error can be made uniformly small above a moving lower
endpoint, provided that endpoint and the demanded accuracy move slowly enough.

The functions `lowerLoss` and `accuracy` describe, at fixed complexity `k`,
the allowed loss in the lower endpoint and the desired error.  The conclusion
selects one common slowly growing complexity scale. -/
theorem exists_pnt_uniform_tail_scale
    (lowerLoss accuracy : ℕ → ℝ)
    (hlower : ∀ k, 0 < lowerLoss k) (haccuracy : ∀ k, 0 < accuracy k) :
    ∃ c : ℝ → ℝ, c =o[atTop] (fun _ ↦ (1 : ℝ)) ∧
      (∀ x : ℝ, Nat.primeCounting ⌊x⌋₊ =
        (1 + c x) * x / Real.log x) ∧
      ∃ scale : ℕ → ℕ,
        Monotone scale ∧ Tendsto scale atTop atTop ∧
          (∀ n, scale n ≤ n) ∧
          ∀ᶠ n in atTop, ∀ x : ℝ,
            (n : ℝ) / lowerLoss (scale n) ≤ x →
              |c x| < accuracy (scale n) := by
  obtain ⟨c, hc, hcformula⟩ := pi_alt
  refine ⟨c, hc, hcformula, ?_⟩
  have hc0 : Tendsto c atTop (nhds 0) := by
    simpa only [isLittleO_one_iff] using hc
  have hfixed : ∀ k, ∀ᶠ n : ℕ in atTop,
      ∀ x : ℝ, (n : ℝ) / lowerLoss k ≤ x → |c x| < accuracy k := by
    intro k
    have herr : ∀ᶠ x : ℝ in atTop, |c x| < accuracy k := by
      rw [Metric.tendsto_atTop] at hc0
      obtain ⟨X, hX⟩ := hc0 (accuracy k) (haccuracy k)
      filter_upwards [eventually_ge_atTop X] with x hx
      simpa [Real.dist_eq] using hX x hx
    obtain ⟨X, hX⟩ := eventually_atTop.1 herr
    filter_upwards [eventually_ge_atTop
      ⌈max 0 (X * lowerLoss k)⌉₊] with n hn
    intro x hx
    apply hX x
    have hnreal : max 0 (X * lowerLoss k) ≤ (n : ℝ) := by
      exact (Nat.le_ceil (max 0 (X * lowerLoss k))).trans (by exact_mod_cast hn)
    have hmul : X * lowerLoss k ≤ (n : ℝ) :=
      (le_max_right _ _).trans hnreal
    exact (le_div_iff₀ (hlower k)).2 hmul |>.trans hx
  exact exists_slow_scale hfixed

end Erdos49.Qualitative
