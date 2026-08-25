import StackExchange.Puzzling139335.ArcVariation.Concatenation
import StackExchange.Puzzling139335.ArcVariation.Finiteness

/-!
# Finite ordered cuts of arc variation

Only the initial segment `t 0, ..., t m` of the cut sequence is used.  Thus the
monotonicity assumption is restricted to this finite set of indices.  Repeated
cut points and degenerate component intervals are permitted.
-/

open Set

namespace Puzzling139335.LoopVariation

open ArcVariation

noncomputable section

variable {α X : Type*} [LinearOrder α] [PseudoMetricSpace X]

/-- Sum of the arc variations on the `m` consecutive parameter intervals. -/
def cutSum (ε : ℝ) (f : α → X) (t : ℕ → α) (m : ℕ) : ℝ :=
  ∑ i ∈ Finset.range m, variationOn ε f (Icc (t i) (t (i + 1)))

@[simp] theorem cutSum_zero (ε : ℝ) (f : α → X) (t : ℕ → α) :
    cutSum ε f t 0 = 0 := by
  simp [cutSum]

theorem cutSum_succ (ε : ℝ) (f : α → X) (t : ℕ → α) (m : ℕ) :
    cutSum ε f t (m + 1) =
      cutSum ε f t m + variationOn ε f (Icc (t m) (t (m + 1))) :=
  Finset.sum_range_succ _ _

private theorem arcScores_subset {ε : ℝ} {f : α → X} {a b c d : α}
    (hac : a ≤ c) (hdb : d ≤ b) :
    scoresOn ε f (Icc c d) ⊆ scoresOn ε f (Icc a b) := by
  rintro _ ⟨xs, hxs, rfl⟩
  refine ⟨xs, ⟨hxs.1, ?_⟩, rfl⟩
  intro x hx
  exact ⟨hac.trans (hxs.2 x hx).1, (hxs.2 x hx).2.trans hdb⟩

/-- An `n + 1`-interval partition loses at most `n` penalties.  Finiteness of
all smaller interval score sets is inherited from the whole interval. -/
theorem arc_partition_estimates_succ {ε : ℝ} {f : α → X}
    (hε : 0 ≤ ε) (n : ℕ) {t : ℕ → α}
    (ht : MonotoneOn t (Icc 0 (n + 1)))
    (hb : BddAbove (scoresOn ε f (Icc (t 0) (t (n + 1))))) :
    cutSum ε f t (n + 1) ≤ variationOn ε f (Icc (t 0) (t (n + 1))) ∧
      variationOn ε f (Icc (t 0) (t (n + 1))) ≤
        cutSum ε f t (n + 1) + (n : ℝ) * ε := by
  induction n with
  | zero => simp [cutSum]
  | succ n ih =>
      have ht' : MonotoneOn t (Icc 0 (n + 1)) := ht.mono (by
        intro i hi
        exact ⟨hi.1, hi.2.trans (by omega)⟩)
      have hstart : t 0 ≤ t (n + 1) :=
        ht ⟨le_rfl, by omega⟩ ⟨by omega, by omega⟩ (by omega)
      have hlast : t (n + 1) ≤ t (n + 1 + 1) :=
        ht ⟨by omega, by omega⟩ ⟨by omega, le_rfl⟩ (by omega)
      have hprefix : BddAbove (scoresOn ε f (Icc (t 0) (t (n + 1)))) :=
        hb.mono (arcScores_subset le_rfl hlast)
      have hlastbdd : BddAbove (scoresOn ε f (Icc (t (n + 1)) (t (n + 1 + 1)))) :=
        hb.mono (arcScores_subset hstart le_rfl)
      have hprev := ih ht' hprefix
      have hjoin := variationOn_concatenation hε hstart hlast hb hprefix hlastbdd
      rw [cutSum_succ ε f t (n + 1)]
      push_cast
      constructor
      · linarith [hprev.1, hjoin.1]
      · linarith [hprev.2, hjoin.2]

/-- For `m > 0` consecutive intervals, total arc variation differs from the
sum of the restrictions by a nonnegative error at most `(m - 1) * ε`. -/
theorem arc_partition_estimates {ε : ℝ} {f : α → X} {t : ℕ → α} {m : ℕ}
    (hm : 0 < m) (hε : 0 ≤ ε) (ht : MonotoneOn t (Icc 0 m))
    (hb : BddAbove (scoresOn ε f (Icc (t 0) (t m)))) :
    cutSum ε f t m ≤ variationOn ε f (Icc (t 0) (t m)) ∧
      variationOn ε f (Icc (t 0) (t m)) ≤
        cutSum ε f t m + ((m - 1 : ℕ) : ℝ) * ε := by
  cases m with
  | zero => omega
  | succ n => simpa using arc_partition_estimates_succ hε n ht hb

end

noncomputable section

variable {X : Type*} [PseudoMetricSpace X]

/-- Continuous positive-resolution version of the finite arc partition bounds,
with boundedness supplied by compactness and uniform continuity. -/
theorem arc_partition_estimates_of_continuousOn
    {ε : ℝ} {f : ℝ → X} {t : ℕ → ℝ} {m : ℕ}
    (hm : 0 < m) (hε : 0 < ε) (ht : MonotoneOn t (Icc 0 m))
    (hf : ContinuousOn f (Icc (t 0) (t m))) :
    cutSum ε f t m ≤ variationOn ε f (Icc (t 0) (t m)) ∧
      variationOn ε f (Icc (t 0) (t m)) ≤
        cutSum ε f t m + ((m - 1 : ℕ) : ℝ) * ε := by
  have hends : t 0 ≤ t m :=
    ht ⟨le_rfl, Nat.zero_le m⟩ ⟨Nat.zero_le m, le_rfl⟩ (Nat.zero_le m)
  exact arc_partition_estimates hm hε.le ht (bddAbove_scoresOn_Icc hends hf hε)

end

end Puzzling139335.LoopVariation
