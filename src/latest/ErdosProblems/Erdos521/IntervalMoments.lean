/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Moment bounds for intervals contained in a controlled local disk.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.UniformLocalMoments
import ErdosProblems.Erdos521.EndpointCover

namespace Erdos521

open MeasureTheory Filter

theorem intervalRootCount_le (ε : ℕ → ℝ) (n : ℕ) (a b : ℝ) : intervalRootCount ε n a b ≤ n :=
  (Finset.card_filter_le _ _).trans (rootCount_le ε n)

theorem intervalRootCount_pow_integrable (n p : ℕ) (a b : ℝ) :
    Integrable (fun ε ↦ (intervalRootCount ε n a b : ℝ) ^ p) sequenceLaw :=
  bounded_nat_pow_integrable sequenceLaw (intervalRootCount_aemeasurable n a b) n p
    (fun ε ↦ intervalRootCount_le ε n a b)

theorem intervalRootCount_le_localRight (ε : ℕ → ℝ) (n : ℕ) {a b r : ℝ}
    (hwidth : b - a ≤ r) : intervalRootCount ε n a b ≤ localRootCount ε n b r := by
  classical
  apply Finset.card_le_card
  intro x hx
  obtain ⟨hxroot, hxI⟩ := Finset.mem_filter.mp hx
  apply Finset.mem_filter.mpr
  refine ⟨hxroot, ?_⟩
  rw [abs_of_nonpos (sub_nonpos.mpr hxI.2)]
  linarith [hxI.1]

theorem eventually_bulk_interval_moments (p : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ a b : ℝ,
      b ∈ Set.Icc (9 / 10 : ℝ) (endpointCenter (localMomentBulkConstant p) n) →
      b - a ≤ (1 - b) / 8 →
      (∫ ε, (intervalRootCount ε n a b : ℝ) ^ p ∂sequenceLaw) ≤ localMomentBoundConstant p := by
  filter_upwards [eventually_bulk_local_moments p] with n hn
  intro a b hb hwidth
  apply le_trans _ (hn b hb)
  apply integral_mono (intervalRootCount_pow_integrable n p a b)
    (localRootCount_pow_integrable n p b ((1 - b) / 8))
  intro ε
  exact pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (intervalRootCount_le_localRight ε n hwidth)) p

end Erdos521
