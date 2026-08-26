/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Deterministic cone records for Erdős Problem 521.
Informal proof: the 29 April 2026 working note, Section 7; Rob Sneiderman.
Formal proof: Codex.
https://web.math.pmf.unizg.hr/~vjekovac/files/Erdos_521_Kac.pdf
https://github.com/Robby955/erdos-521-zero-one
-/
import ErdosProblems.Erdos521.Abel

namespace Erdos521

open scoped BigOperators

/-- The first `n` increments; in particular the empty prefix is zero. -/
def prefixSum (a : ℕ → ℝ) (n : ℕ) : ℝ := ∑ k ∈ Finset.range n, a k

theorem prefixSum_succ (a : ℕ → ℝ) (n : ℕ) :
    prefixSum a (n + 1) = prefixSum a n + a n := by
  exact Finset.sum_range_succ _ _

/-- Initial partial sums of a reversed list are terminal sums of the original list. -/
theorem partialSum_reverse (a : ℕ → ℝ) (m r : ℕ) (hr : r ≤ m) :
    partialSum (fun k ↦ a (m - k)) r = prefixSum a (m + 1) - prefixSum a (m - r) := by
  induction r with
  | zero => simp [partialSum, prefixSum, Finset.sum_range_succ]
  | succ r ih =>
    have hstep : m - r = (m - (r + 1)) + 1 := by omega
    have hprev := ih (by omega)
    rw [show partialSum (fun k ↦ a (m - k)) (r + 1) =
        partialSum (fun k ↦ a (m - k)) r + a (m - (r + 1)) by
      exact Finset.sum_range_succ _ _]
    rw [hprev, hstep, prefixSum_succ a (m - (r + 1))]
    ring

/-- Record at time `m`: all terminal increment sums lie in the cone.
The comparison `k = 0` is the comparison with the initial point. -/
def ConeRecord (a b : ℕ → ℝ) (m : ℕ) : Prop :=
  ∀ k ≤ m, InCone (prefixSum a (m + 1) - prefixSum a k)
    (prefixSum b (m + 1) - prefixSum b k)

/-- The record condition in the exact coefficient order needed for reversal. -/
def CoefficientRecord (ε : ℕ → ℝ) (m : ℕ) : Prop :=
  ConeRecord (fun i ↦ ε (2 * i + 1)) (fun i ↦ ε (2 * i)) m

theorem coneRecord_reverse (a b : ℕ → ℝ) (m : ℕ) (h : ConeRecord a b m)
    (r : ℕ) (hr : r ≤ m) :
    InCone (partialSum (fun k ↦ a (m - k)) r)
      (partialSum (fun k ↦ b (m - k)) r) := by
  rw [partialSum_reverse a m r hr, partialSum_reverse b m r hr]
  exact h (m - r) (Nat.sub_le _ _)

theorem coefficientRecord_leading_pos (ε : ℕ → ℝ) (m : ℕ)
    (h : CoefficientRecord ε m) (hne : ε (2 * m + 1) ≠ 0) :
    0 < ε (2 * m + 1) := by
  have hc := h m le_rfl
  simp only [prefixSum_succ, add_sub_cancel_left] at hc
  exact lt_of_le_of_ne ((abs_nonneg _).trans hc) (Ne.symm hne)

/-- On a coefficient record, the reversed odd-degree polynomial is positive
throughout the open unit interval. -/
theorem coefficientRecord_reverse_pos (ε : ℕ → ℝ) (m : ℕ)
    (h : CoefficientRecord ε m) (hne : ε (2 * m + 1) ≠ 0)
    (x : ℝ) (hx : |x| < 1) :
    0 < powerSum (fun k ↦ ε (2 * m + 1 - k)) (2 * m + 2) x := by
  have hlen : 2 * m + 2 = 2 * (m + 1) := by omega
  rw [hlen, powerSum_pair]
  have hc : ∀ r ≤ m,
      InCone (partialSum (fun k ↦ ε (2 * m + 1 - 2 * k)) r)
        (partialSum (fun k ↦ ε (2 * m + 1 - (2 * k + 1))) r) := by
    intro r hr
    have heq : partialSum (fun k ↦ ε (2 * m + 1 - 2 * k)) r =
        partialSum (fun k ↦ ε (2 * (m - k) + 1)) r := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ m := (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans hr
      change ε (2 * m + 1 - 2 * k) = ε (2 * (m - k) + 1)
      congr 1
      omega
    have hoeq : partialSum (fun k ↦ ε (2 * m + 1 - (2 * k + 1))) r =
        partialSum (fun k ↦ ε (2 * (m - k))) r := by
      apply Finset.sum_congr rfl
      intro k hk
      have hk' : k ≤ m := (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans hr
      change ε (2 * m + 1 - (2 * k + 1)) = ε (2 * (m - k))
      congr 1
      omega
    rw [heq, hoeq]
    exact coneRecord_reverse _ _ m h r hr
  apply cone_powerSum_pos _ _ m hc _ x hx
  simpa using coefficientRecord_leading_pos ε m h hne

/-- A cone record forces every real zero of the corresponding odd-degree
polynomial to belong to `[-1,1]`. No assertion about endpoint zeros is needed. -/
theorem coefficientRecord_no_exterior_root (ε : ℕ → ℝ) (m : ℕ)
    (h : CoefficientRecord ε m) (hne : ε (2 * m + 1) ≠ 0)
    (x : ℝ) (hx : 1 < |x|) : powerSum ε (2 * m + 2) x ≠ 0 := by
  have hx0 : x ≠ 0 := by
    intro heq
    norm_num [heq] at hx
  have hxinv : |x⁻¹| < 1 := by
    rw [abs_inv]
    exact (inv_lt_one₀ (lt_trans zero_lt_one hx)).mpr hx
  have hpos := coefficientRecord_reverse_pos ε m h hne x⁻¹ hxinv
  have hid := reverse_powerSum_mul ε (2 * m + 1) x hx0
  intro hzero
  rw [hzero] at hid
  exact (mul_ne_zero (ne_of_gt hpos) (pow_ne_zero _ hx0)) hid

/-- Prefix sums after discarding the first `r` increments. -/
theorem prefixSum_shift (a : ℕ → ℝ) (r n : ℕ) :
    prefixSum (fun i ↦ a (r + i)) n = prefixSum a (r + n) - prefixSum a r := by
  induction n with
  | zero => simp [prefixSum]
  | succ n ih =>
    rw [prefixSum_succ, ih, ← Nat.add_assoc, prefixSum_succ a (r + n)]
    ring

/-- A global record remains a record after deleting an earlier prefix. -/
theorem ConeRecord.shift {a b : ℕ → ℝ} {r n : ℕ} (h : ConeRecord a b (r + n)) :
    ConeRecord (fun i ↦ a (r + i)) (fun i ↦ b (r + i)) n := by
  intro k hk
  simp only [prefixSum_shift]
  have ha : prefixSum a (r + (n + 1)) - prefixSum a r -
      (prefixSum a (r + k) - prefixSum a r) =
      prefixSum a (r + n + 1) - prefixSum a (r + k) := by
    rw [Nat.add_assoc]
    ring
  have hb : prefixSum b (r + (n + 1)) - prefixSum b r -
      (prefixSum b (r + k) - prefixSum b r) =
      prefixSum b (r + n + 1) - prefixSum b (r + k) := by
    rw [Nat.add_assoc]
    ring
  rw [ha, hb]
  exact h (r + k) (Nat.add_le_add_left hk r)

/-- Unboundedly many record times. -/
def InfiniteRecords (a b : ℕ → ℝ) : Prop :=
  ∀ N : ℕ, ∃ m, N ≤ m ∧ ConeRecord a b m

/-- The pointwise inclusion behind the finite-prefix zero-one argument.
Only this direction is asserted; pointwise tail invariance is not needed. -/
theorem InfiniteRecords.shift {a b : ℕ → ℝ} (h : InfiniteRecords a b) (r : ℕ) :
    InfiniteRecords (fun i ↦ a (r + i)) (fun i ↦ b (r + i)) := by
  intro N
  obtain ⟨m, hm, hrecord⟩ := h (r + N)
  refine ⟨m - r, by omega, ?_⟩
  apply ConeRecord.shift
  simpa [Nat.add_sub_of_le (show r ≤ m by omega)] using hrecord

/-- Record comparisons against only the portion of the path starting at `r`. -/
def ConeRecordFrom (a b : ℕ → ℝ) (r m : ℕ) : Prop :=
  ∀ k, r ≤ k → k ≤ m → InCone (prefixSum a (m + 1) - prefixSum a k)
    (prefixSum b (m + 1) - prefixSum b k)

theorem coneRecordFrom_iff_shift (a b : ℕ → ℝ) (r n : ℕ) :
    ConeRecordFrom a b r (r + n) ↔
      ConeRecord (fun i ↦ a (r + i)) (fun i ↦ b (r + i)) n := by
  constructor
  · intro h k hk
    simp only [prefixSum_shift, sub_sub_sub_cancel_right]
    simpa only [Nat.add_assoc] using h (r + k) (by omega) (by omega)
  · intro h k hrk hkn
    have hh := h (k - r) (by omega)
    simp only [prefixSum_shift, sub_sub_sub_cancel_right,
      Nat.add_sub_of_le hrk] at hh
    simpa only [Nat.add_assoc] using hh

/-- The exact event decomposition used before applying independence to
disjoint blocks of increments. -/
theorem coneRecord_decomposition (a b : ℕ → ℝ) (m l : ℕ) (hml : m < l) :
    (ConeRecord a b m ∧ ConeRecord a b l) ↔
      (ConeRecord a b m ∧ ConeRecordFrom a b (m + 1) l) := by
  constructor
  · rintro ⟨hm, hl⟩
    exact ⟨hm, fun k _ hk ↦ hl k hk⟩
  · rintro ⟨hm, hseg⟩
    refine ⟨hm, fun k hk ↦ ?_⟩
    by_cases hkm : k ≤ m
    · have h₁ := hseg (m + 1) le_rfl (by omega)
      have h₂ := hm k hkm
      have hsum := inCone_add h₁ h₂
      convert hsum using 1 <;> ring
    · exact hseg k (by omega) hk

end Erdos521
