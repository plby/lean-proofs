import ErdosProblems.Erdos239.External.Erdos67.LogFourierPhase
import ErdosProblems.Erdos239.External.Erdos67.LogPhaseHigherDerivative
import ErdosProblems.Erdos239.External.Erdos67.LSeriesLogPhaseBridge

/-!
# Residue-class logarithmic sums as consecutive real-shifted phases

This file gives the exact reindexing needed to apply a consecutive-interval
Weyl estimate to one residue class modulo a positive integer.  The first
integer in the residue class at or above the left endpoint is selected by
well-ordering; the selected terms are then an initial range with common
difference the modulus.

After passing to real logarithms, that common difference contributes only a
constant Fourier phase of norm one.  Consequently the norm of the residue
class sum is *equal* to the norm of a consecutive logarithmic-phase sum with
a positive real starting point.
-/

open scoped BigOperators

namespace Erdos67.ResidueLogPhase

noncomputable section

open Erdos1149
open Erdos67.LogPhaseSum
open Erdos67.LSeriesLogPhaseBridge
open Erdos67.LogPhaseHigherDerivative

/-- Positive coefficient used after removing the harmless global sign of a
logarithmic Fourier phase. -/
def positiveLogCoefficient (t : ℝ) : ℝ :=
  |t| / (2 * Real.pi)

theorem positiveLogCoefficient_pos {t : ℝ} (ht : t ≠ 0) :
    0 < positiveLogCoefficient t := by
  unfold positiveLogCoefficient
  positivity

theorem normalizedLogArgument_eq_shiftedLogPhase_of_nonpos
    {t U : ℝ} (ht : t ≤ 0) (j : ℕ) :
    normalizedLogArgument t (U + j) =
      shiftedLogPhase (positiveLogCoefficient t) U j := by
  unfold normalizedLogArgument shiftedLogPhase positiveLogCoefficient
  rw [abs_of_nonpos ht]
  ring

theorem normalizedLogArgument_eq_neg_shiftedLogPhase_of_nonneg
    {t U : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    normalizedLogArgument t (U + j) =
      -shiftedLogPhase (positiveLogCoefficient t) U j := by
  unfold normalizedLogArgument shiftedLogPhase positiveLogCoefficient
  rw [abs_of_nonneg ht]
  ring

theorem phase_neg (x : ℝ) :
    HigherDerivative.phase (-x) =
      starRingEnd ℂ (HigherDerivative.phase x) := by
  have h := HigherDerivative.phase_sub 0 x
  have hzero : HigherDerivative.phase 0 = 1 := by
    change ((Real.fourierChar 0 : Circle) : ℂ) = 1
    simp
  rw [hzero, one_mul] at h
  simpa only [zero_sub] using h

/-- Removing the sign of the height does not change the norm of a finite
logarithmic Fourier sum. -/
theorem norm_sum_normalizedLogArgument_eq_positive
    (t U : ℝ) (P : ℕ) :
    ‖∑ j ∈ Finset.range P,
        HigherDerivative.phase (normalizedLogArgument t (U + j))‖ =
      ‖∑ j ∈ Finset.range P,
        HigherDerivative.phase (shiftedLogPhase
          (positiveLogCoefficient t) U j)‖ := by
  rcases le_total t 0 with ht | ht
  · simp_rw [normalizedLogArgument_eq_shiftedLogPhase_of_nonpos ht]
  · simp_rw [normalizedLogArgument_eq_neg_shiftedLogPhase_of_nonneg ht,
      phase_neg]
    rw [← map_sum, Complex.norm_conj]

/-- There is an index whose representative in the residue class `c` lies at
or above `A`. -/
theorem exists_residueIndex_ge {q A : ℕ} [NeZero q] (c : ZMod q) :
    ∃ k : ℕ, A ≤ c.val + q * k := by
  have hq : 1 ≤ q := Nat.pos_of_ne_zero (NeZero.ne q)
  refine ⟨A, le_trans ?_ (Nat.le_add_left (q * A) c.val)⟩
  simpa only [one_mul] using Nat.mul_le_mul_right A hq

/-- The least index whose standard representative lies at or above `A`. -/
def firstResidueIndex {q : ℕ} [NeZero q] (A : ℕ) (c : ZMod q) : ℕ :=
  Nat.find (exists_residueIndex_ge (A := A) c)

/-- The first natural number congruent to `c` modulo `q` which is at least
`A`. -/
def firstResidueAtOrAbove {q : ℕ} [NeZero q] (A : ℕ) (c : ZMod q) : ℕ :=
  c.val + q * firstResidueIndex A c

theorem le_firstResidueAtOrAbove {q A : ℕ} [NeZero q] (c : ZMod q) :
    A ≤ firstResidueAtOrAbove A c := by
  exact Nat.find_spec (exists_residueIndex_ge (A := A) c)

theorem firstResidueIndex_min {q A k : ℕ} [NeZero q] (c : ZMod q)
    (hk : A ≤ c.val + q * k) :
    firstResidueIndex A c ≤ k := by
  exact Nat.find_min' (exists_residueIndex_ge (A := A) c) hk

/-- The number of members of the residue class in `[A,M]`. -/
def residueIntervalLength {q : ℕ} [NeZero q]
    (A M : ℕ) (c : ZMod q) : ℕ :=
  if firstResidueAtOrAbove A c ≤ M then
    (M - firstResidueAtOrAbove A c) / q + 1
  else 0

theorem residueClassSum_Icc_eq_sum_range
    {q A M : ℕ} [NeZero q] (c : ZMod q) (u : ℕ → ℂ) :
    residueClassSum (Finset.Icc A M) c u =
      ∑ j ∈ Finset.range (residueIntervalLength A M c),
        u (firstResidueAtOrAbove A c + q * j) := by
  classical
  unfold residueClassSum
  let k₀ := firstResidueIndex A c
  let n₀ := firstResidueAtOrAbove A c
  let P := residueIntervalLength A M c
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hn₀ : n₀ = c.val + q * k₀ := rfl
  apply Finset.sum_bij
      (fun n hn ↦ (n - n₀) / q)
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases (ZMod.natCast_eq_iff q n c).mp hn.2 with ⟨k, hk⟩
    have hk₀ : k₀ ≤ k :=
      firstResidueIndex_min c (by simpa only [hk] using hn.1.1)
    have hn₀n : n₀ ≤ n := by
      rw [hn₀, hk]
      exact Nat.add_le_add_left (Nat.mul_le_mul_left q hk₀) c.val
    have hdiff : n - n₀ = q * (k - k₀) := by
      rw [hn₀, hk, Nat.add_sub_add_left, Nat.mul_sub_left_distrib]
    have hdiv : (n - n₀) / q = k - k₀ := by
      rw [hdiff, Nat.mul_div_cancel_left _ hq]
    have hn₀M : n₀ ≤ M := hn₀n.trans hn.1.2
    change firstResidueAtOrAbove A c ≤ M at hn₀M
    simp only [P, residueIntervalLength, if_pos hn₀M, Finset.mem_range]
    rw [hdiv]
    apply Nat.lt_succ_of_le
    rw [Nat.le_div_iff_mul_le hq]
    have hmul : q * (k - k₀) = n - n₀ := hdiff.symm
    rw [mul_comm, hmul]
    change n - n₀ ≤ M - n₀
    exact Nat.sub_le_sub_right hn.1.2 n₀
  · intro n₁ hn₁ n₂ hn₂ heq
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn₁ hn₂
    rcases (ZMod.natCast_eq_iff q n₁ c).mp hn₁.2 with ⟨k₁, hk₁⟩
    rcases (ZMod.natCast_eq_iff q n₂ c).mp hn₂.2 with ⟨k₂, hk₂⟩
    have hk₀₁ : k₀ ≤ k₁ :=
      firstResidueIndex_min c (by simpa only [hk₁] using hn₁.1.1)
    have hk₀₂ : k₀ ≤ k₂ :=
      firstResidueIndex_min c (by simpa only [hk₂] using hn₂.1.1)
    have hd₁ : n₁ - n₀ = q * (k₁ - k₀) := by
      rw [hn₀, hk₁, Nat.add_sub_add_left, Nat.mul_sub_left_distrib]
    have hd₂ : n₂ - n₀ = q * (k₂ - k₀) := by
      rw [hn₀, hk₂, Nat.add_sub_add_left, Nat.mul_sub_left_distrib]
    rw [hd₁, hd₂, Nat.mul_div_cancel_left _ hq,
      Nat.mul_div_cancel_left _ hq] at heq
    have : k₁ = k₂ := tsub_inj_left hk₀₁ hk₀₂ heq
    simpa [hk₁, hk₂, this]
  · intro j hj
    simp only [Finset.mem_range] at hj
    let n := n₀ + q * j
    have hn₀M : n₀ ≤ M := by
      by_contra hnot
      have hzero : residueIntervalLength A M c = 0 := by
        have hnot' : ¬ firstResidueAtOrAbove A c ≤ M := by
          simpa only [n₀] using hnot
        dsimp only [residueIntervalLength]
        rw [if_neg hnot']
      rw [hzero] at hj
      omega
    change firstResidueAtOrAbove A c ≤ M at hn₀M
    have hjle : j ≤ (M - n₀) / q := by
      simpa only [P, residueIntervalLength, if_pos hn₀M,
        Nat.lt_add_one_iff] using hj
    have hqj : q * j ≤ M - n₀ := by
      simpa only [mul_comm] using (Nat.le_div_iff_mul_le hq).mp hjle
    have hnM : n ≤ M := by
      dsimp only [n]
      omega
    have hAn : A ≤ n := by
      exact (le_firstResidueAtOrAbove c).trans (Nat.le_add_right n₀ (q * j))
    have hncast : (n : ZMod q) = c := by
      apply (ZMod.natCast_eq_iff q n c).2
      refine ⟨k₀ + j, ?_⟩
      dsimp only [n]
      rw [hn₀]
      ring
    refine ⟨n, ?_, ?_⟩
    · exact Finset.mem_filter.2 ⟨Finset.mem_Icc.2 ⟨hAn, hnM⟩, hncast⟩
    ·
      dsimp only [n]
      rw [Nat.add_sub_cancel_left, Nat.mul_div_cancel_left _ hq]
  · intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    rcases (ZMod.natCast_eq_iff q n c).mp hn.2 with ⟨k, hk⟩
    have hk₀ : k₀ ≤ k :=
      firstResidueIndex_min c (by simpa only [hk] using hn.1.1)
    have hdiff : n - n₀ = q * (k - k₀) := by
      rw [hn₀, hk, Nat.add_sub_add_left, Nat.mul_sub_left_distrib]
    congr 1
    rw [hdiff, Nat.mul_div_cancel_left _ hq]
    change n = n₀ + q * (k - k₀)
    rw [hn₀, hk, Nat.mul_sub_left_distrib]
    have hmul : q * k₀ ≤ q * k := Nat.mul_le_mul_left q hk₀
    omega

/-- The first selected residue representative is positive when the original
left endpoint is positive. -/
theorem firstResidueAtOrAbove_pos {q A : ℕ} [NeZero q] (c : ZMod q)
    (hA : 0 < A) : 0 < firstResidueAtOrAbove A c :=
  hA.trans_le (le_firstResidueAtOrAbove c)

/-- Exact splitting of the logarithmic Fourier phase along a positive
arithmetic progression. -/
theorem natLogTwist_firstResidue_add_mul
    {q A : ℕ} [NeZero q] (c : ZMod q) (t : ℝ) (hA : 0 < A) (j : ℕ) :
    natLogTwist (firstResidueAtOrAbove A c + q * j) t =
      HigherDerivative.phase (normalizedLogArgument t q) *
        HigherDerivative.phase
          (normalizedLogArgument t
            ((firstResidueAtOrAbove A c : ℝ) / q + j)) := by
  have hq : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hn₀ : 0 < firstResidueAtOrAbove A c :=
    firstResidueAtOrAbove_pos c hA
  have hshift : 0 < (firstResidueAtOrAbove A c : ℝ) / q + j := by
    positivity
  rw [← higherDerivative_phase_normalizedLogArgument_nat t]
  · have harg :
        normalizedLogArgument t
            ((firstResidueAtOrAbove A c + q * j : ℕ) : ℝ) =
          normalizedLogArgument t q +
            normalizedLogArgument t
              ((firstResidueAtOrAbove A c : ℝ) / q + j) := by
      unfold normalizedLogArgument
      rw [show ((firstResidueAtOrAbove A c + q * j : ℕ) : ℝ) =
        (q : ℝ) * ((firstResidueAtOrAbove A c : ℝ) / q + j) by
        push_cast
        field_simp,
        Real.log_mul (by positivity) hshift.ne']
      ring
    rw [harg]
    change ((Real.fourierChar (_ + _) : Circle) : ℂ) =
      ((Real.fourierChar _ : Circle) : ℂ) *
        ((Real.fourierChar _ : Circle) : ℂ)
    rw [AddChar.map_add_eq_mul, Circle.coe_mul]
  · positivity

/-- A residue-class logarithmic sum is norm-identical to a consecutive
real-shifted logarithmic Fourier sum. -/
theorem norm_residueClassSum_natLogTwist_eq
    {q A M : ℕ} [NeZero q] (c : ZMod q) (t : ℝ) (hA : 0 < A) :
    ‖residueClassSum (Finset.Icc A M) c
        (fun n ↦ natLogTwist n t)‖ =
      ‖∑ j ∈ Finset.range (residueIntervalLength A M c),
          HigherDerivative.phase
            (normalizedLogArgument t
              ((firstResidueAtOrAbove A c : ℝ) / q + j))‖ := by
  rw [residueClassSum_Icc_eq_sum_range]
  simp_rw [natLogTwist_firstResidue_add_mul c t hA]
  rw [← Finset.mul_sum, norm_mul]
  have hqN : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hq : 0 < (q : ℝ) := by exact_mod_cast hqN
  rw [show ‖HigherDerivative.phase (normalizedLogArgument t q)‖ = 1 by
    rw [higherDerivative_phase_normalizedLogArgument t hq]
    exact norm_logPhase t hq]
  simp

/-- Final source-facing form of the residue adapter: the right side is the
positive-coefficient shifted logarithmic phase consumed by the controlled
Weyl estimates. -/
theorem norm_residueClassSum_natLogTwist_eq_positiveShifted
    {q A M : ℕ} [NeZero q] (c : ZMod q) (t : ℝ) (hA : 0 < A) :
    ‖residueClassSum (Finset.Icc A M) c
        (fun n ↦ natLogTwist n t)‖ =
      ‖∑ j ∈ Finset.range (residueIntervalLength A M c),
          HigherDerivative.phase
            (shiftedLogPhase (positiveLogCoefficient t)
              ((firstResidueAtOrAbove A c : ℝ) / q) j)‖ := by
  rw [norm_residueClassSum_natLogTwist_eq c t hA]
  exact norm_sum_normalizedLogArgument_eq_positive t
    ((firstResidueAtOrAbove A c : ℝ) / q)
    (residueIntervalLength A M c)

end

end Erdos67.ResidueLogPhase
