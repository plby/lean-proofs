/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos175.ReciprocalExpSumBound
import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# The one-step reciprocal exponential-sum bound

This file treats the middle-frequency branch of Granville--Ramaré,
Proposition 8.1.  One Weyl differencing step is followed by the concrete
Kusmin--Landau estimate for a first difference of the reciprocal phase.
-/

namespace Erdos175

open scoped BigOperators

noncomputable section

private lemma finiteHarmonic_le_one_add_log_k1 (H : ℕ) :
    finiteHarmonic H ≤ 1 + Real.log H := by
  have heq : finiteHarmonic H = (harmonic H : ℝ) := by
    unfold finiteHarmonic harmonic
    simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [heq]
  exact harmonic_le_one_add_log H

/-- One Weyl step, followed by a `K/(r+1)` estimate for every terminal
correlation. -/
theorem reciprocalExpRange_sq_le_of_terminal
    (x : ℝ) (C N q : ℕ) (hq : 1 ≤ q) (hqN : q ≤ N)
    (K : ℝ) (_hK : 0 ≤ K)
    (hterminal : ∀ r < q,
      ‖∑ n ∈ Finset.range (N - (r + 1)),
        positiveCorrelation
          (fun j ↦ e (reciprocalPhase x (C + j))) r n‖ ≤
        K * (((r + 1 : ℕ) : ℝ))⁻¹) :
    ‖reciprocalExpRange x C N‖ ^ 2 ≤
      2 * (N : ℝ) ^ 2 / (q : ℝ) +
        4 * (N : ℝ) * K / (q : ℝ) * finiteHarmonic q := by
  have hqpos : 0 < q := by omega
  have hNpos : 0 < N := lt_of_lt_of_le hqpos hqN
  let z : ℕ → ℂ := fun j ↦ e (reciprocalPhase x (C + j))
  have hz : ∀ n < N, ‖z n‖ ≤ 1 := by
    intro n hn
    simp [z]
  have hweyl := VanDerCorput.normalized_sq_norm_sum_le_positiveCorrelations_ambient
    z N N q hNpos hqpos (by rfl) hqN hz
  have hsum :
      (∑ r ∈ Finset.range q,
        ‖∑ n ∈ Finset.range (N - (r + 1)),
          positiveCorrelation z r n‖ / (N : ℝ)) ≤
        K / (N : ℝ) * finiteHarmonic q := by
    calc
      _ ≤ ∑ r ∈ Finset.range q,
          (K * (((r + 1 : ℕ) : ℝ))⁻¹) / (N : ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        exact div_le_div_of_nonneg_right
          (hterminal r (Finset.mem_range.mp hr)) (by positivity)
      _ = K / (N : ℝ) * finiteHarmonic q := by
        unfold finiteHarmonic
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _hr
        ring
  have hnormalized :
      (‖reciprocalExpRange x C N‖ / (N : ℝ)) ^ 2 ≤
        2 / (q : ℝ) +
          4 / (q : ℝ) * (K / (N : ℝ) * finiteHarmonic q) := by
    rw [reciprocalExpRange]
    have hcoef : 0 ≤ 4 / (q : ℝ) := by positivity
    have hweighted := mul_le_mul_of_nonneg_left hsum hcoef
    exact hweyl.trans (add_le_add_right hweighted _)
  have hscale : 0 < (N : ℝ) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hnormalized hscale.le
  calc
    ‖reciprocalExpRange x C N‖ ^ 2 =
        (‖reciprocalExpRange x C N‖ / (N : ℝ)) ^ 2 * (N : ℝ) ^ 2 := by
      field_simp
    _ ≤ (2 / (q : ℝ) +
          4 / (q : ℝ) * (K / (N : ℝ) * finiteHarmonic q)) *
          (N : ℝ) ^ 2 := hmul
    _ = 2 * (N : ℝ) ^ 2 / (q : ℝ) +
        4 * (N : ℝ) * K / (q : ℝ) * finiteHarmonic q := by
      field_simp

/-- Ambient-length version of the preceding one-step inequality.  This is
the form needed for arbitrary subintervals of a fixed dyadic block. -/
theorem reciprocalExpRange_sq_le_of_terminal_ambient
    (x : ℝ) (C L M q : ℕ) (hM : 0 < M) (hq : 1 ≤ q)
    (hLM : L ≤ M) (hqM : q ≤ M)
    (K : ℝ) (_hK : 0 ≤ K)
    (hterminal : ∀ r < q,
      ‖∑ n ∈ Finset.range (L - (r + 1)),
        positiveCorrelation
          (fun j ↦ e (reciprocalPhase x (C + j))) r n‖ ≤
        K * (((r + 1 : ℕ) : ℝ))⁻¹) :
    ‖reciprocalExpRange x C L‖ ^ 2 ≤
      2 * (M : ℝ) ^ 2 / (q : ℝ) +
        4 * (M : ℝ) * K / (q : ℝ) * finiteHarmonic q := by
  have hqpos : 0 < q := by omega
  let z : ℕ → ℂ := fun j ↦ e (reciprocalPhase x (C + j))
  have hz : ∀ n < L, ‖z n‖ ≤ 1 := by
    intro n hn
    simp [z]
  have hweyl := VanDerCorput.normalized_sq_norm_sum_le_positiveCorrelations_ambient
    z L M q hM hqpos hLM hqM hz
  have hsum :
      (∑ r ∈ Finset.range q,
        ‖∑ n ∈ Finset.range (L - (r + 1)),
          positiveCorrelation z r n‖ / (M : ℝ)) ≤
        K / (M : ℝ) * finiteHarmonic q := by
    calc
      _ ≤ ∑ r ∈ Finset.range q,
          (K * (((r + 1 : ℕ) : ℝ))⁻¹) / (M : ℝ) := by
        apply Finset.sum_le_sum
        intro r hr
        exact div_le_div_of_nonneg_right
          (hterminal r (Finset.mem_range.mp hr)) (by positivity)
      _ = K / (M : ℝ) * finiteHarmonic q := by
        unfold finiteHarmonic
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro r _hr
        ring
  have hnormalized :
      (‖reciprocalExpRange x C L‖ / (M : ℝ)) ^ 2 ≤
        2 / (q : ℝ) +
          4 / (q : ℝ) * (K / (M : ℝ) * finiteHarmonic q) := by
    rw [reciprocalExpRange]
    have hcoef : 0 ≤ 4 / (q : ℝ) := by positivity
    have hweighted := mul_le_mul_of_nonneg_left hsum hcoef
    exact hweyl.trans (add_le_add_right hweighted _)
  have hscale : 0 < (M : ℝ) ^ 2 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hnormalized hscale.le
  calc
    ‖reciprocalExpRange x C L‖ ^ 2 =
        (‖reciprocalExpRange x C L‖ / (M : ℝ)) ^ 2 * (M : ℝ) ^ 2 := by
      field_simp
    _ ≤ (2 / (q : ℝ) +
          4 / (q : ℝ) * (K / (M : ℝ) * finiteHarmonic q)) *
          (M : ℝ) ^ 2 := hmul
    _ = 2 * (M : ℝ) ^ 2 / (q : ℝ) +
        4 * (M : ℝ) * K / (q : ℝ) * finiteHarmonic q := by
      field_simp
/-- A first multiplicative correlation is the once-differenced reciprocal
phase used by the concrete Kusmin--Landau theorem. -/
lemma positiveCorrelation_reciprocal_eq_expPhase_onceDiff
    (x : ℝ) (C r n : ℕ) :
    positiveCorrelation (fun j ↦ e (reciprocalPhase x (C + j))) r n =
      expPhase (onceDiffReciprocal x (r + 1 : ℕ) (C + n : ℕ)) := by
  rw [expPhase_eq_e, positiveCorrelation_e]
  congr 1
  simp only [positivePhaseDifference, onceDiffReciprocal, onceDiff, reciprocalPhase]
  push_cast
  ring

/-- Concrete terminal bound for every first-order correlation, including
the ranges of length zero or one. -/
lemma terminalCorrelation_reciprocal_k1_le
    (x : ℝ) (C N q r : ℕ)
    (hx : 0 < x) (hC : 0 < C) (hr : r < q)
    (hderiv : 4 * x * (q : ℝ) ≤ (C : ℝ) ^ 3) :
    ‖∑ n ∈ Finset.range (N - (r + 1)),
        positiveCorrelation
          (fun j ↦ e (reciprocalPhase x (C + j))) r n‖ ≤
      ((C + N : ℕ) : ℝ) ^ 3 / (2 * x) * (((r + 1 : ℕ) : ℝ))⁻¹ := by
  let L : ℕ := N - (r + 1)
  have hrq : r + 1 ≤ q := by omega
  have hrqR : ((r + 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast hrq
  have hupper :
      4 * x * ((r + 1 : ℕ) : ℝ) / (C : ℝ) ^ 3 ≤ 1 := by
    have hC3 : 0 < (C : ℝ) ^ 3 := by positivity
    apply (div_le_iff₀ hC3).2
    calc
      4 * x * ((r + 1 : ℕ) : ℝ) ≤ 4 * x * (q : ℝ) := by gcongr
      _ ≤ (C : ℝ) ^ 3 := hderiv
      _ = 1 * (C : ℝ) ^ 3 := by ring
  have hlarge :
      2 ≤ ((C + N : ℕ) : ℝ) ^ 3 /
        (2 * x * ((r + 1 : ℕ) : ℝ)) := by
    have hden : 0 < 2 * x * ((r + 1 : ℕ) : ℝ) := by positivity
    apply (le_div_iff₀ hden).2
    have hCN : (C : ℝ) ≤ ((C + N : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_add_right C N)
    have hpow : (C : ℝ) ^ 3 ≤ ((C + N : ℕ) : ℝ) ^ 3 := by gcongr
    have hxr : 4 * x * ((r + 1 : ℕ) : ℝ) ≤ (C : ℝ) ^ 3 := by
      calc
        _ ≤ 4 * x * (q : ℝ) := by gcongr
        _ ≤ _ := hderiv
    nlinarith
  by_cases hL : 2 ≤ L
  · have hlength : L - 2 + 2 = L := by omega
    have hendNat : C + (L - 2 + 1) + (r + 1) ≤ C + N := by
      dsimp [L]
      omega
    have hend :
        (C : ℝ) + ((L - 2 + 1 : ℕ) : ℝ) + ((r + 1 : ℕ) : ℝ) ≤
          ((C + N : ℕ) : ℝ) := by
      exact_mod_cast hendNat
    have hKL := kusminLandau_onceDiffReciprocal
      x ((r + 1 : ℕ) : ℝ) (C : ℝ) ((C + N : ℕ) : ℝ) (L - 2)
      hx (by positivity) (by positivity) hend hupper
    calc
      ‖∑ n ∈ Finset.range (N - (r + 1)),
          positiveCorrelation
            (fun j ↦ e (reciprocalPhase x (C + j))) r n‖ =
          ‖∑ n ∈ Finset.range L,
            expPhase (onceDiffReciprocal x (r + 1 : ℕ) (C + n : ℕ))‖ := by
        dsimp [L]
        congr 1
        apply Finset.sum_congr rfl
        intro n _hn
        exact positiveCorrelation_reciprocal_eq_expPhase_onceDiff x C r n
      _ ≤ ((C + N : ℕ) : ℝ) ^ 3 /
          (2 * x * ((r + 1 : ℕ) : ℝ)) := by
        rw [← hlength]
        simpa only [Nat.cast_add] using hKL
      _ = ((C + N : ℕ) : ℝ) ^ 3 / (2 * x) *
          (((r + 1 : ℕ) : ℝ))⁻¹ := by field_simp
  · have hLtwo : L ≤ 1 := by omega
    calc
      ‖∑ n ∈ Finset.range (N - (r + 1)),
          positiveCorrelation
            (fun j ↦ e (reciprocalPhase x (C + j))) r n‖ ≤
          ∑ n ∈ Finset.range L,
            ‖positiveCorrelation
              (fun j ↦ e (reciprocalPhase x (C + j))) r n‖ := by
        dsimp [L]
        exact norm_sum_le _ _
      _ = (L : ℝ) := by simp [positiveCorrelation]
      _ ≤ 2 := by exact_mod_cast (show L ≤ 2 by omega)
      _ ≤ ((C + N : ℕ) : ℝ) ^ 3 /
          (2 * x * ((r + 1 : ℕ) : ℝ)) := hlarge
      _ = ((C + N : ℕ) : ℝ) ^ 3 / (2 * x) *
          (((r + 1 : ℕ) : ℝ))⁻¹ := by field_simp

/-- The concrete one-step reciprocal exponential-sum square estimate. -/
theorem reciprocalExpRange_sq_le_k1
    (x : ℝ) (C N q : ℕ)
    (hx : 0 < x) (hC : 0 < C) (hq : 1 ≤ q) (hqN : q ≤ N)
    (hderiv : 4 * x * (q : ℝ) ≤ (C : ℝ) ^ 3) :
    ‖reciprocalExpRange x C N‖ ^ 2 ≤
      2 * (N : ℝ) ^ 2 / (q : ℝ) +
        4 * (N : ℝ) * (((C + N : ℕ) : ℝ) ^ 3 / (2 * x)) /
          (q : ℝ) * finiteHarmonic q := by
  apply reciprocalExpRange_sq_le_of_terminal x C N q hq hqN
    (((C + N : ℕ) : ℝ) ^ 3 / (2 * x)) (by positivity)
  intro r hr
  exact terminalCorrelation_reciprocal_k1_le x C N q r hx hC hr hderiv

/-- Concrete one-step estimate for a short range inside an ambient block of
length `M`. -/
theorem reciprocalExpRange_sq_le_k1_ambient
    (x : ℝ) (C L M q : ℕ)
    (hx : 0 < x) (hC : 0 < C) (hM : 0 < M)
    (hq : 1 ≤ q) (hLM : L ≤ M) (hqM : q ≤ M)
    (hderiv : 4 * x * (q : ℝ) ≤ (C : ℝ) ^ 3) :
    ‖reciprocalExpRange x C L‖ ^ 2 ≤
      2 * (M : ℝ) ^ 2 / (q : ℝ) +
        4 * (M : ℝ) * (((C + L : ℕ) : ℝ) ^ 3 / (2 * x)) /
          (q : ℝ) * finiteHarmonic q := by
  apply reciprocalExpRange_sq_le_of_terminal_ambient x C L M q hM hq hLM hqM
    (((C + L : ℕ) : ℝ) ^ 3 / (2 * x)) (by positivity)
  intro r hr
  exact terminalCorrelation_reciprocal_k1_le x C L q r hx hC hr hderiv

/-! ## Selecting and eliminating the one-step shift -/

def reciprocalShiftAdmissibleK1 (x : ℝ) (C q : ℕ) : Prop :=
  4 * x * (q : ℝ) ≤ (C : ℝ) ^ 3

def reciprocalShiftK1 (x : ℝ) (C N : ℕ) : ℕ := by
  classical
  exact Nat.findGreatest (reciprocalShiftAdmissibleK1 x C) N

lemma reciprocalShiftK1_le (x : ℝ) (C N : ℕ) :
    reciprocalShiftK1 x C N ≤ N := by
  classical
  exact Nat.findGreatest_le _

lemma reciprocalShiftK1_admissible (x : ℝ) (C N : ℕ) :
    reciprocalShiftAdmissibleK1 x C (reciprocalShiftK1 x C N) := by
  classical
  unfold reciprocalShiftK1
  exact Nat.findGreatest_spec (P := reciprocalShiftAdmissibleK1 x C)
    (m := 0) (n := N) (Nat.zero_le _) (by simp [reciprocalShiftAdmissibleK1])

lemma reciprocalShiftK1_pos {x : ℝ} {C N : ℕ} (hN : 0 < N)
    (hone : 4 * x ≤ (C : ℝ) ^ 3) :
    0 < reciprocalShiftK1 x C N := by
  classical
  rw [reciprocalShiftK1, Nat.findGreatest_pos]
  refine ⟨1, by omega, hN, ?_⟩
  simpa [reciprocalShiftAdmissibleK1] using hone

lemma reciprocalShiftK1_succ_not_admissible {x : ℝ} {C N : ℕ}
    (hlt : reciprocalShiftK1 x C N < N) :
    ¬ reciprocalShiftAdmissibleK1 x C (reciprocalShiftK1 x C N + 1) := by
  classical
  exact Nat.findGreatest_is_greatest (P := reciprocalShiftAdmissibleK1 x C)
    (Nat.lt_succ_self _) (Nat.succ_le_iff.mpr hlt)

lemma reciprocalShiftK1_lt_of_middle {x : ℝ} {C N : ℕ}
    (hmiddle : (C : ℝ) ^ 3 < 4 * x * (N : ℝ)) :
    reciprocalShiftK1 x C N < N := by
  have hle := reciprocalShiftK1_le x C N
  by_contra hnot
  have heq : reciprocalShiftK1 x C N = N :=
    Nat.le_antisymm hle (Nat.le_of_not_gt hnot)
  have hadm := reciprocalShiftK1_admissible x C N
  rw [heq] at hadm
  exact (not_le_of_gt hmiddle) hadm

/-- The selected one-step shift is within a factor two of its real
threshold. -/
lemma reciprocalShiftK1_scale_bounds {x : ℝ} {C N : ℕ}
    (hx : 0 < x) (hN : 0 < N)
    (hone : 4 * x ≤ (C : ℝ) ^ 3)
    (hmiddle : (C : ℝ) ^ 3 < 4 * x * (N : ℝ)) :
    let q := reciprocalShiftK1 x C N
    1 ≤ q ∧ q ≤ N ∧
      4 * x * (q : ℝ) ≤ (C : ℝ) ^ 3 ∧
      (C : ℝ) ^ 3 < 8 * x * (q : ℝ) := by
  let q := reciprocalShiftK1 x C N
  have hq : 1 ≤ q := reciprocalShiftK1_pos hN hone
  have hlt : q < N := reciprocalShiftK1_lt_of_middle hmiddle
  have hfail := reciprocalShiftK1_succ_not_admissible hlt
  have hnext : (C : ℝ) ^ 3 < 4 * x * ((q + 1 : ℕ) : ℝ) :=
    lt_of_not_ge hfail
  have hqdoubleNat : q + 1 ≤ 2 * q := by omega
  have hqdouble : ((q + 1 : ℕ) : ℝ) ≤ 2 * (q : ℝ) := by
    exact_mod_cast hqdoubleNat
  refine ⟨hq, reciprocalShiftK1_le x C N,
    reciprocalShiftK1_admissible x C N, ?_⟩
  calc
    (C : ℝ) ^ 3 < 4 * x * ((q + 1 : ℕ) : ℝ) := hnext
    _ ≤ 4 * x * (2 * (q : ℝ)) := by gcongr
    _ = 8 * x * (q : ℝ) := by ring

/-- The q-free square estimate in the one-step middle-frequency branch. -/
theorem reciprocalExpRange_sq_le_dyadic_qfree_k1
    (x : ℝ) (C N : ℕ)
    (hx : 0 < x) (hC : 0 < C) (hN : 0 < N) (hNC : N ≤ C)
    (hone : 4 * x ≤ (C : ℝ) ^ 3)
    (hmiddle : (C : ℝ) ^ 3 < 4 * x * (N : ℝ)) :
    ‖reciprocalExpRange x C N‖ ^ 2 ≤
      528 * (N : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) *
        (1 + Real.log C) := by
  let q := reciprocalShiftK1 x C N
  obtain ⟨hq, hqN, hderiv, hscale⟩ :=
    reciprocalShiftK1_scale_bounds hx hN hone hmiddle
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hC3 : 0 < (C : ℝ) ^ 3 := by positivity
  have hqC : q ≤ C := hqN.trans hNC
  have hlogq : Real.log (q : ℝ) ≤ Real.log (C : ℝ) :=
    Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqC)
  have hlogC : 0 ≤ Real.log (C : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ C by omega))
  have hH := finiteHarmonic_le_one_add_log_k1 q
  have hinvq : 1 / (q : ℝ) ≤ 8 * x / (C : ℝ) ^ 3 := by
    rw [div_le_div_iff₀ hqpos hC3]
    nlinarith [hscale]
  have hinvN : 1 / (N : ℝ) ≤ 4 * x / (C : ℝ) ^ 3 := by
    have hNr : (0 : ℝ) < N := by exact_mod_cast hN
    rw [div_le_div_iff₀ hNr hC3]
    simpa only [one_mul] using hmiddle.le
  have hCN : ((C + N : ℕ) : ℝ) ≤ 2 * (C : ℝ) := by
    exact_mod_cast (show C + N ≤ 2 * C by omega)
  have hCNpow : ((C + N : ℕ) : ℝ) ^ 3 ≤ 8 * (C : ℝ) ^ 3 := by
    calc
      _ ≤ (2 * (C : ℝ)) ^ 3 := by gcongr
      _ = _ := by ring
  have hraw := reciprocalExpRange_sq_le_k1 x C N q hx hC hq hqN hderiv
  have hdiag :
      2 * (N : ℝ) ^ 2 / (q : ℝ) ≤
        16 * (N : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) := by
    calc
      2 * (N : ℝ) ^ 2 / (q : ℝ) =
          2 * (N : ℝ) ^ 2 * (1 / (q : ℝ)) := by ring
      _ ≤ 2 * (N : ℝ) ^ 2 * (8 * x / (C : ℝ) ^ 3) := by
        gcongr
      _ = 16 * (N : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) := by ring
  have hKq :
      (((C + N : ℕ) : ℝ) ^ 3 / (2 * x)) / (q : ℝ) ≤ 32 := by
    rw [div_le_iff₀ hqpos, div_le_iff₀ (by positivity : 0 < 2 * x)]
    nlinarith [hCNpow, hscale]
  have hterminal :
      4 * (N : ℝ) * (((C + N : ℕ) : ℝ) ^ 3 / (2 * x)) /
          (q : ℝ) * finiteHarmonic q ≤
        512 * (N : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) *
          (1 + Real.log C) := by
    have hlog : 0 ≤ 1 + Real.log (C : ℝ) := by positivity
    have hHnonneg := finiteHarmonic_nonneg q
    have hNfactor :
        (N : ℝ) ≤ 4 * (N : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) := by
      have hNr : (0 : ℝ) < N := by exact_mod_cast hN
      have hm := mul_le_mul_of_nonneg_left hinvN (show 0 ≤ (N : ℝ) ^ 2 by positivity)
      field_simp at hm ⊢
      nlinarith
    calc
      4 * (N : ℝ) * (((C + N : ℕ) : ℝ) ^ 3 / (2 * x)) /
            (q : ℝ) * finiteHarmonic q ≤
          128 * (N : ℝ) * finiteHarmonic q := by
        calc
          _ = 4 * (N : ℝ) *
              ((((C + N : ℕ) : ℝ) ^ 3 / (2 * x)) / (q : ℝ)) *
                finiteHarmonic q := by ring
          _ ≤ 4 * (N : ℝ) * 32 * finiteHarmonic q := by gcongr
          _ = _ := by ring
      _ ≤ 128 * (N : ℝ) * (1 + Real.log C) := by
        have hadd : 1 + Real.log (q : ℝ) ≤ 1 + Real.log (C : ℝ) := by
          linarith
        have := hH.trans hadd
        gcongr
      _ ≤ 512 * (N : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) *
          (1 + Real.log C) := by
        calc
          _ ≤ 128 * (4 * (N : ℝ) ^ 2 * (x / (C : ℝ) ^ 3)) *
              (1 + Real.log C) := by gcongr
          _ = _ := by ring
  calc
    ‖reciprocalExpRange x C N‖ ^ 2 ≤
        2 * (N : ℝ) ^ 2 / (q : ℝ) +
          4 * (N : ℝ) * (((C + N : ℕ) : ℝ) ^ 3 / (2 * x)) /
            (q : ℝ) * finiteHarmonic q := hraw
    _ ≤ 16 * (N : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) +
        512 * (N : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) *
          (1 + Real.log C) := add_le_add hdiag hterminal
    _ ≤ 528 * (N : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) *
        (1 + Real.log C) := by
      have : 1 ≤ 1 + Real.log (C : ℝ) := by linarith
      have hbase : 0 ≤ (N : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) := by positivity
      nlinarith

/-- Ambient q-free square estimate.  The summation length `L` may be any
prefix of the ambient dyadic length `M`. -/
theorem reciprocalExpRange_sq_le_dyadic_qfree_k1_ambient
    (x : ℝ) (C L M : ℕ)
    (hx : 0 < x) (hC : 0 < C) (hM : 0 < M)
    (hLM : L ≤ M) (hMC : M ≤ C)
    (hone : 4 * x ≤ (C : ℝ) ^ 3)
    (hmiddle : (C : ℝ) ^ 3 < 4 * x * (M : ℝ)) :
    ‖reciprocalExpRange x C L‖ ^ 2 ≤
      528 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) *
        (1 + Real.log C) := by
  let q := reciprocalShiftK1 x C M
  obtain ⟨hq, hqM, hderiv, hscale⟩ :=
    reciprocalShiftK1_scale_bounds hx hM hone hmiddle
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hC3 : 0 < (C : ℝ) ^ 3 := by positivity
  have hqC : q ≤ C := hqM.trans hMC
  have hlogq : Real.log (q : ℝ) ≤ Real.log (C : ℝ) :=
    Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast hqC)
  have hlogC : 0 ≤ Real.log (C : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ C by omega))
  have hH := finiteHarmonic_le_one_add_log_k1 q
  have hinvq : 1 / (q : ℝ) ≤ 8 * x / (C : ℝ) ^ 3 := by
    rw [div_le_div_iff₀ hqpos hC3]
    nlinarith [hscale]
  have hinvM : 1 / (M : ℝ) ≤ 4 * x / (C : ℝ) ^ 3 := by
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    rw [div_le_div_iff₀ hMr hC3]
    simpa only [one_mul] using hmiddle.le
  have hLC : L ≤ C := hLM.trans hMC
  have hCL : ((C + L : ℕ) : ℝ) ≤ 2 * (C : ℝ) := by
    exact_mod_cast (show C + L ≤ 2 * C by omega)
  have hCLpow : ((C + L : ℕ) : ℝ) ^ 3 ≤ 8 * (C : ℝ) ^ 3 := by
    calc
      _ ≤ (2 * (C : ℝ)) ^ 3 := by gcongr
      _ = _ := by ring
  have hraw := reciprocalExpRange_sq_le_k1_ambient
    x C L M q hx hC hM hq hLM hqM hderiv
  have hdiag :
      2 * (M : ℝ) ^ 2 / (q : ℝ) ≤
        16 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) := by
    calc
      2 * (M : ℝ) ^ 2 / (q : ℝ) =
          2 * (M : ℝ) ^ 2 * (1 / (q : ℝ)) := by ring
      _ ≤ 2 * (M : ℝ) ^ 2 * (8 * x / (C : ℝ) ^ 3) := by gcongr
      _ = 16 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) := by ring
  have hKq :
      (((C + L : ℕ) : ℝ) ^ 3 / (2 * x)) / (q : ℝ) ≤ 32 := by
    rw [div_le_iff₀ hqpos, div_le_iff₀ (by positivity : 0 < 2 * x)]
    nlinarith [hCLpow, hscale]
  have hMfactor :
      (M : ℝ) ≤ 4 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) := by
    have hMr : (0 : ℝ) < M := by exact_mod_cast hM
    have hm := mul_le_mul_of_nonneg_left hinvM (show 0 ≤ (M : ℝ) ^ 2 by positivity)
    field_simp at hm ⊢
    nlinarith
  have hterminal :
      4 * (M : ℝ) * (((C + L : ℕ) : ℝ) ^ 3 / (2 * x)) /
          (q : ℝ) * finiteHarmonic q ≤
        512 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) *
          (1 + Real.log C) := by
    have hlog : 0 ≤ 1 + Real.log (C : ℝ) := by positivity
    have hHnonneg := finiteHarmonic_nonneg q
    calc
      4 * (M : ℝ) * (((C + L : ℕ) : ℝ) ^ 3 / (2 * x)) /
            (q : ℝ) * finiteHarmonic q ≤
          128 * (M : ℝ) * finiteHarmonic q := by
        calc
          _ = 4 * (M : ℝ) *
              ((((C + L : ℕ) : ℝ) ^ 3 / (2 * x)) / (q : ℝ)) *
                finiteHarmonic q := by ring
          _ ≤ 4 * (M : ℝ) * 32 * finiteHarmonic q := by gcongr
          _ = _ := by ring
      _ ≤ 128 * (M : ℝ) * (1 + Real.log C) := by
        have hadd : 1 + Real.log (q : ℝ) ≤ 1 + Real.log (C : ℝ) := by
          linarith
        have := hH.trans hadd
        gcongr
      _ ≤ 512 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) *
          (1 + Real.log C) := by
        calc
          _ ≤ 128 * (4 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3)) *
              (1 + Real.log C) := by gcongr
          _ = _ := by ring
  calc
    ‖reciprocalExpRange x C L‖ ^ 2 ≤
        2 * (M : ℝ) ^ 2 / (q : ℝ) +
          4 * (M : ℝ) * (((C + L : ℕ) : ℝ) ^ 3 / (2 * x)) /
            (q : ℝ) * finiteHarmonic q := hraw
    _ ≤ 16 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) +
        512 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) *
          (1 + Real.log C) := add_le_add hdiag hterminal
    _ ≤ 528 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) *
        (1 + Real.log C) := by
      have : 1 ≤ 1 + Real.log (C : ℝ) := by linarith
      have hbase : 0 ≤ (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) := by positivity
      nlinarith

/-- Norm form of the ambient one-step estimate. -/
theorem norm_reciprocalExpRange_le_dyadic_qfree_k1_ambient
    (x : ℝ) (C L M : ℕ)
    (hx : 0 < x) (hC : 0 < C) (hM : 0 < M)
    (hLM : L ≤ M) (hMC : M ≤ C)
    (hone : 4 * x ≤ (C : ℝ) ^ 3)
    (hmiddle : (C : ℝ) ^ 3 < 4 * x * (M : ℝ)) :
    ‖reciprocalExpRange x C L‖ ≤
      24 * (M : ℝ) * Real.sqrt (x / (C : ℝ) ^ 3) *
        Real.sqrt (1 + Real.log C) := by
  have hdelta : 0 ≤ x / (C : ℝ) ^ 3 := by positivity
  have hlogC : 0 ≤ Real.log (C : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ C by omega))
  have hLlog : 0 ≤ 1 + Real.log (C : ℝ) := by positivity
  apply le_of_pow_le_pow_left₀ (n := 2) (by norm_num) (by positivity)
  calc
    ‖reciprocalExpRange x C L‖ ^ 2 ≤
        528 * (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) *
          (1 + Real.log C) :=
      reciprocalExpRange_sq_le_dyadic_qfree_k1_ambient
        x C L M hx hC hM hLM hMC hone hmiddle
    _ ≤ (24 * (M : ℝ) * Real.sqrt (x / (C : ℝ) ^ 3) *
          Real.sqrt (1 + Real.log C)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hdelta, Real.sq_sqrt hLlog]
      have hprod : 0 ≤ (M : ℝ) ^ 2 * (x / (C : ℝ) ^ 3) *
          (1 + Real.log (C : ℝ)) := by positivity
      norm_num
      nlinarith

/-- Natural-Ioc middle-frequency estimate.  The ambient length is the left
endpoint scale `A+1`, so the result is uniform over all prefixes of the
dyadic interval. -/
theorem norm_reciprocalExpSum_le_dyadic_qfree_k1
    (x : ℝ) (A B : ℕ) (hx : 0 < x) (hAB : A ≤ B)
    (hdyadic : B - A ≤ A + 1)
    (hone : 4 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 3)
    (hmiddle : ((A + 1 : ℕ) : ℝ) ^ 3 <
      4 * x * ((A + 1 : ℕ) : ℝ)) :
    ‖reciprocalExpSum x A B‖ ≤
      24 * ((A + 1 : ℕ) : ℝ) *
        Real.sqrt (x / ((A + 1 : ℕ) : ℝ) ^ 3) *
        Real.sqrt (1 + Real.log ((A + 1 : ℕ) : ℝ)) := by
  rw [reciprocalExpSum_eq_range x A B hAB]
  exact norm_reciprocalExpRange_le_dyadic_qfree_k1_ambient
    x (A + 1) (B - A) (A + 1) hx (by omega) (by omega)
    hdyadic (by rfl) hone hmiddle

/-- Paper-shaped logarithmic version of the natural-Ioc one-step bound. -/
theorem norm_reciprocalExpSum_le_dyadic_qfree_k1_log
    (x : ℝ) (A B : ℕ) (hx : 0 < x) (hAB : A ≤ B)
    (hdyadic : B - A ≤ A + 1)
    (hone : 4 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 3)
    (hmiddle : ((A + 1 : ℕ) : ℝ) ^ 3 <
      4 * x * ((A + 1 : ℕ) : ℝ))
    (hlog : 1 ≤ Real.log ((A + 1 : ℕ) : ℝ)) :
    ‖reciprocalExpSum x A B‖ ≤
      48 * ((A + 1 : ℕ) : ℝ) *
        Real.sqrt (x / ((A + 1 : ℕ) : ℝ) ^ 3) *
        Real.sqrt (Real.log ((A + 1 : ℕ) : ℝ)) := by
  have hbase := norm_reciprocalExpSum_le_dyadic_qfree_k1
    x A B hx hAB hdyadic hone hmiddle
  have hsqrt :
      Real.sqrt (1 + Real.log ((A + 1 : ℕ) : ℝ)) ≤
        2 * Real.sqrt (Real.log ((A + 1 : ℕ) : ℝ)) := by
    have hlog0 : 0 ≤ Real.log ((A + 1 : ℕ) : ℝ) := hlog.trans' (by norm_num)
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · rw [mul_pow, Real.sq_sqrt hlog0]
      nlinarith
  calc
    ‖reciprocalExpSum x A B‖ ≤
        24 * ((A + 1 : ℕ) : ℝ) *
          Real.sqrt (x / ((A + 1 : ℕ) : ℝ) ^ 3) *
          Real.sqrt (1 + Real.log ((A + 1 : ℕ) : ℝ)) := hbase
    _ ≤ 24 * ((A + 1 : ℕ) : ℝ) *
          Real.sqrt (x / ((A + 1 : ℕ) : ℝ) ^ 3) *
          (2 * Real.sqrt (Real.log ((A + 1 : ℕ) : ℝ))) := by gcongr
    _ = _ := by ring

/-- An unconditional natural-Ioc envelope combining the direct,
one-difference, and two-difference branch expressions.  The proof uses the
direct branch at low frequency, the one-step theorem in its admissible
middle range, and the trivial estimate once the one-step upper constraint
fails.  The nonnegative `k = 2` term is retained explicitly for downstream
branchwise estimates. -/
theorem norm_reciprocalExpSum_le_three_branch
    (x : ℝ) (A B : ℕ) (hx : 0 < x) (hAB : A ≤ B)
    (hdyadic : B - A ≤ A + 1)
    (_hglobal : 12 * x ≤ ((A + 1 : ℕ) : ℝ) ^ 4) :
    ‖reciprocalExpSum x A B‖ ≤
      ((B + 1 : ℕ) : ℝ) ^ 2 / x +
      24 * ((A + 1 : ℕ) : ℝ) *
        Real.sqrt (x / ((A + 1 : ℕ) : ℝ) ^ 3) *
        Real.sqrt (1 + Real.log ((A + 1 : ℕ) : ℝ)) +
      256 * ((B - A : ℕ) : ℝ) *
        (x / ((A + 1 : ℕ) : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
        Real.sqrt (Real.log ((A + 1 : ℕ) : ℝ)) := by
  let C : ℕ := A + 1
  have hC : 0 < C := by omega
  have hlogC : 0 ≤ Real.log (C : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ C by omega))
  have hnonnegDirect : 0 ≤ ((B + 1 : ℕ) : ℝ) ^ 2 / x := by positivity
  have hnonnegK1 : 0 ≤
      24 * (C : ℝ) * Real.sqrt (x / (C : ℝ) ^ 3) *
        Real.sqrt (1 + Real.log (C : ℝ)) := by positivity
  have hnonnegK2 : 0 ≤
      256 * ((B - A : ℕ) : ℝ) *
        (x / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
        Real.sqrt (Real.log (C : ℝ)) := by positivity
  by_cases hdirect : x / (C : ℝ) ^ 2 ≤ 1 / 2
  · have hd := norm_reciprocalExpSum_le_firstDerivative x A B hx hAB (by
      simpa only [C] using hdirect)
    calc
      ‖reciprocalExpSum x A B‖ ≤ ((B + 1 : ℕ) : ℝ) ^ 2 / x := hd
      _ ≤ ((B + 1 : ℕ) : ℝ) ^ 2 / x +
          24 * (C : ℝ) * Real.sqrt (x / (C : ℝ) ^ 3) *
            Real.sqrt (1 + Real.log (C : ℝ)) +
          256 * ((B - A : ℕ) : ℝ) *
            (x / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
            Real.sqrt (Real.log (C : ℝ)) := by
        nlinarith [hnonnegK1, hnonnegK2]
      _ = _ := by rfl
  · have hC2 : (C : ℝ) ^ 2 < 2 * x := by
      have hC2pos : 0 < (C : ℝ) ^ 2 := by positivity
      have hlt : 1 / 2 < x / (C : ℝ) ^ 2 := lt_of_not_ge hdirect
      rw [lt_div_iff₀ hC2pos] at hlt
      nlinarith
    have hmiddle : (C : ℝ) ^ 3 < 4 * x * (C : ℝ) := by
      have hCr : 0 < (C : ℝ) := by positivity
      have hm := mul_lt_mul_of_pos_right hC2 hCr
      nlinarith
    by_cases hone : 4 * x ≤ (C : ℝ) ^ 3
    · have hk1 := norm_reciprocalExpSum_le_dyadic_qfree_k1
        x A B hx hAB hdyadic (by simpa only [C] using hone)
          (by simpa only [C] using hmiddle)
      calc
        ‖reciprocalExpSum x A B‖ ≤
            24 * (C : ℝ) * Real.sqrt (x / (C : ℝ) ^ 3) *
              Real.sqrt (1 + Real.log (C : ℝ)) := by simpa only [C] using hk1
        _ ≤ ((B + 1 : ℕ) : ℝ) ^ 2 / x +
            24 * (C : ℝ) * Real.sqrt (x / (C : ℝ) ^ 3) *
              Real.sqrt (1 + Real.log (C : ℝ)) +
            256 * ((B - A : ℕ) : ℝ) *
              (x / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
              Real.sqrt (Real.log (C : ℝ)) := by
          nlinarith [hnonnegDirect, hnonnegK2]
        _ = _ := by rfl

    · have hratio : (1 / 4 : ℝ) ≤ x / (C : ℝ) ^ 3 := by
        have hC3pos : 0 < (C : ℝ) ^ 3 := by positivity
        rw [le_div_iff₀ hC3pos]
        nlinarith [lt_of_not_ge hone]
      have hsqrtRatio : (1 / 2 : ℝ) ≤ Real.sqrt (x / (C : ℝ) ^ 3) := by
        rw [Real.le_sqrt' (by norm_num : (0 : ℝ) < 1 / 2)]
        norm_num
        exact hratio
      have hsqrtLog : 1 ≤ Real.sqrt (1 + Real.log (C : ℝ)) := by
        rw [Real.le_sqrt' zero_lt_one, one_pow]
        linarith
      have htriv := norm_reciprocalExpSum_le x A B
      have hCbound : ((B - A : ℕ) : ℝ) ≤ (C : ℝ) := by
        exact_mod_cast hdyadic
      have hK1large : (C : ℝ) ≤
          24 * (C : ℝ) * Real.sqrt (x / (C : ℝ) ^ 3) *
            Real.sqrt (1 + Real.log (C : ℝ)) := by
        calc
          (C : ℝ) ≤ 24 * (C : ℝ) * (1 / 2 : ℝ) * 1 := by
            have hCr : 0 ≤ (C : ℝ) := by positivity
            nlinarith
          _ ≤ 24 * (C : ℝ) * Real.sqrt (x / (C : ℝ) ^ 3) *
              Real.sqrt (1 + Real.log (C : ℝ)) := by gcongr
      calc
        ‖reciprocalExpSum x A B‖ ≤ ((B - A : ℕ) : ℝ) := htriv
        _ ≤ (C : ℝ) := hCbound
        _ ≤ 24 * (C : ℝ) * Real.sqrt (x / (C : ℝ) ^ 3) *
            Real.sqrt (1 + Real.log (C : ℝ)) := hK1large
        _ ≤ ((B + 1 : ℕ) : ℝ) ^ 2 / x +
            24 * (C : ℝ) * Real.sqrt (x / (C : ℝ) ^ 3) *
              Real.sqrt (1 + Real.log (C : ℝ)) +
            256 * ((B - A : ℕ) : ℝ) *
              (x / (C : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
              Real.sqrt (Real.log (C : ℝ)) := by
          nlinarith [hnonnegDirect, hnonnegK2]
        _ = _ := by rfl

/-- Sign-symmetric form of the unconditional three-branch envelope. -/
theorem norm_reciprocalExpSum_le_three_branch_abs
    (t : ℝ) (A B : ℕ) (ht : t ≠ 0) (hAB : A ≤ B)
    (hdyadic : B - A ≤ A + 1)
    (hglobal : 12 * |t| ≤ ((A + 1 : ℕ) : ℝ) ^ 4) :
    ‖reciprocalExpSum t A B‖ ≤
      ((B + 1 : ℕ) : ℝ) ^ 2 / |t| +
      24 * ((A + 1 : ℕ) : ℝ) *
        Real.sqrt (|t| / ((A + 1 : ℕ) : ℝ) ^ 3) *
        Real.sqrt (1 + Real.log ((A + 1 : ℕ) : ℝ)) +
      256 * ((B - A : ℕ) : ℝ) *
        (|t| / ((A + 1 : ℕ) : ℝ) ^ 4) ^ (1 / 6 : ℝ) *
        Real.sqrt (Real.log ((A + 1 : ℕ) : ℝ)) := by
  by_cases htpos : 0 < t
  · simpa only [abs_of_pos htpos] using
      norm_reciprocalExpSum_le_three_branch t A B htpos hAB hdyadic
        (by simpa only [abs_of_pos htpos] using hglobal)
  · have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt htpos) ht
    have hy : 0 < -t := neg_pos.mpr htneg
    have hbase := norm_reciprocalExpSum_le_three_branch (-t) A B hy hAB hdyadic
      (by simpa only [abs_of_neg htneg] using hglobal)
    rw [← norm_reciprocalExpSum_neg (-t) A B] at hbase
    simpa only [neg_neg, abs_of_neg htneg] using hbase

end

end Erdos175
