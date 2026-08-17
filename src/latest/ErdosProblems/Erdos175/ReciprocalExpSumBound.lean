/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos175.ReciprocalExpSum
import ErdosProblems.Erdos175.VanDerCorputTwoStep
import ErdosProblems.Erdos175.KusminLandau

/-!
# The two-step reciprocal exponential-sum bound

This file combines the normalized two-step van der Corput inequality with
the Kusmin--Landau estimate for the twice-differenced reciprocal phase.
-/

namespace Erdos175

open scoped BigOperators

noncomputable section

/-- The finite harmonic factor produced by one family of Weyl shifts. -/
def finiteHarmonic (H : ℕ) : ℝ :=
  ∑ r ∈ Finset.range H, ((r + 1 : ℕ) : ℝ)⁻¹

lemma finiteHarmonic_nonneg (H : ℕ) : 0 ≤ finiteHarmonic H := by
  unfold finiteHarmonic
  positivity

lemma sum_double_inv_eq_finiteHarmonic_mul (H₁ H₂ : ℕ) :
    (∑ r₁ ∈ Finset.range H₁, ∑ r₂ ∈ Finset.range H₂,
        (((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ))⁻¹) =
      finiteHarmonic H₁ * finiteHarmonic H₂ := by
  simp only [mul_inv]
  rw [finiteHarmonic, finiteHarmonic, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r₁ _hr₁
  rw [Finset.mul_sum]

/-- Combine the normalized two-step Weyl inequality with a reciprocal
`1/(r₁r₂)` estimate for every terminal correlation. -/
theorem reciprocalExpRange_fourth_le_of_terminal
    (x : ℝ) (C N q : ℕ) (hq : 1 ≤ q) (hqN : q ^ 2 ≤ N)
    (K : ℝ) (hK : 0 ≤ K)
    (hterminal : ∀ r₁ < q ^ 2, ∀ r₂ < q,
      ‖∑ n ∈ Finset.range (N - (r₂ + 1) - (r₁ + 1)),
        positiveCorrelation₂
          (fun j ↦ e (reciprocalPhase x (C + j))) r₁ r₂ n‖ ≤
        K * (((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ))⁻¹) :
    ‖reciprocalExpRange x C N‖ ^ 4 ≤
      512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 +
        (512 : ℝ) * (N : ℝ) ^ 3 * K / (q : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) := by
  have hqpos : 0 < q := by omega
  have hNpos : 0 < N := (pow_pos hqpos 2).trans_le hqN
  let z : ℕ → ℂ := fun j ↦ e (reciprocalPhase x (C + j))
  have hz : ∀ n < N, ‖z n‖ ≤ 1 := by
    intro n hn
    simp [z]
  have hweyl := VanDerCorput.gr_lemma_8_3_k2 z N q hq hqN hz
  have hsum :
      (∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
        ‖∑ n ∈ Finset.range (N - (r₂ + 1) - (r₁ + 1)),
          positiveCorrelation₂ z r₁ r₂ n‖ / (N : ℝ)) ≤
        K / (N : ℝ) *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) := by
    calc
      _ ≤ ∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
          (K * (((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ))⁻¹) /
            (N : ℝ) := by
        apply Finset.sum_le_sum
        intro r₁ hr₁
        apply Finset.sum_le_sum
        intro r₂ hr₂
        exact div_le_div_of_nonneg_right
          (hterminal r₁ (Finset.mem_range.mp hr₁) r₂
            (Finset.mem_range.mp hr₂)) (by positivity)
      _ = K / (N : ℝ) *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) := by
        calc
          _ = K / (N : ℝ) *
              (∑ r₁ ∈ Finset.range (q ^ 2), ∑ r₂ ∈ Finset.range q,
                (((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ))⁻¹) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r₁ _hr₁
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro r₂ _hr₂
            ring
          _ = _ := by rw [sum_double_inv_eq_finiteHarmonic_mul]
  have hnormalized :
      (‖reciprocalExpRange x C N‖ / (8 * (N : ℝ))) ^ 4 ≤
        1 / (8 * (q : ℝ) ^ 2) +
          1 / (8 * (q : ℝ) ^ 3) *
            (K / (N : ℝ) *
              (finiteHarmonic (q ^ 2) * finiteHarmonic q)) := by
    rw [reciprocalExpRange]
    have hcoef : 0 ≤ 1 / (8 * (q : ℝ) ^ 3) := by positivity
    have hweighted := mul_le_mul_of_nonneg_left hsum hcoef
    exact hweyl.trans (add_le_add_right hweighted _)
  have hscale : 0 < (8 * (N : ℝ)) ^ 4 := by positivity
  have hmul := mul_le_mul_of_nonneg_right hnormalized hscale.le
  calc
    ‖reciprocalExpRange x C N‖ ^ 4 =
        (‖reciprocalExpRange x C N‖ / (8 * (N : ℝ))) ^ 4 *
          (8 * (N : ℝ)) ^ 4 := by
      field_simp
    _ ≤ (1 / (8 * (q : ℝ) ^ 2) +
          1 / (8 * (q : ℝ) ^ 3) *
            (K / (N : ℝ) *
              (finiteHarmonic (q ^ 2) * finiteHarmonic q))) *
          (8 * (N : ℝ)) ^ 4 := hmul
    _ = 512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 +
        (512 : ℝ) * (N : ℝ) ^ 3 * K / (q : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) := by
      field_simp
      ring

/-! ## The concrete twice-difference terminal phase -/

/-- The second multiplicative correlation is exactly the mixed forward
difference used by the Kusmin--Landau estimate. -/
lemma positiveCorrelation₂_reciprocal_eq_expPhase_twiceDiff
    (x : ℝ) (C h₁ h₂ n : ℕ) :
    positiveCorrelation₂
        (fun j ↦ e (reciprocalPhase x (C + j))) h₁ h₂ n =
      expPhase
        (twiceDiffReciprocal x (h₁ + 1 : ℕ) (h₂ + 1 : ℕ) (C + n : ℕ)) := by
  rw [expPhase_eq_e, positiveCorrelation₂_e]
  congr 1
  rw [positivePhaseDifference₂_apply]
  simp only [twiceDiffReciprocal, twiceDiff, reciprocalPhase]
  push_cast
  ring

/-- Negating every real phase conjugates the complex sum and therefore
does not change its norm. -/
lemma norm_sum_expPhase_neg_eq (f : ℕ → ℝ) (L : ℕ) :
    ‖∑ n ∈ Finset.range L, expPhase (-f n)‖ =
      ‖∑ n ∈ Finset.range L, expPhase (f n)‖ := by
  rw [← Complex.norm_conj]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro n _hn
  rw [expPhase_eq_e, expPhase_eq_e, conj_e]
  simp

/-- The first-derivative branch of the reciprocal exponential-sum bound,
wrapped so that it applies to a range of any natural length. -/
theorem norm_reciprocalExpRange_le_firstDerivative
    (x : ℝ) (C N : ℕ) (hx : 0 < x) (hC : 0 < C)
    (hhalf : x / (C : ℝ) ^ 2 ≤ 1 / 2) :
    ‖reciprocalExpRange x C N‖ ≤ ((C + N : ℕ) : ℝ) ^ 2 / x := by
  have hlarge : 2 ≤ ((C + N : ℕ) : ℝ) ^ 2 / x := by
    apply (le_div_iff₀ hx).2
    have hCpow : 0 < (C : ℝ) ^ 2 := by positivity
    have hbase : 2 * x ≤ (C : ℝ) ^ 2 := by
      have := (div_le_iff₀ hCpow).1 hhalf
      nlinarith
    have hCN : (C : ℝ) ≤ ((C + N : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_add_right C N)
    have hpow : (C : ℝ) ^ 2 ≤ ((C + N : ℕ) : ℝ) ^ 2 := by
      gcongr
    linarith
  by_cases hN : 2 ≤ N
  · have hlength : N - 2 + 2 = N := by omega
    have hendNat : C + (N - 2 + 1) ≤ C + N := by omega
    have hend :
        (C : ℝ) + ((N - 2 + 1 : ℕ) : ℝ) ≤ ((C + N : ℕ) : ℝ) := by
      exact_mod_cast hendNat
    have hKL := kusminLandau_reciprocalPhase x (C : ℝ)
      ((C + N : ℕ) : ℝ) (N - 2) hx (by positivity) hend hhalf
    rw [reciprocalExpRange]
    simpa only [hlength, expPhase_eq_e, reciprocalPhase, Nat.cast_add] using hKL
  · have hNtwo : N ≤ 1 := by omega
    calc
      ‖reciprocalExpRange x C N‖ ≤ (N : ℝ) := norm_reciprocalExpRange_le x C N
      _ ≤ 2 := by exact_mod_cast (show N ≤ 2 by omega)
      _ ≤ _ := hlarge

/-- Every terminal correlation in the two-step Weyl process satisfies the
concrete Kusmin--Landau bound.  The short ranges of length zero or one are
included: in that case the derivative-size hypothesis makes the displayed
right-hand side at least two. -/
lemma terminalCorrelation_reciprocal_le
    (x : ℝ) (C N q r₁ r₂ : ℕ)
    (hx : 0 < x) (hC : 0 < C)
    (hr₁ : r₁ < q ^ 2) (hr₂ : r₂ < q)
    (hderiv : 12 * x * (q : ℝ) ^ 3 ≤ (C : ℝ) ^ 4) :
    ‖∑ n ∈ Finset.range (N - (r₂ + 1) - (r₁ + 1)),
        positiveCorrelation₂
          (fun j ↦ e (reciprocalPhase x (C + j))) r₁ r₂ n‖ ≤
      ((C + N : ℕ) : ℝ) ^ 4 / (6 * x) *
        (((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ))⁻¹ := by
  let L : ℕ := N - (r₂ + 1) - (r₁ + 1)
  have hr₁q : r₁ + 1 ≤ q ^ 2 := by omega
  have hr₂q : r₂ + 1 ≤ q := by omega
  have hrsNat : (r₁ + 1) * (r₂ + 1) ≤ q ^ 3 := by
    calc
      (r₁ + 1) * (r₂ + 1) ≤ q ^ 2 * q :=
        Nat.mul_le_mul hr₁q hr₂q
      _ = q ^ 3 := by ring
  have hrs :
      ((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ) ≤
        (q : ℝ) ^ 3 := by
    exact_mod_cast hrsNat
  have hrsPos :
      0 < ((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ) := by
    positivity
  have hsmall :
      6 * x * ((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ) /
          (C : ℝ) ^ 4 ≤ 1 / 2 := by
    have hCpow : 0 < (C : ℝ) ^ 4 := by positivity
    apply (div_le_iff₀ hCpow).2
    have hxq :
        12 * x *
            (((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ)) ≤
          12 * x * (q : ℝ) ^ 3 := by
      gcongr
    nlinarith
  have hlarge :
      2 ≤ ((C + N : ℕ) : ℝ) ^ 4 /
        (6 * x * ((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ)) := by
    have hden :
        0 < 6 * x * ((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ) := by
      positivity
    apply (le_div_iff₀ hden).2
    have hCN : (C : ℝ) ≤ ((C + N : ℕ) : ℝ) := by
      exact_mod_cast (Nat.le_add_right C N)
    have hpow : (C : ℝ) ^ 4 ≤ ((C + N : ℕ) : ℝ) ^ 4 := by
      gcongr
    have hxrs :
        12 * x *
            (((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ)) ≤
          (C : ℝ) ^ 4 := by
      calc
        _ ≤ 12 * x * (q : ℝ) ^ 3 := by gcongr
        _ ≤ _ := hderiv
    nlinarith
  by_cases hL : 2 ≤ L
  · have hlength : L - 2 + 2 = L := by omega
    have hendNat :
        C + (L - 2 + 1) + (r₁ + 1) + (r₂ + 1) ≤ C + N := by
      dsimp [L]
      omega
    have hend :
        (C : ℝ) + ((L - 2 + 1 : ℕ) : ℝ) +
              ((r₁ + 1 : ℕ) : ℝ) + ((r₂ + 1 : ℕ) : ℝ) ≤
            ((C + N : ℕ) : ℝ) := by
      exact_mod_cast hendNat
    have hKL := kusminLandau_twiceDiffReciprocal
      x ((r₁ + 1 : ℕ) : ℝ) ((r₂ + 1 : ℕ) : ℝ)
      (C : ℝ) ((C + N : ℕ) : ℝ) (L - 2)
      hx (by positivity) (by positivity) (by positivity) hend hsmall
    calc
      ‖∑ n ∈ Finset.range (N - (r₂ + 1) - (r₁ + 1)),
          positiveCorrelation₂
            (fun j ↦ e (reciprocalPhase x (C + j))) r₁ r₂ n‖ =
          ‖∑ n ∈ Finset.range L,
            expPhase (twiceDiffReciprocal x (r₁ + 1 : ℕ) (r₂ + 1 : ℕ)
              (C + n : ℕ))‖ := by
        dsimp [L]
        congr 1
        apply Finset.sum_congr rfl
        intro n _hn
        exact positiveCorrelation₂_reciprocal_eq_expPhase_twiceDiff x C r₁ r₂ n
      _ = ‖∑ n ∈ Finset.range L,
            expPhase (-twiceDiffReciprocal x (r₁ + 1 : ℕ) (r₂ + 1 : ℕ)
              (C + n : ℕ))‖ := by
        symm
        exact norm_sum_expPhase_neg_eq
          (fun n ↦ twiceDiffReciprocal x (r₁ + 1 : ℕ) (r₂ + 1 : ℕ)
            (C + n : ℕ)) L
      _ ≤ ((C + N : ℕ) : ℝ) ^ 4 /
          (6 * x * ((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ)) := by
        rw [← hlength]
        simpa only [Nat.cast_add] using hKL
      _ = ((C + N : ℕ) : ℝ) ^ 4 / (6 * x) *
          (((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ))⁻¹ := by
        field_simp

  · have hLtwo : L ≤ 1 := by omega
    calc
      ‖∑ n ∈ Finset.range (N - (r₂ + 1) - (r₁ + 1)),
          positiveCorrelation₂
            (fun j ↦ e (reciprocalPhase x (C + j))) r₁ r₂ n‖ ≤
          ∑ n ∈ Finset.range L,
            ‖positiveCorrelation₂
              (fun j ↦ e (reciprocalPhase x (C + j))) r₁ r₂ n‖ := by
        dsimp [L]
        exact norm_sum_le _ _
      _ = (L : ℝ) := by
        simp [positiveCorrelation₂, positiveCorrelation]
      _ ≤ 2 := by exact_mod_cast (show L ≤ 2 by omega)
      _ ≤ ((C + N : ℕ) : ℝ) ^ 4 /
          (6 * x * ((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ)) := hlarge
      _ = ((C + N : ℕ) : ℝ) ^ 4 / (6 * x) *
          (((r₁ + 1 : ℕ) : ℝ) * ((r₂ + 1 : ℕ) : ℝ))⁻¹ := by
        field_simp

/-- The concrete `k = 2` reciprocal exponential-sum estimate obtained from
two Weyl differencing steps and Kusmin--Landau.  This is the fourth-power
form of Granville--Ramaré's Proposition 8 estimate, retaining the exact two
finite harmonic factors generated by the positive shifts. -/
theorem reciprocalExpRange_fourth_le
    (x : ℝ) (C N q : ℕ)
    (hx : 0 < x) (hC : 0 < C) (hq : 1 ≤ q) (hqN : q ^ 2 ≤ N)
    (hderiv : 12 * x * (q : ℝ) ^ 3 ≤ (C : ℝ) ^ 4) :
    ‖reciprocalExpRange x C N‖ ^ 4 ≤
      512 * (N : ℝ) ^ 4 / (q : ℝ) ^ 2 +
        (512 : ℝ) * (N : ℝ) ^ 3 *
            (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) / (q : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) := by
  apply reciprocalExpRange_fourth_le_of_terminal x C N q hq hqN
    (((C + N : ℕ) : ℝ) ^ 4 / (6 * x)) (by positivity)
  intro r₁ hr₁ r₂ hr₂
  exact terminalCorrelation_reciprocal_le x C N q r₁ r₂ hx hC hr₁ hr₂ hderiv

/-- Natural-endpoint form of the concrete `k = 2` bound, for the interval
`A < n ≤ B`. -/
theorem reciprocalExpSum_fourth_le
    (x : ℝ) (A B q : ℕ) (hx : 0 < x) (hAB : A ≤ B)
    (hq : 1 ≤ q) (hqN : q ^ 2 ≤ B - A)
    (hderiv : 12 * x * (q : ℝ) ^ 3 ≤ ((A + 1 : ℕ) : ℝ) ^ 4) :
    ‖reciprocalExpSum x A B‖ ^ 4 ≤
      512 * ((B - A : ℕ) : ℝ) ^ 4 / (q : ℝ) ^ 2 +
        (512 : ℝ) * ((B - A : ℕ) : ℝ) ^ 3 *
            ((B + 1 : ℕ) : ℝ) ^ 4 / (6 * x) / (q : ℝ) ^ 3 *
          (finiteHarmonic (q ^ 2) * finiteHarmonic q) := by
  rw [reciprocalExpSum_eq_range x A B hAB]
  have h := reciprocalExpRange_fourth_le x (A + 1) (B - A) q
    hx (by omega) hq hqN hderiv
  have hend : A + 1 + (B - A) = B + 1 := by omega
  rw [hend] at h
  convert h using 1 <;> ring

/-- Natural-endpoint form of the first-derivative branch. -/
theorem norm_reciprocalExpSum_le_firstDerivative
    (x : ℝ) (A B : ℕ) (hx : 0 < x) (hAB : A ≤ B)
    (hhalf : x / ((A + 1 : ℕ) : ℝ) ^ 2 ≤ 1 / 2) :
    ‖reciprocalExpSum x A B‖ ≤ ((B + 1 : ℕ) : ℝ) ^ 2 / x := by
  rw [reciprocalExpSum_eq_range x A B hAB]
  have h := norm_reciprocalExpRange_le_firstDerivative x (A + 1) (B - A)
    hx (by omega) hhalf
  have hend : A + 1 + (B - A) = B + 1 := by omega
  simpa only [hend] using h

end

end Erdos175
