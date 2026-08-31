import ErdosProblems.Erdos796.PruningScales

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Negligibility of the elementary pruning losses

These are the losses that require no box or overlap summation: polynomially
many smooth cofactors, collision cleaning, small distinguished primes, and
the square-root prime-pair boundary.
-/

namespace Erdos796

open Filter Topology

namespace ElementaryPruningErrors

open PruningScales

theorem cast_Y_pow_six (n : ℕ) :
    ((Y n ^ 6 : ℕ) : ℝ) = (logScale n : ℝ) ^ 672 := by
  rw [Y, Nat.cast_pow, Nat.cast_pow, ← pow_mul]

theorem cast_R_pow_four (n : ℕ) :
    ((R n ^ 4 : ℕ) : ℝ) = (logScale n : ℝ) ^ 1792 := by
  rw [R, Nat.cast_pow, Nat.cast_pow, ← pow_mul]

theorem cast_Y_pow_four (n : ℕ) :
    ((Y n ^ 4 : ℕ) : ℝ) = (logScale n : ℝ) ^ 448 := by
  rw [Y, Nat.cast_pow, Nat.cast_pow, ← pow_mul]

theorem cast_W_pow_two (n : ℕ) :
    ((W n ^ 2 : ℕ) : ℝ) = (logScale n : ℝ) ^ 40 := by
  rw [W, Nat.cast_pow, Nat.cast_pow, ← pow_mul]

theorem Y_pow_six_negligible :
    Tendsto (fun n : ℕ => ((Y n ^ 6 : ℕ) : ℝ) / secondOrderScale n)
      atTop (nhds 0) := by
  exact (logScale_pow_div_secondOrder_tendsto_zero 672).congr'
    (Eventually.of_forall fun n => by
      exact congrArg (fun x : ℝ => x / secondOrderScale n)
        (cast_Y_pow_six n).symm)

theorem R_pow_four_negligible :
    Tendsto (fun n : ℕ => ((R n ^ 4 : ℕ) : ℝ) / secondOrderScale n)
      atTop (nhds 0) := by
  exact (logScale_pow_div_secondOrder_tendsto_zero 1792).congr'
    (Eventually.of_forall fun n => by
      exact congrArg (fun x : ℝ => x / secondOrderScale n)
        (cast_R_pow_four n).symm)

/-- Crude monotonicity bound sufficient for a small distinguished prime. -/
theorem primeCounting_sqrt_le_sqrt (n : ℕ) :
    Nat.primeCounting n.sqrt ≤ n.sqrt := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  exact (Finset.card_le_card (show Nat.primesLE n.sqrt ⊆
      positiveIcc n.sqrt by
    intro p hp
    have hp' := Nat.mem_primesLE.mp hp
    exact mem_positiveIcc.mpr ⟨hp'.2.one_le, hp'.1⟩)).trans_eq (by
      simp [positiveIcc])

/-- The `pi(sqrt n) * Y^4` losses are negligible. -/
theorem primeCounting_sqrt_mul_Y_pow_four_negligible :
    Tendsto
      (fun n : ℕ =>
        ((Nat.primeCounting n.sqrt * Y n ^ 4 : ℕ) : ℝ) /
          secondOrderScale n)
      atTop (nhds 0) := by
  have hupper := logScale_pow_mul_sqrt_div_secondOrder_tendsto_zero 448
  refine squeeze_zero' ?_ ?_ hupper
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hscale : 0 < secondOrderScale n := by
      unfold secondOrderScale
      have hlog : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      positivity
    exact div_nonneg (Nat.cast_nonneg _) hscale.le
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hscale : 0 < secondOrderScale n := by
      unfold secondOrderScale
      have hlog : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      positivity
    apply (div_le_div_iff_of_pos_right hscale).mpr
    have hp : (Nat.primeCounting n.sqrt : ℝ) ≤ (n.sqrt : ℝ) := by
      exact_mod_cast primeCounting_sqrt_le_sqrt n
    have hnum : ((Nat.primeCounting n.sqrt * Y n ^ 4 : ℕ) : ℝ) =
        (Nat.primeCounting n.sqrt : ℝ) * (logScale n : ℝ) ^ 448 := by
      rw [Nat.cast_mul, cast_Y_pow_four]
    rw [hnum]
    calc
      (Nat.primeCounting n.sqrt : ℝ) * (logScale n : ℝ) ^ 448 ≤
          (n.sqrt : ℝ) * (logScale n : ℝ) ^ 448 :=
        mul_le_mul_of_nonneg_right hp
          (pow_nonneg (Nat.cast_nonneg _) 448)
      _ = (logScale n : ℝ) ^ 448 * (n.sqrt : ℝ) := mul_comm _ _

/-- A typical `W^2 sqrt n` overlap remainder is negligible. -/
theorem W_sq_mul_sqrt_negligible :
    Tendsto
      (fun n : ℕ =>
        (((W n) ^ 2 * n.sqrt : ℕ) : ℝ) / secondOrderScale n)
      atTop (nhds 0) := by
  apply (logScale_pow_mul_sqrt_div_secondOrder_tendsto_zero 40).congr'
  apply Eventually.of_forall
  intro n
  apply congrArg (fun x : ℝ => x / secondOrderScale n)
  rw [Nat.cast_mul, cast_W_pow_two]

/-- The unit loss is negligible on the second-order scale. -/
theorem one_div_secondOrder_tendsto_zero :
    Tendsto (fun n : ℕ => (1 : ℝ) / secondOrderScale n)
      atTop (nhds 0) := by
  simpa using! logScale_pow_div_secondOrder_tendsto_zero 0

/-- A square prime count is controlled by twice the triangular small-prime
boundary, up to one harmless rounding unit. -/
theorem primeCounting_sqrt_sq_le_triangle (n : ℕ) :
    Nat.primeCounting n.sqrt ^ 2 ≤ 2 * smallPrimeTriangle n + 1 := by
  let p := Nat.primeCounting n.sqrt
  have hprod : p ^ 2 ≤ p * (p + 1) := by
    dsimp [p]
    nlinarith
  have hround : p * (p + 1) ≤ 2 * (p * (p + 1) / 2) + 1 := by
    omega
  exact hprod.trans (by simpa [p, smallPrimeTriangle] using! hround)

/-- Prime pairs with both primes at most `sqrt n` are negligible. -/
theorem primeCounting_sqrt_sq_negligible :
    Tendsto
      (fun n : ℕ => ((Nat.primeCounting n.sqrt ^ 2 : ℕ) : ℝ) /
        secondOrderScale n)
      atTop (nhds 0) := by
  have htri : Tendsto
      (fun n : ℕ => (2 : ℝ) *
        ((smallPrimeTriangle n : ℝ) / secondOrderScale n))
      atTop (nhds 0) := by
    simpa using! sqrtPrimePairBoundaryNegligible.const_mul 2
  have hupper : Tendsto
      (fun n : ℕ =>
        ((2 * smallPrimeTriangle n + 1 : ℕ) : ℝ) /
          secondOrderScale n)
      atTop (nhds 0) := by
    have hsum := htri.add one_div_secondOrder_tendsto_zero
    have heq :
        (fun n : ℕ =>
          ((2 * smallPrimeTriangle n + 1 : ℕ) : ℝ) /
            secondOrderScale n) =ᶠ[atTop]
        (fun n : ℕ =>
          2 * ((smallPrimeTriangle n : ℝ) / secondOrderScale n) +
            1 / secondOrderScale n) := by
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hscale : secondOrderScale n ≠ 0 := by
        unfold secondOrderScale
        have hlog : 0 < Real.log (n : ℝ) :=
          Real.log_pos (by exact_mod_cast (show 1 < n by omega))
        positivity
      push_cast
      field_simp
    have ht := hsum.congr' heq.symm
    simpa using! ht
  have hnonneg : ∀ᶠ n : ℕ in atTop,
      0 ≤ ((Nat.primeCounting n.sqrt ^ 2 : ℕ) : ℝ) / secondOrderScale n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hscale : 0 < secondOrderScale n := by
      unfold secondOrderScale
      have hlog : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      positivity
    positivity
  have hle : ∀ᶠ n : ℕ in atTop,
      ((Nat.primeCounting n.sqrt ^ 2 : ℕ) : ℝ) / secondOrderScale n ≤
        ((2 * smallPrimeTriangle n + 1 : ℕ) : ℝ) / secondOrderScale n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hscale : 0 < secondOrderScale n := by
      unfold secondOrderScale
      have hlog : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      positivity
    rw [div_le_div_iff_of_pos_right hscale]
    exact_mod_cast primeCounting_sqrt_sq_le_triangle n
  exact squeeze_zero' hnonneg hle hupper

end ElementaryPruningErrors

end Erdos796
