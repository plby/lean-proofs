import ErdosProblems.Erdos796.SmallPrimeBudget
import ErdosProblems.Erdos796.ElementaryPruningErrors
import ErdosProblems.Erdos796.CompleteBoxBound

/- Ported to Lean/Mathlib 4.33.0; imports and tactic elaboration adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Negligibility of the small-prime Bonferroni error

The finite small-prime budget contains the natural-valued error

`W(n)^2 * ceil(KsmallReal n)`.

We bound its real cast by

`L(n)^40 * (sqrt(n) + 2 * sqrt(n * sqrt(n)) + 1)`.

Here the inner occurrence of `sqrt(n)` is `Nat.sqrt n`; the middle term is
an elementary `n^(3/4)` surrogate.  Its fourth power is at most `n^3`, so
the normalized contribution is controlled by the fourth root of
`L(n)^164 / n`.  No prime-density estimate is used.
-/

namespace Erdos796

open Filter Topology

namespace SmallPrimeError

open PruningScales SmallPrimeBudget ElementaryPruningErrors

/-- The natural-valued Bonferroni error from the small-prime budget. -/
noncomputable def smallPrimeError (n : ℕ) : ℕ :=
  W n ^ 2 * Nat.ceil (KsmallReal n)

/-- An explicit real `n^(3/4)` surrogate built from the natural square
root. -/
noncomputable def threeQuarterRoot (n : ℕ) : ℝ :=
  Real.sqrt ((n : ℝ) * (n.sqrt : ℝ))

/-- Explicit elementary majorant for the small-prime error. -/
noncomputable def smallPrimeErrorMajorant (n : ℕ) : ℝ :=
  (logScale n : ℝ) ^ 40 *
    ((n.sqrt : ℝ) + 2 * threeQuarterRoot n + 1)

theorem threeQuarterRoot_nonneg (n : ℕ) :
    0 ≤ threeQuarterRoot n := by
  exact Real.sqrt_nonneg _

theorem smallPrimeErrorMajorant_nonneg (n : ℕ) :
    0 ≤ smallPrimeErrorMajorant n := by
  unfold smallPrimeErrorMajorant
  exact mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 40) (by
    have ht := threeQuarterRoot_nonneg n
    positivity)

/-- The KST radical in `KsmallReal` is bounded by twice the explicit
three-quarter-root surrogate. -/
theorem KsmallReal_le_threeQuarterMajorant (n : ℕ) :
    KsmallReal n ≤
      (n.sqrt : ℝ) + 2 * threeQuarterRoot n := by
  let s : ℝ := n.sqrt
  let N : ℝ := n
  have hs0 : 0 ≤ s := by positivity
  have hN0 : 0 ≤ N := by positivity
  have hchooseNat : Nat.choose n.sqrt 2 ≤ n.sqrt ^ 2 :=
    Nat.choose_le_pow n.sqrt 2
  have hchoose : (Nat.choose n.sqrt 2 : ℝ) ≤ s ^ 2 := by
    dsimp [s]
    exact_mod_cast hchooseNat
  have hss : s * s ≤ N := by
    dsimp [s, N]
    exact_mod_cast Nat.sqrt_le n
  have hrad :
      2 * s * (Nat.choose n.sqrt 2 : ℝ) ≤ 2 * N * s := by
    calc
      2 * s * (Nat.choose n.sqrt 2 : ℝ) ≤
          2 * s * s ^ 2 :=
        mul_le_mul_of_nonneg_left hchoose (mul_nonneg (by norm_num) hs0)
      _ = 2 * (s * s) * s := by ring
      _ ≤ 2 * N * s := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hss (by norm_num)) hs0
  have hsqrtRad :
      Real.sqrt
          (2 * s * (Nat.choose n.sqrt 2 : ℝ)) ≤
        Real.sqrt (2 * N * s) :=
    Real.sqrt_le_sqrt hrad
  have hNs0 : 0 ≤ N * s := mul_nonneg hN0 hs0
  have hsqrtTwo :
      Real.sqrt (2 * N * s) ≤ 2 * Real.sqrt (N * s) := by
    rw [Real.sqrt_le_iff]
    constructor
    · positivity
    · have hsquare := Real.sq_sqrt hNs0
      nlinarith
  unfold KsmallReal threeQuarterRoot
  change s +
      Real.sqrt (2 * s * (Nat.choose n.sqrt 2 : ℝ)) ≤
    s + 2 * Real.sqrt (N * s)
  exact add_le_add le_rfl (hsqrtRad.trans hsqrtTwo)

/-- The real cast of the natural error is bounded by the explicit
elementary majorant. -/
theorem cast_smallPrimeError_le_majorant (n : ℕ) :
    (smallPrimeError n : ℝ) ≤ smallPrimeErrorMajorant n := by
  have hK0 : 0 ≤ KsmallReal n := by
    unfold KsmallReal
    positivity
  have hceil : (Nat.ceil (KsmallReal n) : ℝ) ≤ KsmallReal n + 1 :=
    le_of_lt (Nat.ceil_lt_add_one hK0)
  have hfactor :
      (Nat.ceil (KsmallReal n) : ℝ) ≤
        (n.sqrt : ℝ) + 2 * threeQuarterRoot n + 1 := by
    have hK := KsmallReal_le_threeQuarterMajorant n
    linarith
  rw [smallPrimeError, Nat.cast_mul, cast_W_pow_two]
  unfold smallPrimeErrorMajorant
  exact mul_le_mul_of_nonneg_left hfactor
    (pow_nonneg (Nat.cast_nonneg _) 40)

/-- A nonnegative number whose fourth power is at most `y` is at most the
iterated square root of `y`. -/
theorem le_realFourthRoot_of_pow_four_le
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ^ 4 ≤ y) :
    x ≤ Tripartite.realFourthRoot y := by
  unfold Tripartite.realFourthRoot
  apply (Real.le_sqrt hx (Real.sqrt_nonneg y)).2
  apply (Real.le_sqrt (sq_nonneg x) hy).2
  nlinarith

/-- The polylogarithmically weighted `n^(3/4)` surrogate is negligible on
the second-order scale. -/
theorem logScale_pow_forty_mul_threeQuarterRoot_negligible :
    Tendsto
      (fun n : ℕ =>
        ((logScale n : ℝ) ^ 40 * threeQuarterRoot n) /
          secondOrderScale n)
      atTop (nhds 0) := by
  have hbase := logScale_pow_div_nat_tendsto_zero 164
  have hroot : Tendsto
      (fun n : ℕ =>
        Tripartite.realFourthRoot
          ((logScale n : ℝ) ^ 164 / (n : ℝ)))
      atTop (nhds 0) := by
    have h := hbase.sqrt.sqrt
    simpa [Tripartite.realFourthRoot] using! h
  refine squeeze_zero' ?_ ?_ hroot
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have hscale : 0 < secondOrderScale n := by
      unfold secondOrderScale
      have hlog : 0 < Real.log (n : ℝ) :=
        Real.log_pos (by exact_mod_cast (show 1 < n by omega))
      positivity
    exact div_nonneg
      (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 40)
        (threeQuarterRoot_nonneg n)) hscale.le
  · filter_upwards [eventually_ge_atTop 2] with n hn
    let L : ℝ := logScale n
    let N : ℝ := n
    let s : ℝ := n.sqrt
    let t : ℝ := threeQuarterRoot n
    have hNpos : 0 < N := by
      dsimp [N]
      positivity
    have hLpos : 0 < L := by
      dsimp [L]
      exact_mod_cast (show 0 < logScale n by simp [logScale])
    have hs0 : 0 ≤ s := by positivity
    have ht0 : 0 ≤ t := by
      dsimp [t]
      exact threeQuarterRoot_nonneg n
    have hlog : 0 < Real.log (n : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < n by omega))
    have hlogL : Real.log (n : ℝ) ≤ L := by
      simpa [L] using! log_natCast_le_logScale (show 0 < n by omega)
    have hss : s * s ≤ N := by
      dsimp [s, N]
      exact_mod_cast Nat.sqrt_le n
    have htsq : t ^ 2 = N * s := by
      dsimp [t, threeQuarterRoot, N, s]
      exact Real.sq_sqrt (by positivity)
    have ht4 : t ^ 4 ≤ N ^ 3 := by
      calc
        t ^ 4 = (t ^ 2) ^ 2 := by ring
        _ = (N * s) ^ 2 := by rw [htsq]
        _ = N ^ 2 * (s * s) := by ring
        _ ≤ N ^ 2 * N :=
          mul_le_mul_of_nonneg_left hss (sq_nonneg N)
        _ = N ^ 3 := by ring
    have hnormalized :
        (L ^ 41 * t / N) ^ 4 ≤ L ^ 164 / N := by
      calc
        (L ^ 41 * t / N) ^ 4 =
            L ^ 164 * t ^ 4 / N ^ 4 := by
          rw [div_pow, mul_pow, ← pow_mul]
        _ ≤ L ^ 164 * N ^ 3 / N ^ 4 := by
          apply (div_le_div_iff_of_pos_right (pow_pos hNpos 4)).2
          exact mul_le_mul_of_nonneg_left ht4
            (pow_nonneg hLpos.le 164)
        _ = L ^ 164 / N := by
          field_simp [hNpos.ne']
    have hrootBound :
        L ^ 41 * t / N ≤
          Tripartite.realFourthRoot (L ^ 164 / N) := by
      exact le_realFourthRoot_of_pow_four_le
        (div_nonneg
          (mul_nonneg (pow_nonneg hLpos.le 41) ht0) hNpos.le)
        (div_nonneg (pow_nonneg hLpos.le 164) hNpos.le)
        hnormalized
    have hnumerator :
        L ^ 40 * Real.log (n : ℝ) * t ≤ L ^ 41 * t := by
      have hmul := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlogL
          (pow_nonneg hLpos.le 40)) ht0
      simpa [pow_succ] using! hmul
    calc
      ((logScale n : ℝ) ^ 40 * threeQuarterRoot n) /
          secondOrderScale n =
          L ^ 40 * Real.log (n : ℝ) * t / N := by
        dsimp [L, N, t]
        unfold secondOrderScale
        field_simp [hNpos.ne', hlog.ne']
      _ ≤ L ^ 41 * t / N :=
        (div_le_div_iff_of_pos_right hNpos).2 hnumerator
      _ ≤ Tripartite.realFourthRoot (L ^ 164 / N) := hrootBound
      _ = Tripartite.realFourthRoot
          ((logScale n : ℝ) ^ 164 / (n : ℝ)) := by rfl

/-- The explicit elementary majorant is negligible. -/
theorem smallPrimeErrorMajorant_negligible :
    Tendsto
      (fun n : ℕ => smallPrimeErrorMajorant n / secondOrderScale n)
      atTop (nhds 0) := by
  have hfirst := logScale_pow_mul_sqrt_div_secondOrder_tendsto_zero 40
  have hmiddle := logScale_pow_forty_mul_threeQuarterRoot_negligible
  have hlast := logScale_pow_div_secondOrder_tendsto_zero 40
  have hsum := (hfirst.add (hmiddle.const_mul 2)).add hlast
  have heq :
      (fun n : ℕ =>
        ((logScale n : ℝ) ^ 40 * (n.sqrt : ℝ)) /
            secondOrderScale n +
          2 * (((logScale n : ℝ) ^ 40 * threeQuarterRoot n) /
            secondOrderScale n) +
          (logScale n : ℝ) ^ 40 / secondOrderScale n) =ᶠ[atTop]
        (fun n : ℕ =>
          smallPrimeErrorMajorant n / secondOrderScale n) := by
    exact Eventually.of_forall fun n => by
      unfold smallPrimeErrorMajorant
      ring
  have h := hsum.congr' heq
  simpa using! h

/-- The natural-valued small-prime Bonferroni error is negligible relative
to `secondOrderScale`. -/
theorem smallPrimeError_negligible :
    Tendsto
      (fun n : ℕ => (smallPrimeError n : ℝ) / secondOrderScale n)
      atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_ smallPrimeErrorMajorant_negligible
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
    exact (div_le_div_iff_of_pos_right hscale).2
      (cast_smallPrimeError_le_majorant n)

end SmallPrimeError

end Erdos796
