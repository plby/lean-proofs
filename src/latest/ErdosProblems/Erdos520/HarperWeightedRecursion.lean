import ErdosProblems.Erdos520.HarperFractionalRecursion

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open scoped ENNReal NNReal

namespace Erdos
namespace Problem520

/-!
# Weighted form of Harper's dyadic fractional-moment recursion

Harper's upper-bound iteration does not linearize the *raw* moments.  At
exponent `q` it first normalizes by the target

`(((1 - q) * N)⁻¹) ^ q`,

where in the application `N = sqrt (log log x)`.  Passing from
`q` to `(1 + q) / 2` doubles the reciprocal scale, while the Holder power
on the bad event cancels the factor `1 / (1 - q)` in the barrier height.

This file records those two exact identities and a general finite weighted
recursion theorem.  It is deliberately independent of the construction of
the good event and of the Euler-product moment itself.
-/

/-! ## A generic weighted nonlinear recursion -/

/-- A nonlinear fractional-moment recurrence can be iterated after division
by a varying target weight.

The hypothesis `htransfer` is the entire exponent bookkeeping: after the
next weight is raised to `theta m`, the bad-event coefficient must cost at
most `rho` times the current weight.  The elementary bound
`x ^ theta <= 1 + x` is then applied only to the *normalized* next moment.
Thus the additive `1` does not destroy a decaying unnormalized target. -/
theorem finite_weighted_fractional_contraction_recursion
    (M W theta bad : ℕ → ℝ) {L : ℕ} {A rho B : ℝ}
    (hA : 0 ≤ A) (hrho0 : 0 ≤ rho) (hrhoHalf : rho ≤ 1 / 2)
    (hW : ∀ m, m ≤ L → 0 < W m)
    (hM : ∀ m, m ≤ L → 0 ≤ M m)
    (htheta0 : ∀ m, m < L → 0 ≤ theta m)
    (htheta1 : ∀ m, m < L → theta m ≤ 1)
    (hbad0 : ∀ m, m < L → 0 ≤ bad m)
    (hrec : ∀ m, m < L →
      M m ≤ A * W m + bad m * (M (m + 1)) ^ (theta m))
    (htransfer : ∀ m, m < L →
      bad m * (W (m + 1)) ^ (theta m) ≤ rho * W m)
    (hbase : M L ≤ B * W L) (hB : 0 ≤ B) :
    M 0 ≤ W 0 * (2 * (A + rho) + B) := by
  let R : ℕ → ℝ := fun m ↦ M m / W m
  have hR0 : ∀ m, m ≤ L → 0 ≤ R m := by
    intro m hm
    exact div_nonneg (hM m hm) (hW m hm).le
  have hRrec : ∀ m, m < L →
      R m ≤ A + rho * (1 + R (m + 1)) := by
    intro m hm
    have hmL : m ≤ L := Nat.le_of_lt hm
    have hmsL : m + 1 ≤ L := by omega
    have hWm := hW m hmL
    have hWms := hW (m + 1) hmsL
    have hRms0 := hR0 (m + 1) hmsL
    have hfactor : W (m + 1) * R (m + 1) = M (m + 1) := by
      dsimp only [R]
      field_simp
    have hpower :
        (M (m + 1)) ^ (theta m) =
          (W (m + 1)) ^ (theta m) * (R (m + 1)) ^ (theta m) := by
      rw [← hfactor, Real.mul_rpow hWms.le hRms0]
    have hlinear :
        (R (m + 1)) ^ (theta m) ≤ 1 + R (m + 1) :=
      rpow_le_one_add_self hRms0 (htheta0 m hm) (htheta1 m hm)
    have hbadWeight0 :
        0 ≤ bad m * (W (m + 1)) ^ (theta m) :=
      mul_nonneg (hbad0 m hm) (Real.rpow_nonneg hWms.le _)
    have hbadPower :
        bad m * (M (m + 1)) ^ (theta m) ≤
          (rho * W m) * (1 + R (m + 1)) := by
      rw [hpower, ← mul_assoc]
      calc
        bad m * (W (m + 1)) ^ (theta m) *
              (R (m + 1)) ^ (theta m) ≤
            (bad m * (W (m + 1)) ^ (theta m)) *
              (1 + R (m + 1)) :=
          mul_le_mul_of_nonneg_left hlinear hbadWeight0
        _ ≤ (rho * W m) * (1 + R (m + 1)) :=
          mul_le_mul_of_nonneg_right (htransfer m hm) (by linarith)
    apply (div_le_iff₀ hWm).2
    calc
      M m ≤ A * W m + bad m * (M (m + 1)) ^ (theta m) :=
        hrec m hm
      _ ≤ A * W m + (rho * W m) * (1 + R (m + 1)) :=
        add_le_add_right hbadPower _
      _ = (A + rho * (1 + R (m + 1))) * W m := by ring
  have hRbase : R L ≤ B := by
    exact (div_le_iff₀ (hW L le_rfl)).2 (by
      simpa [mul_comm] using! hbase)
  have hRbound := finite_half_contraction_recursion R
    hA hrho0 hrhoHalf hRrec hRbase hB
  have hWzero := hW 0 (Nat.zero_le L)
  calc
    M 0 = W 0 * R 0 := by
      dsimp only [R]
      field_simp
    _ ≤ W 0 * (2 * (A + rho) + B) :=
      mul_le_mul_of_nonneg_left hRbound hWzero.le

/-! ## Harper's exact dyadic exponent and target weight -/

/-- Distance of the `m`-th Harper exponent from one. -/
noncomputable def harperDyadicMomentGap (m : ℕ) : ℝ :=
  1 - harperDyadicMomentExponent m

theorem harperDyadicMomentGap_eq (m : ℕ) :
    harperDyadicMomentGap m = 1 / (3 * (2 : ℝ) ^ m) := by
  unfold harperDyadicMomentGap harperDyadicMomentExponent
  ring

@[simp] theorem harperDyadicMomentGap_zero :
    harperDyadicMomentGap 0 = 1 / 3 := by
  norm_num [harperDyadicMomentGap_eq]

theorem harperDyadicMomentGap_pos (m : ℕ) :
    0 < harperDyadicMomentGap m := by
  rw [harperDyadicMomentGap_eq]
  positivity

theorem harperDyadicMomentGap_succ (m : ℕ) :
    harperDyadicMomentGap (m + 1) = harperDyadicMomentGap m / 2 := by
  rw [harperDyadicMomentGap_eq, harperDyadicMomentGap_eq, pow_succ]
  field_simp

/-- Holder exponent attached to the bad event at the `m`-th step. -/
noncomputable def harperDyadicBadHolderExponent (m : ℕ) : ℝ :=
  1 - harperDyadicMomentExponent m /
    harperDyadicMomentExponent (m + 1)

theorem harperDyadicBadHolderExponent_eq (m : ℕ) :
    harperDyadicBadHolderExponent m =
      harperDyadicMomentGap m /
        (1 + harperDyadicMomentExponent m) := by
  rw [harperDyadicBadHolderExponent,
    harperDyadicMomentExponent_succ]
  have hqpos := harperDyadicMomentExponent_pos m
  have hqone := harperDyadicMomentExponent_lt_one m
  unfold harperDyadicMomentGap
  field_simp
  ring

theorem harperDyadicBadHolderExponent_nonneg (m : ℕ) :
    0 ≤ harperDyadicBadHolderExponent m := by
  rw [harperDyadicBadHolderExponent_eq]
  exact div_nonneg (harperDyadicMomentGap_pos m).le (by
    linarith [harperDyadicMomentExponent_pos m])

theorem harperDyadicBadHolderExponent_le_one (m : ℕ) :
    harperDyadicBadHolderExponent m ≤ 1 := by
  rw [harperDyadicBadHolderExponent_eq]
  have hqpos := harperDyadicMomentExponent_pos m
  have hgap : harperDyadicMomentGap m =
      1 - harperDyadicMomentExponent m := rfl
  rw [div_le_one (by positivity)]
  rw [hgap]
  linarith

/-- The unnormalized target at scale `N`.  In Harper's application
`N = sqrt (log log x)`. -/
noncomputable def harperDyadicMomentWeight (N : ℝ) (m : ℕ) : ℝ :=
  (((harperDyadicMomentGap m) * N)⁻¹) ^
    (harperDyadicMomentExponent m)

theorem harperDyadicMomentWeight_pos {N : ℝ} (hN : 0 < N) (m : ℕ) :
    0 < harperDyadicMomentWeight N m := by
  unfold harperDyadicMomentWeight
  exact Real.rpow_pos_of_pos
    (inv_pos.mpr (mul_pos (harperDyadicMomentGap_pos m) hN)) _

@[simp] theorem harperDyadicMomentWeight_zero (N : ℝ) :
    harperDyadicMomentWeight N 0 =
      ((N / 3)⁻¹) ^ harperTwoThird := by
  simp only [harperDyadicMomentWeight, harperDyadicMomentGap_zero,
    harperDyadicMomentExponent_zero]
  congr 2
  ring

/-- Exact transport of the target weight through the Holder exponent.
The reciprocal scale doubles, producing precisely `2 ^ q_m`. -/
theorem harperDyadicMomentWeight_holder_exact
    {N : ℝ} (hN : 0 < N) (m : ℕ) :
    (harperDyadicMomentWeight N (m + 1)) ^
        (harperDyadicMomentExponent m /
          harperDyadicMomentExponent (m + 1)) =
      (2 : ℝ) ^ (harperDyadicMomentExponent m) *
        harperDyadicMomentWeight N m := by
  let q : ℝ := harperDyadicMomentExponent m
  let q' : ℝ := harperDyadicMomentExponent (m + 1)
  let s : ℝ := harperDyadicMomentGap m * N
  have hq' : 0 < q' := harperDyadicMomentExponent_pos (m + 1)
  have hs : 0 < s := mul_pos (harperDyadicMomentGap_pos m) hN
  have hscale : harperDyadicMomentGap (m + 1) * N = s / 2 := by
    dsimp only [s]
    rw [harperDyadicMomentGap_succ]
    ring
  have hqmul : q' * (q / q') = q := by
    field_simp
  change ((((harperDyadicMomentGap (m + 1) * N)⁻¹) ^ q') ^
      (q / q')) = (2 : ℝ) ^ q * ((s⁻¹) ^ q)
  rw [← Real.rpow_mul (inv_nonneg.mpr (mul_nonneg
    (harperDyadicMomentGap_pos (m + 1)).le hN.le))]
  rw [hqmul, hscale]
  have hinvScale : (s / 2)⁻¹ = 2 * s⁻¹ := by
    field_simp
  rw [hinvScale, Real.mul_rpow (by norm_num) (inv_nonneg.mpr hs.le)]

/-! ## Cancellation of the barrier height against Holder -/

/-- Algebraic cancellation behind Harper's choice
`2 * C / (1 - q)` in the fair-probability exponent. -/
theorem harperDyadicBarrierHolder_cancel (C : ℝ) (m : ℕ) :
    (-2 * C / harperDyadicMomentGap m) *
        harperDyadicBadHolderExponent m =
      -2 * C / (1 + harperDyadicMomentExponent m) := by
  rw [harperDyadicBadHolderExponent_eq]
  have hgap := ne_of_gt (harperDyadicMomentGap_pos m)
  have hden : 1 + harperDyadicMomentExponent m ≠ 0 :=
    ne_of_gt (by linarith [harperDyadicMomentExponent_pos m])
  field_simp

/-- A bad-event estimate `exp (-2*C/(1-q))` therefore contributes at most
`exp (-C)` after Holder, uniformly along the dyadic ladder. -/
theorem harperDyadicBadHolderCoefficient_le
    {C : ℝ} (hC : 0 ≤ C) (m : ℕ) :
    (Real.exp (-2 * C / harperDyadicMomentGap m)) ^
        (harperDyadicBadHolderExponent m) ≤
      Real.exp (-C) := by
  rw [← Real.exp_mul, harperDyadicBarrierHolder_cancel]
  rw [Real.exp_le_exp]
  have hqpos := harperDyadicMomentExponent_pos m
  have hqone := harperDyadicMomentExponent_lt_one m
  have hden : 0 < 1 + harperDyadicMomentExponent m := by linarith
  apply (div_le_iff₀ hden).2
  nlinarith

/-- Combining the bad-event Holder coefficient with the transported target
weight costs at most the uniform contraction `2 * exp (-C)`. -/
theorem harperDyadicBadWeight_transfer
    {N C : ℝ} (hN : 0 < N) (hC : 0 ≤ C) (m : ℕ) :
    (Real.exp (-2 * C / harperDyadicMomentGap m)) ^
          (harperDyadicBadHolderExponent m) *
        (harperDyadicMomentWeight N (m + 1)) ^
          (harperDyadicMomentExponent m /
            harperDyadicMomentExponent (m + 1)) ≤
      (2 * Real.exp (-C)) * harperDyadicMomentWeight N m := by
  rw [harperDyadicMomentWeight_holder_exact hN]
  have hbad := harperDyadicBadHolderCoefficient_le hC m
  have hpow : (2 : ℝ) ^ harperDyadicMomentExponent m ≤ 2 := by
    simpa only [Real.rpow_one] using!
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
        (harperDyadicMomentExponent_lt_one m).le
  have hweight0 := (harperDyadicMomentWeight_pos hN m).le
  have hbad0 : 0 ≤
      (Real.exp (-2 * C / harperDyadicMomentGap m)) ^
        (harperDyadicBadHolderExponent m) :=
    Real.rpow_nonneg (Real.exp_pos _).le _
  have hexp0 := (Real.exp_pos (-C)).le
  calc
    (Real.exp (-2 * C / harperDyadicMomentGap m)) ^
          (harperDyadicBadHolderExponent m) *
        ((2 : ℝ) ^ harperDyadicMomentExponent m *
          harperDyadicMomentWeight N m) =
        ((Real.exp (-2 * C / harperDyadicMomentGap m)) ^
          (harperDyadicBadHolderExponent m) *
            (2 : ℝ) ^ harperDyadicMomentExponent m) *
          harperDyadicMomentWeight N m := by ring
    _ ≤ (Real.exp (-C) * 2) * harperDyadicMomentWeight N m := by
      apply mul_le_mul_of_nonneg_right _ hweight0
      exact mul_le_mul hbad hpow
        (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) _) hexp0
    _ = (2 * Real.exp (-C)) * harperDyadicMomentWeight N m := by ring

/-- It is enough to take `C >= log 4` for the preceding coefficient to be
at most one half.  (The analytic key propositions may of course require a
larger fixed `C`.) -/
theorem two_mul_exp_neg_le_half {C : ℝ}
    (hC : Real.log 4 ≤ C) :
    2 * Real.exp (-C) ≤ 1 / 2 := by
  have hExp : Real.exp (-C) ≤ Real.exp (-Real.log 4) := by
    rw [Real.exp_le_exp]
    linarith
  have hlog : Real.exp (-Real.log 4) = (1 / 4 : ℝ) := by
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    norm_num
  rw [hlog] at hExp
  nlinarith

/-- Harper's numerical iteration in raw-moment coordinates.  Each good term
is `A` times the exponent-dependent target weight.  The bad event has the
published exponential scale `exp (-2*C/(1-q_m))`, and Holder is applied at
`q_m < q_(m+1)`.  If `C >= log 4`, the weighted bad branch contracts by at
most one half at every step. -/
theorem harperDyadicWeightedMomentIteration
    (M : ℕ → ℝ) {N C A B : ℝ} {L : ℕ}
    (hN : 0 < N) (hC : Real.log 4 ≤ C)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hM : ∀ m, m ≤ L → 0 ≤ M m)
    (hrec : ∀ m, m < L →
      M m ≤ A * harperDyadicMomentWeight N m +
        (Real.exp (-2 * C / harperDyadicMomentGap m)) ^
            (harperDyadicBadHolderExponent m) *
          (M (m + 1)) ^
            (harperDyadicMomentExponent m /
              harperDyadicMomentExponent (m + 1)))
    (hbase : M L ≤ B * harperDyadicMomentWeight N L) :
    M 0 ≤ harperDyadicMomentWeight N 0 *
      (2 * (A + 2 * Real.exp (-C)) + B) := by
  let theta : ℕ → ℝ := fun m ↦
    harperDyadicMomentExponent m /
      harperDyadicMomentExponent (m + 1)
  let bad : ℕ → ℝ := fun m ↦
    (Real.exp (-2 * C / harperDyadicMomentGap m)) ^
      (harperDyadicBadHolderExponent m)
  have hC0 : 0 ≤ C := by
    have hlog : 0 < Real.log 4 := Real.log_pos (by norm_num)
    linarith
  have htheta0 : ∀ m, m < L → 0 ≤ theta m := by
    intro m hm
    exact div_nonneg (harperDyadicMomentExponent_pos m).le
      (harperDyadicMomentExponent_pos (m + 1)).le
  have htheta1 : ∀ m, m < L → theta m ≤ 1 := by
    intro m hm
    exact (div_le_one (harperDyadicMomentExponent_pos (m + 1))).2
      (harperDyadicMomentExponent_strictMono (Nat.lt_succ_self m)).le
  have hbad0 : ∀ m, m < L → 0 ≤ bad m := by
    intro m hm
    exact Real.rpow_nonneg (Real.exp_pos _).le _
  have htransfer : ∀ m, m < L →
      bad m *
          (harperDyadicMomentWeight N (m + 1)) ^ (theta m) ≤
        (2 * Real.exp (-C)) * harperDyadicMomentWeight N m := by
    intro m hm
    exact harperDyadicBadWeight_transfer hN hC0 m
  apply finite_weighted_fractional_contraction_recursion
    M (harperDyadicMomentWeight N) theta bad
      hA (mul_nonneg (by norm_num) (Real.exp_pos _).le)
      (two_mul_exp_neg_le_half hC)
      (fun m hm ↦ harperDyadicMomentWeight_pos hN m)
      hM htheta0 htheta1 hbad0
  · simpa only [theta, bad] using! hrec
  · exact htransfer
  · exact hbase
  · exact hB

/-! ## Initial saving and stopping condition -/

/-- At the initial exponent `2/3`, the target is exactly the desired
inverse `2/3` power of `N/3`. -/
theorem harperDyadicMomentWeight_initial (N : ℝ) :
    harperDyadicMomentWeight N 0 = ((N / 3)⁻¹) ^ (2 / 3 : ℝ) := by
  rw [harperDyadicMomentWeight_zero]
  rfl

/-- With `N = sqrt n`, the initial target is exactly a constant times the
required `n^(-1/3)` saving. -/
theorem harperDyadicMomentWeight_sqrt_initial
    {n : ℝ} (hn : 0 < n) :
    harperDyadicMomentWeight (Real.sqrt n) 0 =
      (3 : ℝ) ^ (2 / 3 : ℝ) * n ^ (-1 / 3 : ℝ) := by
  rw [harperDyadicMomentWeight_initial]
  have hsqrt := Real.sqrt_pos.2 hn
  have hinv : (Real.sqrt n / 3)⁻¹ = 3 * (Real.sqrt n)⁻¹ := by
    field_simp
  rw [hinv, Real.mul_rpow (by norm_num) (inv_nonneg.mpr hsqrt.le)]
  rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hn.le,
    ← Real.rpow_mul hn.le]
  congr 2
  ring

/-- Once `(1-q_L)N <= 1`, Jensen's trivial bound `M_L <= 1` is no larger
than the terminal target weight. -/
theorem one_le_harperDyadicMomentWeight_of_stop
    {N : ℝ} (hN : 0 < N) {L : ℕ}
    (hstop : harperDyadicMomentGap L * N ≤ 1) :
    1 ≤ harperDyadicMomentWeight N L := by
  unfold harperDyadicMomentWeight
  have hscale : 0 < harperDyadicMomentGap L * N :=
    mul_pos (harperDyadicMomentGap_pos L) hN
  exact Real.one_le_rpow ((one_le_inv₀ hscale).2 hstop)
    (harperDyadicMomentExponent_pos L).le

/-- Harper stops one dyadic interval earlier, when
`(1-q_L)N <= 2`.  The trivial terminal bound `M_L <= 1` then costs only the
fixed normalized base constant `B = 2`. -/
theorem one_le_two_mul_harperDyadicMomentWeight_of_paper_stop
    {N : ℝ} (hN : 0 < N) {L : ℕ}
    (hstop : harperDyadicMomentGap L * N ≤ 2) :
    1 ≤ 2 * harperDyadicMomentWeight N L := by
  let s : ℝ := harperDyadicMomentGap L * N
  have hs : 0 < s := mul_pos (harperDyadicMomentGap_pos L) hN
  have hhalfInv : (1 / 2 : ℝ) ≤ s⁻¹ := by
    rw [inv_eq_one_div]
    exact (le_div_iff₀ hs).2 (by dsimp only [s]; nlinarith)
  have hq0 := (harperDyadicMomentExponent_pos L).le
  have hbase :
      (1 / 2 : ℝ) ^ harperDyadicMomentExponent L ≤
        s⁻¹ ^ harperDyadicMomentExponent L :=
    Real.rpow_le_rpow (by norm_num) hhalfInv hq0
  have hhalf : (1 / 2 : ℝ) ≤
      (1 / 2 : ℝ) ^ harperDyadicMomentExponent L := by
    simpa only [Real.rpow_one] using!
      Real.rpow_le_rpow_of_exponent_ge
        (by norm_num : (0 : ℝ) < 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1)
        (harperDyadicMomentExponent_lt_one L).le
  change 1 ≤ 2 * (s⁻¹ ^ harperDyadicMomentExponent L)
  nlinarith

/-- The stopping condition written in the numerical form used in the
paper: `2^L >= N/3`. -/
theorem harperDyadic_stop_iff {N : ℝ} (L : ℕ) :
    harperDyadicMomentGap L * N ≤ 1 ↔
      N / 3 ≤ (2 : ℝ) ^ L := by
  rw [harperDyadicMomentGap_eq]
  have hden : 0 < 3 * (2 : ℝ) ^ L := by positivity
  rw [one_div_mul_eq_div, div_le_one hden,
    div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
  simp only [mul_comm]

/-- The exact stopping depth used in the paper is the first `L` satisfying
`2^L >= N/6`, equivalently `(1-q_L)N <= 2`. -/
theorem harperDyadic_paper_stop_iff {N : ℝ} (L : ℕ) :
    harperDyadicMomentGap L * N ≤ 2 ↔
      N / 6 ≤ (2 : ℝ) ^ L := by
  rw [harperDyadicMomentGap_eq]
  have hden : 0 < 3 * (2 : ℝ) ^ L := by positivity
  rw [one_div_mul_eq_div, div_le_iff₀ hden,
    div_le_iff₀ (by norm_num : (0 : ℝ) < 6)]
  constructor <;> intro h <;> nlinarith

end Problem520
end Erdos
