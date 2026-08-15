import ErdosProblems.Erdos888.PrimeEstimates
import ErdosProblems.Erdos888.BlockMajorant
import ErdosProblems.Erdos888.RectangleTerm
import ErdosProblems.Erdos888.DyadicSums
import ErdosProblems.Erdos888.DyadicTransport

/-!
# The dyadic rectangle-sum bridge for Erdős problem 888

This file connects the `T^(3/4) M N` term supplied by coloured Kővári--
Sós--Turán to the harmonic convolution estimated in `RectangleTerm`.

At ambient scale `n = 2^J`, write `i ≤ j` for the endpoint-prime scales
and put `k = J - i - j`.  The trivial core bound and the two prime-counting
bounds leave the weight

`2^J q^k / ((i+1)(j+1))`,  where `q = 2^(-1/4)`.

The definition `dyadicRectangleMajorant` below uses `(i,k)` as its finite
coordinates; its associated right index is `j = J-i-k`.  Thus the range
`k < J-2i+1` says exactly `i ≤ j` and `i+j ≤ J`.  This slack-coordinate
form makes the final summation transparent: the elementary inequality

`(J-i+1)/(J-i-k+1) ≤ k+1`

reduces the inner sum to a fixed convergent weighted geometric series.
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace Erdos888
namespace RectangleBridge

noncomputable section

/-- The geometric loss for one unit of unused dyadic exponent.  Algebraically
this is `2^(-1/4)`, expressed through the radical already used by the KST
bound. -/
def quarterDecay : ℝ := threeQuarterRoot 2 / 2

lemma threeQuarterRoot_nonneg (x : ℝ) : 0 ≤ threeQuarterRoot x := by
  exact Real.sqrt_nonneg _

lemma threeQuarterRoot_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    threeQuarterRoot x ≤ threeQuarterRoot y := by
  unfold threeQuarterRoot
  apply Real.sqrt_le_sqrt
  exact mul_le_mul hxy (Real.sqrt_le_sqrt hxy) (Real.sqrt_nonneg x)
    (hx.trans hxy)

lemma threeQuarterRoot_mul {x y : ℝ} (hx : 0 ≤ x) (_hy : 0 ≤ y) :
    threeQuarterRoot (x * y) = threeQuarterRoot x * threeQuarterRoot y := by
  unfold threeQuarterRoot
  rw [Real.sqrt_mul hx, show x * y * (Real.sqrt x * Real.sqrt y) =
      (x * Real.sqrt x) * (y * Real.sqrt y) by ring]
  rw [Real.sqrt_mul (mul_nonneg hx (Real.sqrt_nonneg x))]

lemma threeQuarterRoot_pow (x : ℝ) (hx : 0 ≤ x) (m : ℕ) :
    threeQuarterRoot (x ^ m) = threeQuarterRoot x ^ m := by
  induction m with
  | zero => simp [threeQuarterRoot]
  | succ m ih =>
      rw [pow_succ, pow_succ, threeQuarterRoot_mul (pow_nonneg hx m) hx, ih]

lemma quarterDecay_nonneg : 0 ≤ quarterDecay := by
  exact div_nonneg (threeQuarterRoot_nonneg 2) (by norm_num)

/-- A deliberately rational numerical upper bound on `2^(-1/4)`. -/
lemma quarterDecay_le_six_sevenths : quarterDecay ≤ (6 / 7 : ℝ) := by
  unfold quarterDecay threeQuarterRoot
  have hs2 : Real.sqrt (2 : ℝ) ≤ 10 / 7 := by
    apply (Real.sqrt_le_iff).2
    constructor <;> norm_num
  have hprod : (2 : ℝ) * Real.sqrt 2 ≤ 20 / 7 := by linarith
  have hs6 : Real.sqrt ((2 : ℝ) * Real.sqrt 2) ≤ 12 / 7 := by
    apply (Real.sqrt_le_iff).2
    constructor
    · norm_num
    · nlinarith
  linarith

lemma quarterDecay_lt_one : quarterDecay < 1 :=
  quarterDecay_le_six_sevenths.trans_lt (by norm_num)

/-- A finite weighted geometric sum, with a constant independent of the
truncation point. -/
lemma sum_range_succ_mul_quarterDecay_le (m : ℕ) :
    (∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℝ) * quarterDecay ^ k) ≤ 49 := by
  let q : ℝ := (6 / 7 : ℝ)
  have hq0 : 0 ≤ q := by norm_num [q]
  have hq1 : ‖q‖ < 1 := by norm_num [q, abs_of_nonneg hq0]
  calc
    (∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℝ) * quarterDecay ^ k) ≤
        ∑ k ∈ Finset.range m, ((k + 1 : ℕ) : ℝ) * q ^ k := by
      apply Finset.sum_le_sum
      intro k hk
      exact mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ quarterDecay_nonneg quarterDecay_le_six_sevenths k)
        (by positivity)
    _ ≤ ∑' k : ℕ, ((k + 1 : ℕ) : ℝ) * q ^ k := by
      apply Summable.sum_le_tsum (s := Finset.range m)
      · intro k hk
        positivity
      · simpa only [Nat.cast_add, Nat.cast_one, Nat.choose_one_right] using
          (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 1 hq1)
    _ = 49 := by
      rw [show (fun k : ℕ ↦ ((k + 1 : ℕ) : ℝ) * q ^ k) =
          (fun k : ℕ ↦ (((k + 1).choose 1 : ℕ) : ℝ) * q ^ k) by
        funext k
        simp]
      rw [tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 hq1]
      norm_num [q]

/-- The right-hand dyadic index represented by a slack coordinate. -/
def rightIndex (J i k : ℕ) : ℕ := J - i - k

lemma rightIndex_constraints {J i k : ℕ} (hk : k < J + 1 - 2 * i) :
    i ≤ rightIndex J i k ∧ i + rightIndex J i k ≤ J := by
  unfold rightIndex
  constructor <;> omega

/-- The explicit finite `S₁` majorant at ambient size `2^J`.

The inner coordinate `k` is the slack `J-i-j`; consequently its range is
equivalent to `i ≤ j` and `i+j ≤ J`. -/
def dyadicRectangleMajorant (J : ℕ) : ℝ :=
  (2 : ℝ) ^ J *
    ∑ i ∈ Finset.range (J + 1),
      ∑ k ∈ Finset.range (J + 1 - 2 * i),
        quarterDecay ^ k * ((i + 1 : ℕ) : ℝ)⁻¹ *
          ((rightIndex J i k + 1 : ℕ) : ℝ)⁻¹

lemma dyadicRectangleMajorant_nonneg (J : ℕ) :
    0 ≤ dyadicRectangleMajorant J := by
  unfold dyadicRectangleMajorant
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg
    (mul_nonneg (pow_nonneg quarterDecay_nonneg k) (inv_nonneg.mpr (by positivity)))
    (inv_nonneg.mpr (by positivity))

private lemma slack_denominator_le {J i k : ℕ}
    (hk : k < J + 1 - 2 * i) :
    (((rightIndex J i k + 1 : ℕ) : ℝ)⁻¹) ≤
      ((k + 1 : ℕ) : ℝ) * (((J - i + 1 : ℕ) : ℝ)⁻¹) := by
  have hjpos : (0 : ℝ) < (rightIndex J i k + 1 : ℕ) := by positivity
  have hKpos : (0 : ℝ) < (J - i + 1 : ℕ) := by positivity
  rw [← one_div, ← div_eq_mul_inv]
  apply (le_div_iff₀ hKpos).2
  rw [one_div]
  rw [inv_mul_eq_div]
  apply (div_le_iff₀ hjpos).2
  unfold rightIndex
  have heq : J - i + 1 = (J - i - k + 1) + k := by omega
  rw [heq]
  push_cast
  have hk0 : (0 : ℝ) ≤ k := by positivity
  have hr1 : (1 : ℝ) ≤ ((J - i - k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le (J - i - k)))
  nlinarith

/-- Pointwise comparison of the complete finite dyadic rectangle sum with
the harmonic convolution.  The constant `49` is the value of
`∑ (k+1)(6/7)^k`. -/
theorem dyadicRectangleMajorant_le_rectangleTerm (J : ℕ) :
    dyadicRectangleMajorant J ≤
      49 * RectangleTerm.rectangleTerm J := by
  unfold dyadicRectangleMajorant RectangleTerm.rectangleTerm
  have hpow : 0 ≤ (2 : ℝ) ^ J := by positivity
  have hsum :
      (∑ i ∈ Finset.range (J + 1),
          ∑ k ∈ Finset.range (J + 1 - 2 * i),
            quarterDecay ^ k * ((i + 1 : ℕ) : ℝ)⁻¹ *
              ((rightIndex J i k + 1 : ℕ) : ℝ)⁻¹) ≤
        49 * DyadicSums.harmonicConvolution J := by
    calc
      (∑ i ∈ Finset.range (J + 1),
          ∑ k ∈ Finset.range (J + 1 - 2 * i),
            quarterDecay ^ k * ((i + 1 : ℕ) : ℝ)⁻¹ *
              ((rightIndex J i k + 1 : ℕ) : ℝ)⁻¹) ≤
        ∑ i ∈ Finset.range (J + 1),
          49 * (((i + 1 : ℕ) : ℝ)⁻¹ *
            ((J - i + 1 : ℕ) : ℝ)⁻¹) := by
        apply Finset.sum_le_sum
        intro i hi
        calc
          (∑ k ∈ Finset.range (J + 1 - 2 * i),
              quarterDecay ^ k * ((i + 1 : ℕ) : ℝ)⁻¹ *
                ((rightIndex J i k + 1 : ℕ) : ℝ)⁻¹) ≤
              ∑ k ∈ Finset.range (J + 1 - 2 * i),
                (((k + 1 : ℕ) : ℝ) * quarterDecay ^ k) *
                  (((i + 1 : ℕ) : ℝ)⁻¹ *
                    ((J - i + 1 : ℕ) : ℝ)⁻¹) := by
            apply Finset.sum_le_sum
            intro k hk
            have hden := slack_denominator_le
              (J := J) (i := i) (k := k) (Finset.mem_range.1 hk)
            have hq : 0 ≤ quarterDecay ^ k := pow_nonneg quarterDecay_nonneg k
            have hi0 : 0 ≤ (((i + 1 : ℕ) : ℝ)⁻¹) := by positivity
            calc
              quarterDecay ^ k * ((i + 1 : ℕ) : ℝ)⁻¹ *
                    ((rightIndex J i k + 1 : ℕ) : ℝ)⁻¹ ≤
                  quarterDecay ^ k * ((i + 1 : ℕ) : ℝ)⁻¹ *
                    (((k + 1 : ℕ) : ℝ) *
                      ((J - i + 1 : ℕ) : ℝ)⁻¹) :=
                mul_le_mul_of_nonneg_left hden (mul_nonneg hq hi0)
              _ = (((k + 1 : ℕ) : ℝ) * quarterDecay ^ k) *
                    (((i + 1 : ℕ) : ℝ)⁻¹ *
                      ((J - i + 1 : ℕ) : ℝ)⁻¹) := by ring
          _ = (∑ k ∈ Finset.range (J + 1 - 2 * i),
                ((k + 1 : ℕ) : ℝ) * quarterDecay ^ k) *
                (((i + 1 : ℕ) : ℝ)⁻¹ *
                  ((J - i + 1 : ℕ) : ℝ)⁻¹) := by rw [Finset.sum_mul]
          _ ≤ 49 * (((i + 1 : ℕ) : ℝ)⁻¹ *
                ((J - i + 1 : ℕ) : ℝ)⁻¹) := by
            apply mul_le_mul_of_nonneg_right
              (sum_range_succ_mul_quarterDecay_le _) (by positivity)
      _ = 49 * DyadicSums.harmonicConvolution J := by
        unfold DyadicSums.harmonicConvolution
        rw [Finset.mul_sum]
  calc
    (2 : ℝ) ^ J *
        (∑ i ∈ Finset.range (J + 1),
          ∑ k ∈ Finset.range (J + 1 - 2 * i),
            quarterDecay ^ k * ((i + 1 : ℕ) : ℝ)⁻¹ *
              ((rightIndex J i k + 1 : ℕ) : ℝ)⁻¹) ≤
        (2 : ℝ) ^ J * (49 * DyadicSums.harmonicConvolution J) :=
      mul_le_mul_of_nonneg_left hsum hpow
    _ = 49 * ((2 : ℝ) ^ J * DyadicSums.harmonicConvolution J) := by ring

/-- The explicit dyadic majorant already has the required Erdős-888 order. -/
theorem dyadicRectangleMajorant_isBigO_dyadicScale :
    dyadicRectangleMajorant =O[atTop]
      (fun J : ℕ ↦ scale (2 ^ J)) := by
  have hrect : dyadicRectangleMajorant =O[atTop]
      RectangleTerm.rectangleTerm := by
    apply IsBigO.of_bound 49
    filter_upwards with J
    rw [Real.norm_of_nonneg (dyadicRectangleMajorant_nonneg J),
      Real.norm_of_nonneg (RectangleTerm.rectangleTerm_nonneg J)]
    exact dyadicRectangleMajorant_le_rectangleTerm J
  exact hrect.trans RectangleTerm.rectangleTerm_isBigO_dyadicScale

/-! ## Arithmetic input for the finite majorant -/

lemma dyadicPrimeBlock_eq_dyadicPrimes (i : ℕ) :
    dyadicPrimeBlock i = dyadicPrimes (2 ^ i) := by
  ext p
  simp only [mem_dyadicPrimeBlock, mem_dyadicPrimes]
  rw [pow_succ]
  simp only [Nat.mul_comm]

/-- The regularized logarithm on `2^i` is bounded below by a fixed multiple
of `i+1`, uniformly down to `i=0`. -/
lemma half_nat_succ_le_lambda_two_pow (i : ℕ) :
    (((i + 1 : ℕ) : ℝ) / 2) ≤ lambda ((2 ^ i : ℕ) : ℝ) := by
  rw [lambda_eq_one_add_log (by positivity : (((2 ^ i : ℕ) : ℝ) ≠ 0)),
    Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  have hlog2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  push_cast
  nlinarith [mul_le_mul_of_nonneg_left hlog2 (Nat.cast_nonneg i)]

/-- A single positive constant controls every exponent-indexed prime block
in the form used by the dyadic summation. -/
theorem exists_forall_dyadicPrimeBlock_card_le :
    ∃ C : ℝ, 0 < C ∧ ∀ i : ℕ,
      ((dyadicPrimeBlock i).card : ℝ) ≤
        2 * C * (2 : ℝ) ^ i * (((i + 1 : ℕ) : ℝ)⁻¹) := by
  obtain ⟨C, hC, hprime⟩ := exists_forall_dyadicPrimeCount_le_scale
  refine ⟨C, hC, fun i ↦ ?_⟩
  have hlam : 0 < lambda (((2 : ℕ) ^ i : ℕ) : ℝ) :=
    lambda_pos (by
      exact_mod_cast (one_le_pow₀ (by norm_num : 1 ≤ (2 : ℕ))))
  have hhalf := half_nat_succ_le_lambda_two_pow i
  have hraw : ((dyadicPrimeBlock i).card : ℝ) ≤
      C * ((((2 : ℕ) ^ i : ℕ) : ℝ) /
        lambda (((2 : ℕ) ^ i : ℕ) : ℝ)) := by
    rw [dyadicPrimeBlock_eq_dyadicPrimes]
    exact hprime (2 ^ i)
  calc
    ((dyadicPrimeBlock i).card : ℝ) ≤
        C * ((((2 : ℕ) ^ i : ℕ) : ℝ) /
          lambda (((2 : ℕ) ^ i : ℕ) : ℝ)) := hraw
    _ ≤ C * ((((2 : ℕ) ^ i : ℕ) : ℝ) /
          (((i + 1 : ℕ) : ℝ) / 2)) := by
      apply mul_le_mul_of_nonneg_left _ hC.le
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) hhalf
    _ = 2 * C * (2 : ℝ) ^ i * (((i + 1 : ℕ) : ℝ)⁻¹) := by
      rw [Nat.cast_pow, Nat.cast_ofNat]
      field_simp

/-- The trivial core-count estimate `T ≤ n/(2^i 2^j)`, including the
integer rounding in the definition of `blockCoreCandidates`. -/
theorem blockCoreCandidates_card_le_div (n i j : ℕ) :
    (blockCoreCandidates n i j).card ≤ n / (2 ^ i * 2 ^ j) := by
  have hsubset : blockCoreCandidates n i j ⊆
      Finset.Icc 1 (n / (2 ^ i * 2 ^ j)) := by
    intro c hc
    have hc' := mem_blockCoreCandidates.mp hc
    apply Finset.mem_Icc.mpr
    refine ⟨hc'.1, (Nat.le_div_iff_mul_le (by positivity)).2 ?_⟩
    simpa [Nat.mul_assoc] using hc'.2.2.2.2.1
  calc
    (blockCoreCandidates n i j).card ≤
        (Finset.Icc 1 (n / (2 ^ i * 2 ^ j))).card :=
      Finset.card_le_card hsubset
    _ ≤ n / (2 ^ i * 2 ^ j) := by simp

private lemma cast_two_pow_div_eq (J i j : ℕ) (hij : i + j ≤ J) :
    (((2 : ℕ) ^ J : ℕ) : ℝ) /
        ((((2 : ℕ) ^ i : ℕ) : ℝ) * (((2 : ℕ) ^ j : ℕ) : ℝ)) =
      (2 : ℝ) ^ (J - i - j) := by
  push_cast
  have he : J = i + j + (J - i - j) := by omega
  have hpow : (2 : ℝ) ^ J =
      ((2 : ℝ) ^ i * (2 : ℝ) ^ j) * (2 : ℝ) ^ (J - i - j) := by
    calc
      (2 : ℝ) ^ J = (2 : ℝ) ^ (i + j + (J - i - j)) :=
        congrArg (fun m : ℕ ↦ (2 : ℝ) ^ m) he
      _ = ((2 : ℝ) ^ i * (2 : ℝ) ^ j) *
          (2 : ℝ) ^ (J - i - j) := by rw [pow_add, pow_add]
  field_simp
  exact hpow

private lemma threeQuarterRoot_two_pow_mul (J i j : ℕ)
    (hij : i + j ≤ J) :
    threeQuarterRoot ((2 : ℝ) ^ (J - i - j)) * (2 : ℝ) ^ i * (2 : ℝ) ^ j =
      (2 : ℝ) ^ J * quarterDecay ^ (J - i - j) := by
  let s := J - i - j
  have hs : i + j + s = J := by dsimp [s]; omega
  have hq : quarterDecay * 2 = threeQuarterRoot 2 := by
    unfold quarterDecay
    ring
  calc
    threeQuarterRoot ((2 : ℝ) ^ s) * (2 : ℝ) ^ i * (2 : ℝ) ^ j =
        threeQuarterRoot 2 ^ s * (2 : ℝ) ^ i * (2 : ℝ) ^ j := by
      rw [threeQuarterRoot_pow 2 (by norm_num) s]
    _ = (quarterDecay ^ s * (2 : ℝ) ^ s) *
          (2 : ℝ) ^ i * (2 : ℝ) ^ j := by rw [← mul_pow, hq]
    _ = (2 : ℝ) ^ (i + j + s) * quarterDecay ^ s := by
      rw [pow_add, pow_add]
      ring
    _ = (2 : ℝ) ^ J * quarterDecay ^ (J - i - j) := by rw [hs]

/-- One coloured-KST rectangle block is controlled by the corresponding
summand of the explicit dyadic majorant. -/
theorem rectangleBlock_le_majorant {C T M N : ℝ} {J i j : ℕ}
    (hC : 0 ≤ C) (hij : i + j ≤ J)
    (hT : T ≤ (((2 : ℕ) ^ J : ℕ) : ℝ) /
      ((((2 : ℕ) ^ i : ℕ) : ℝ) * (((2 : ℕ) ^ j : ℕ) : ℝ)))
    (hT0 : 0 ≤ T)
    (hM : M ≤ 2 * C * (2 : ℝ) ^ i * (((i + 1 : ℕ) : ℝ)⁻¹))
    (hM0 : 0 ≤ M)
    (hN : N ≤ 2 * C * (2 : ℝ) ^ j * (((j + 1 : ℕ) : ℝ)⁻¹))
    (hN0 : 0 ≤ N) :
    2 * threeQuarterRoot T * M * N ≤
      8 * C ^ 2 * (2 : ℝ) ^ J * quarterDecay ^ (J - i - j) *
        (((i + 1 : ℕ) : ℝ)⁻¹) * (((j + 1 : ℕ) : ℝ)⁻¹) := by
  have hratio0 : 0 ≤ (((2 : ℕ) ^ J : ℕ) : ℝ) /
      ((((2 : ℕ) ^ i : ℕ) : ℝ) * (((2 : ℕ) ^ j : ℕ) : ℝ)) := by positivity
  have htq : threeQuarterRoot T ≤
      threeQuarterRoot ((2 : ℝ) ^ (J - i - j)) := by
    rw [← cast_two_pow_div_eq J i j hij]
    exact threeQuarterRoot_mono hT0 hT
  have hMi0 : 0 ≤ 2 * C * (2 : ℝ) ^ i * (((i + 1 : ℕ) : ℝ)⁻¹) := by
    positivity
  have hNj0 : 0 ≤ 2 * C * (2 : ℝ) ^ j * (((j + 1 : ℕ) : ℝ)⁻¹) := by
    positivity
  calc
    2 * threeQuarterRoot T * M * N ≤
        2 * threeQuarterRoot ((2 : ℝ) ^ (J - i - j)) * M * N := by
      apply mul_le_mul_of_nonneg_right _ hN0
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left htq (by norm_num)) hM0
    _ ≤ 2 * threeQuarterRoot ((2 : ℝ) ^ (J - i - j)) *
          (2 * C * (2 : ℝ) ^ i * (((i + 1 : ℕ) : ℝ)⁻¹)) * N := by
      apply mul_le_mul_of_nonneg_right _ hN0
      apply mul_le_mul_of_nonneg_left hM
      exact mul_nonneg (by norm_num) (threeQuarterRoot_nonneg _)
    _ ≤
        2 * threeQuarterRoot ((2 : ℝ) ^ (J - i - j)) *
          (2 * C * (2 : ℝ) ^ i * (((i + 1 : ℕ) : ℝ)⁻¹)) *
          (2 * C * (2 : ℝ) ^ j * (((j + 1 : ℕ) : ℝ)⁻¹)) := by
      apply mul_le_mul_of_nonneg_left hN
      exact mul_nonneg
        (mul_nonneg (by norm_num) (threeQuarterRoot_nonneg _)) hMi0
    _ = 8 * C ^ 2 *
          (threeQuarterRoot ((2 : ℝ) ^ (J - i - j)) *
            (2 : ℝ) ^ i * (2 : ℝ) ^ j) *
          (((i + 1 : ℕ) : ℝ)⁻¹) * (((j + 1 : ℕ) : ℝ)⁻¹) := by ring
    _ = 8 * C ^ 2 * (2 : ℝ) ^ J * quarterDecay ^ (J - i - j) *
          (((i + 1 : ℕ) : ℝ)⁻¹) * (((j + 1 : ℕ) : ℝ)⁻¹) := by
      rw [threeQuarterRoot_two_pow_mul J i j hij]
      ring

/-- The actual candidate-core rectangle contribution, written in the same
slack coordinates as `dyadicRectangleMajorant`. -/
def dyadicCandidateRectangleSum (J : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (J + 1),
    ∑ k ∈ Finset.range (J + 1 - 2 * i),
      2 * threeQuarterRoot
          ((blockCoreCandidates (2 ^ J) i (rightIndex J i k)).card : ℝ) *
        ((dyadicPrimeBlock i).card : ℝ) *
          ((dyadicPrimeBlock (rightIndex J i k)).card : ℝ)

lemma dyadicCandidateRectangleSum_nonneg (J : ℕ) :
    0 ≤ dyadicCandidateRectangleSum J := by
  unfold dyadicCandidateRectangleSum
  apply Finset.sum_nonneg
  intro i hi
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) (threeQuarterRoot_nonneg _))
      (Nat.cast_nonneg _)) (Nat.cast_nonneg _)

/-- Unconditional pointwise estimate for the actual arithmetic block sum.
All analytic constants have been discharged using the global prime-block
bound; the result has no local estimation hypotheses. -/
theorem exists_forall_dyadicCandidateRectangleSum_le_rectangleTerm :
    ∃ K : ℝ, 0 < K ∧ ∀ J : ℕ,
      dyadicCandidateRectangleSum J ≤ K * RectangleTerm.rectangleTerm J := by
  obtain ⟨C, hC, hprime⟩ := exists_forall_dyadicPrimeBlock_card_le
  refine ⟨8 * C ^ 2 * 49, by positivity, fun J ↦ ?_⟩
  have hsum : dyadicCandidateRectangleSum J ≤
      8 * C ^ 2 * dyadicRectangleMajorant J := by
    unfold dyadicCandidateRectangleSum dyadicRectangleMajorant
    have hpoint :
        (∑ i ∈ Finset.range (J + 1),
          ∑ k ∈ Finset.range (J + 1 - 2 * i),
            2 * threeQuarterRoot
                ((blockCoreCandidates (2 ^ J) i (rightIndex J i k)).card : ℝ) *
              ((dyadicPrimeBlock i).card : ℝ) *
                ((dyadicPrimeBlock (rightIndex J i k)).card : ℝ)) ≤
          ∑ i ∈ Finset.range (J + 1),
            ∑ k ∈ Finset.range (J + 1 - 2 * i),
              8 * C ^ 2 * (2 : ℝ) ^ J * quarterDecay ^ k *
                (((i + 1 : ℕ) : ℝ)⁻¹) *
                  (((rightIndex J i k + 1 : ℕ) : ℝ)⁻¹) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro k hk
      have hk' := Finset.mem_range.mp hk
      have hidx := rightIndex_constraints (J := J) (i := i) (k := k) hk'
      have hcardNat := blockCoreCandidates_card_le_div
        (2 ^ J) i (rightIndex J i k)
      have hT : ((blockCoreCandidates (2 ^ J) i
          (rightIndex J i k)).card : ℝ) ≤
          (((2 : ℕ) ^ J : ℕ) : ℝ) /
            ((((2 : ℕ) ^ i : ℕ) : ℝ) *
              (((2 : ℕ) ^ (rightIndex J i k) : ℕ) : ℝ)) := by
        calc
          ((blockCoreCandidates (2 ^ J) i
              (rightIndex J i k)).card : ℝ) ≤
              ((2 ^ J / (2 ^ i * 2 ^ rightIndex J i k) : ℕ) : ℝ) := by
            exact_mod_cast hcardNat
          _ ≤ (((2 : ℕ) ^ J : ℕ) : ℝ) /
              ((2 ^ i * 2 ^ rightIndex J i k : ℕ) : ℝ) := Nat.cast_div_le
          _ = (((2 : ℕ) ^ J : ℕ) : ℝ) /
              ((((2 : ℕ) ^ i : ℕ) : ℝ) *
                (((2 : ℕ) ^ (rightIndex J i k) : ℕ) : ℝ)) := by push_cast; rfl
      have hb := rectangleBlock_le_majorant (C := C)
        (T := ((blockCoreCandidates (2 ^ J) i
          (rightIndex J i k)).card : ℝ))
        (M := ((dyadicPrimeBlock i).card : ℝ))
        (N := ((dyadicPrimeBlock (rightIndex J i k)).card : ℝ))
        hC.le hidx.2 hT (Nat.cast_nonneg _) (hprime i) (Nat.cast_nonneg _)
        (hprime (rightIndex J i k)) (Nat.cast_nonneg _)
      have hslack : J - i - rightIndex J i k = k := by
        unfold rightIndex
        omega
      simpa [hslack] using hb
    calc
      (∑ i ∈ Finset.range (J + 1),
          ∑ k ∈ Finset.range (J + 1 - 2 * i),
            2 * threeQuarterRoot
                ((blockCoreCandidates (2 ^ J) i (rightIndex J i k)).card : ℝ) *
              ((dyadicPrimeBlock i).card : ℝ) *
                ((dyadicPrimeBlock (rightIndex J i k)).card : ℝ)) ≤
          ∑ i ∈ Finset.range (J + 1),
            ∑ k ∈ Finset.range (J + 1 - 2 * i),
              8 * C ^ 2 * (2 : ℝ) ^ J * quarterDecay ^ k *
                (((i + 1 : ℕ) : ℝ)⁻¹) *
                  (((rightIndex J i k + 1 : ℕ) : ℝ)⁻¹) := hpoint
      _ = 8 * C ^ 2 * ((2 : ℝ) ^ J *
          ∑ i ∈ Finset.range (J + 1),
            ∑ k ∈ Finset.range (J + 1 - 2 * i),
              quarterDecay ^ k * (((i + 1 : ℕ) : ℝ)⁻¹) *
                (((rightIndex J i k + 1 : ℕ) : ℝ)⁻¹)) := by
        calc
          (∑ i ∈ Finset.range (J + 1),
              ∑ k ∈ Finset.range (J + 1 - 2 * i),
                8 * C ^ 2 * (2 : ℝ) ^ J * quarterDecay ^ k *
                  (((i + 1 : ℕ) : ℝ)⁻¹) *
                    (((rightIndex J i k + 1 : ℕ) : ℝ)⁻¹)) =
              ∑ i ∈ Finset.range (J + 1),
                ∑ k ∈ Finset.range (J + 1 - 2 * i),
                  (8 * C ^ 2 * (2 : ℝ) ^ J) *
                    (quarterDecay ^ k * (((i + 1 : ℕ) : ℝ)⁻¹) *
                      (((rightIndex J i k + 1 : ℕ) : ℝ)⁻¹)) := by
            apply Finset.sum_congr rfl
            intro i hi
            apply Finset.sum_congr rfl
            intro k hk
            ring
          _ = (8 * C ^ 2 * (2 : ℝ) ^ J) *
              (∑ i ∈ Finset.range (J + 1),
                ∑ k ∈ Finset.range (J + 1 - 2 * i),
                  quarterDecay ^ k * (((i + 1 : ℕ) : ℝ)⁻¹) *
                    (((rightIndex J i k + 1 : ℕ) : ℝ)⁻¹)) := by
            simp_rw [Finset.mul_sum]
          _ = _ := by ring
  calc
    dyadicCandidateRectangleSum J ≤
        8 * C ^ 2 * dyadicRectangleMajorant J := hsum
    _ ≤ 8 * C ^ 2 * (49 * RectangleTerm.rectangleTerm J) := by
      exact mul_le_mul_of_nonneg_left
        (dyadicRectangleMajorant_le_rectangleTerm J) (by positivity)
    _ = (8 * C ^ 2 * 49) * RectangleTerm.rectangleTerm J := by ring

/-- The candidate-core rectangle contribution has the target order along
dyadic ambient sizes. -/
theorem dyadicCandidateRectangleSum_isBigO_dyadicScale :
    dyadicCandidateRectangleSum =O[atTop]
      (fun J : ℕ ↦ scale (2 ^ J)) := by
  obtain ⟨K, hK, hbound⟩ :=
    exists_forall_dyadicCandidateRectangleSum_le_rectangleTerm
  have hrect : dyadicCandidateRectangleSum =O[atTop]
      RectangleTerm.rectangleTerm := by
    apply IsBigO.of_bound K
    filter_upwards with J
    rw [Real.norm_of_nonneg (dyadicCandidateRectangleSum_nonneg J),
      Real.norm_of_nonneg (RectangleTerm.rectangleTerm_nonneg J)]
    exact hbound J
  exact hrect.trans RectangleTerm.rectangleTerm_isBigO_dyadicScale

/-! ## Identification with the universal block term -/

/-- Canonical triangular pairs whose product scale does not exceed `2^J`. -/
def activeTriangularIndices (J : ℕ) : Finset (ℕ × ℕ) :=
  (triangularBlockIndices (2 ^ J)).filter fun ij ↦ ij.1 + ij.2 ≤ J

/-- The same finite index set in `(left index, slack)` coordinates. -/
def rectangleSlackIndices (J : ℕ) : Finset (Σ _i : ℕ, ℕ) :=
  (Finset.range (J + 1)).sigma fun i ↦ Finset.range (J + 1 - 2 * i)

private lemma candidate_indices_sum_le {J i j : ℕ}
    (hne : (blockCoreCandidates (2 ^ J) i j).Nonempty) : i + j ≤ J := by
  obtain ⟨c, hc⟩ := hne
  have hs := mem_blockCoreCandidates.mp hc
  have hpow : 2 ^ (i + j) ≤ 2 ^ J := by
    rw [pow_add]
    calc
      2 ^ i * 2 ^ j = 1 * (2 ^ i * 2 ^ j) := by simp
      _ ≤ c * (2 ^ i * 2 ^ j) := Nat.mul_le_mul_right _ hs.1
      _ = c * 2 ^ i * 2 ^ j := by ring
      _ ≤ 2 ^ J := hs.2.2.2.2.1
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < (2 : ℕ))).mp hpow

private lemma candidate_eq_empty_of_sum_gt {J i j : ℕ} (hij : J < i + j) :
    blockCoreCandidates (2 ^ J) i j = ∅ := by
  apply Finset.not_nonempty_iff_eq_empty.mp
  intro hne
  exact (not_le_of_gt hij) (candidate_indices_sum_le hne)

private lemma sum_triangle_eq_sum_active (J : ℕ) :
    (∑ ij ∈ triangularBlockIndices (2 ^ J),
      2 * threeQuarterRoot
          ((blockCoreCandidates (2 ^ J) ij.1 ij.2).card : ℝ) *
        ((dyadicPrimeBlock ij.1).card : ℝ) *
          ((dyadicPrimeBlock ij.2).card : ℝ)) =
      ∑ ij ∈ activeTriangularIndices J,
        2 * threeQuarterRoot
            ((blockCoreCandidates (2 ^ J) ij.1 ij.2).card : ℝ) *
          ((dyadicPrimeBlock ij.1).card : ℝ) *
            ((dyadicPrimeBlock ij.2).card : ℝ) := by
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro ij hij hnot
  have hsum : J < ij.1 + ij.2 := by
    by_contra h
    apply hnot
    exact Finset.mem_filter.mpr ⟨hij, by omega⟩
  rw [candidate_eq_empty_of_sum_gt hsum]
  simp [threeQuarterRoot]

/-- The finite reindexing `(i,j) ↔ (i,J-i-j)` between the active triangle
and the slack-coordinate sum. -/
private lemma sum_active_eq_sum_slack (J : ℕ) :
    (∑ ij ∈ activeTriangularIndices J,
      2 * threeQuarterRoot
          ((blockCoreCandidates (2 ^ J) ij.1 ij.2).card : ℝ) *
        ((dyadicPrimeBlock ij.1).card : ℝ) *
          ((dyadicPrimeBlock ij.2).card : ℝ)) =
      ∑ z ∈ rectangleSlackIndices J,
        2 * threeQuarterRoot
            ((blockCoreCandidates (2 ^ J) z.1
              (rightIndex J z.1 z.2)).card : ℝ) *
          ((dyadicPrimeBlock z.1).card : ℝ) *
            ((dyadicPrimeBlock (rightIndex J z.1 z.2)).card : ℝ) := by
  classical
  apply Finset.sum_bij'
      (fun ij _ ↦ (⟨ij.1, J - ij.1 - ij.2⟩ : Σ _i : ℕ, ℕ))
      (fun z _ ↦ (z.1, rightIndex J z.1 z.2))
  · intro ij hij
    have ha := Finset.mem_filter.mp hij
    have ht := mem_triangularBlockIndices.mp ha.1
    simp only [rectangleSlackIndices, Finset.mem_sigma, Finset.mem_range]
    exact ⟨by simpa [Nat.log_pow (by norm_num : 1 < (2 : ℕ))] using ht.1,
      by omega⟩
  · intro z hz
    have hz' := Finset.mem_sigma.mp hz
    have hk := Finset.mem_range.mp hz'.2
    have hc := rightIndex_constraints (J := J) (i := z.1) (k := z.2) hk
    apply Finset.mem_filter.mpr
    constructor
    · apply mem_triangularBlockIndices.mpr
      rw [Nat.log_pow (by norm_num : 1 < (2 : ℕ))]
      exact ⟨Finset.mem_range.mp hz'.1, by omega, hc.1⟩
    · exact hc.2
  · intro ij hij
    have ha := Finset.mem_filter.mp hij
    have hsum := ha.2
    apply Prod.ext
    · rfl
    · simp [rightIndex]
      omega
  · intro z hz
    have hz' := Finset.mem_sigma.mp hz
    have hk := Finset.mem_range.mp hz'.2
    rcases z with ⟨i, k⟩
    change k < J + 1 - 2 * i at hk
    apply Sigma.ext (by rfl)
    have hkJi : k ≤ J - i := by omega
    apply heq_of_eq
    unfold rightIndex
    exact tsub_tsub_cancel_of_le hkJi
  · intro ij hij
    have ha := Finset.mem_filter.mp hij
    have hrecover : rightIndex J ij.1 (J - ij.1 - ij.2) = ij.2 := by
      unfold rightIndex
      omega
    simp only [hrecover]

/-- At powers of two, the universal rectangle term is exactly the explicit
candidate-core sum estimated above. -/
theorem universalRectangleTerm_two_pow_eq (J : ℕ) :
    universalRectangleTerm (2 ^ J) = dyadicCandidateRectangleSum J := by
  rw [universalRectangleTerm, sum_triangle_eq_sum_active,
    sum_active_eq_sum_slack]
  unfold dyadicCandidateRectangleSum rectangleSlackIndices
  rw [Finset.sum_sigma]

/-- An unconditional pointwise dyadic bound in the exact form consumed by
the upper-bound assembly. -/
theorem exists_forall_universalRectangleTerm_two_pow_le_rectangleTerm :
    ∃ K : ℝ, 0 < K ∧ ∀ J : ℕ,
      universalRectangleTerm (2 ^ J) ≤
        K * RectangleTerm.rectangleTerm J := by
  obtain ⟨K, hK, h⟩ :=
    exists_forall_dyadicCandidateRectangleSum_le_rectangleTerm
  exact ⟨K, hK, fun J ↦ by rw [universalRectangleTerm_two_pow_eq]; exact h J⟩

/-- The actual universal `S₁` contribution has the required order at all
natural arguments. -/
theorem universalRectangleTerm_isBigO_scale :
    universalRectangleTerm =O[atTop] scale := by
  obtain ⟨K, hK, hdyadicPoint⟩ :=
    exists_forall_universalRectangleTerm_two_pow_le_rectangleTerm
  apply isBigO_of_monotone_dyadic_bound (C := 8 * K)
    monotone_universalRectangleTerm (mul_pos (by norm_num) hK)
    (Eventually.of_forall universalRectangleTerm_nonneg)
  filter_upwards [RectangleTerm.eventually_rectangleTerm_le_scale] with J hrect
  calc
    universalRectangleTerm (2 ^ J) ≤
        K * RectangleTerm.rectangleTerm J := hdyadicPoint J
    _ ≤ K * (8 * scale (2 ^ J)) :=
      mul_le_mul_of_nonneg_left hrect hK.le
    _ = (8 * K) * scale (2 ^ J) := by ring

end

end RectangleBridge
end Erdos888
