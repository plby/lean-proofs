import ErdosProblems.Erdos888.PrimeEstimates
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic

/-!
# Smooth squarefree cores for Erdős Problem 888

This module isolates the Rankin-trick estimate used for the `S₃` term.  The
set `smoothCoreSet n X` consists of the squarefree positive integers `c`
which satisfy `c X² ≤ n` and whose prime factors are all below `2X`.

The main algebraic result is `T0_rankin`: with exponent `3/4`, the cardinality
of this set is bounded by the Rankin scale times the finite Euler product over
primes below `2X`.  Everything in this file is finite; in particular no
convergence or infinite Euler-product statement is hidden in the definition.
-/

namespace Erdos888

open scoped BigOperators

/-- The smooth squarefree cores occurring after the `Y`-sum in the `S₃`
estimate.  Writing the size condition as `c * X ^ 2 ≤ n` avoids all floor
rounding. -/
def smoothCoreSet (n X : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n).filter fun c ↦
    Squarefree c ∧ c * X ^ 2 ≤ n ∧ ∀ p ∈ c.primeFactors, p < 2 * X

/-- The counting function denoted `T₀(X)` in the paper (with the ambient
parameter `n` made explicit). -/
def T0 (n X : ℕ) : ℕ :=
  (smoothCoreSet n X).card

theorem mem_smoothCoreSet {n X c : ℕ} :
    c ∈ smoothCoreSet n X ↔
      1 ≤ c ∧ c ≤ n ∧ Squarefree c ∧ c * X ^ 2 ≤ n ∧
        ∀ p ∈ c.primeFactors, p < 2 * X := by
  simp [smoothCoreSet, and_assoc]

theorem smoothCoreSet_pos {n X c : ℕ} (hc : c ∈ smoothCoreSet n X) :
    0 < c := by
  exact (mem_smoothCoreSet.mp hc).1

theorem smoothCoreSet_squarefree {n X c : ℕ}
    (hc : c ∈ smoothCoreSet n X) : Squarefree c :=
  (mem_smoothCoreSet.mp hc).2.2.1

theorem smoothCoreSet_size {n X c : ℕ} (hc : c ∈ smoothCoreSet n X) :
    c * X ^ 2 ≤ n :=
  (mem_smoothCoreSet.mp hc).2.2.2.1

theorem smoothCoreSet_primeFactor_lt {n X c p : ℕ}
    (hc : c ∈ smoothCoreSet n X) (hp : p ∈ c.primeFactors) :
    p < 2 * X :=
  (mem_smoothCoreSet.mp hc).2.2.2.2 p hp

/-- The finite Euler product which occurs in Rankin's trick. -/
noncomputable def rankinMoment (X : ℕ) : ℝ :=
  ∏ p ∈ (2 * X).primesBelow, (1 + (p : ℝ) ^ (-(3 / 4 : ℝ)))

/-- The Rankin scale `(n / X²)^(3/4)`. -/
noncomputable def rankinScale (n X : ℕ) : ℝ :=
  ((n : ℝ) / (X : ℝ) ^ 2) ^ (3 / 4 : ℝ)

/-- Logarithm of the Rankin Euler-product majorant. -/
noncomputable def rankinPrimeSum (X : ℕ) : ℝ :=
  ∑ p ∈ (2 * X).primesBelow, (p : ℝ) ^ (-(3 / 4 : ℝ))

/-- The finite Euler product is bounded by the exponential of its linear
prime sum, using `1 + u ≤ exp u` term by term. -/
theorem rankinMoment_le_exp_primeSum (X : ℕ) :
    rankinMoment X ≤ Real.exp (rankinPrimeSum X) := by
  classical
  rw [rankinMoment, rankinPrimeSum, Real.exp_sum]
  apply Finset.prod_le_prod
  · intro p hp
    positivity
  · intro p hp
    simpa [add_comm] using
      Real.add_one_le_exp ((p : ℝ) ^ (-(3 / 4 : ℝ)))

/-- Convenient consequence of a supplied upper bound for the prime sum. -/
theorem rankinMoment_le_exp_of_primeSum_le {X : ℕ} {L : ℝ}
    (h : rankinPrimeSum X ≤ L) : rankinMoment X ≤ Real.exp L :=
  (rankinMoment_le_exp_primeSum X).trans (Real.exp_monotone h)

/-- The prime sum is monotone in the smoothness parameter. -/
theorem rankinPrimeSum_mono {X Y : ℕ} (hXY : X ≤ Y) :
    rankinPrimeSum X ≤ rankinPrimeSum Y := by
  classical
  unfold rankinPrimeSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [Nat.mem_primesBelow] at hp ⊢
    exact ⟨hp.1.trans_le (Nat.mul_le_mul_left 2 hXY), hp.2⟩
  · intro p hp hnot
    positivity

/-- Comparison with the inclusive prime sum from `PrimeEstimates`. -/
theorem rankinPrimeSum_le_primeThreeQuarterSum (X : ℕ) :
    rankinPrimeSum X ≤ primeThreeQuarterSum (2 * X) := by
  classical
  unfold rankinPrimeSum primeThreeQuarterSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [Nat.mem_primesBelow] at hp
    rw [mem_primesUpTo]
    exact ⟨hp.2, hp.1.le⟩
  · intro p hp hnot
    positivity

theorem primeThreeQuarterSum_mono {m n : ℕ} (hmn : m ≤ n) :
    primeThreeQuarterSum m ≤ primeThreeQuarterSum n := by
  classical
  unfold primeThreeQuarterSum
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [mem_primesUpTo] at hp ⊢
    exact ⟨hp.1, hp.2.trans hmn⟩
  · intro p hp hnot
    positivity

/-- Natural cutoff corresponding to `(log n)^4`. -/
noncomputable def logFourthThreshold (n : ℕ) : ℕ :=
  ⌊(Real.log (n : ℝ)) ^ 4⌋₊

theorem logFourthThreshold_tendsto_atTop :
    Filter.Tendsto logFourthThreshold Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro B
  have hlog := (Real.tendsto_log_atTop.comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop (max 1 (B : ℝ))
  filter_upwards [hlog] with n hn
  apply Nat.le_floor
  have hB : (B : ℝ) ≤ Real.log (n : ℝ) :=
    (le_max_right (1 : ℝ) B).trans hn
  have hlogOne : 1 ≤ Real.log (n : ℝ) :=
    (le_max_left (1 : ℝ) B).trans hn
  calc
    (B : ℝ) ≤ Real.log (n : ℝ) := hB
    _ ≤ (Real.log (n : ℝ)) ^ 2 := by
      nlinarith [mul_nonneg (show 0 ≤ Real.log (n : ℝ) by linarith)
        (sub_nonneg.mpr hlogOne)]
    _ ≤ (Real.log (n : ℝ)) ^ 4 := by
      have hsqOne : 1 ≤ (Real.log (n : ℝ)) ^ 2 := one_le_pow₀ hlogOne
      nlinarith [mul_nonneg (sq_nonneg (Real.log (n : ℝ)))
        (sub_nonneg.mpr hsqOne)]

theorem lambda_logFourthThreshold_tendsto_atTop :
    Filter.Tendsto (fun n : ℕ ↦ lambda (logFourthThreshold n : ℝ))
      Filter.atTop Filter.atTop := by
  have hcast : Filter.Tendsto (fun n : ℕ ↦ (logFourthThreshold n : ℝ))
      Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop.comp logFourthThreshold_tendsto_atTop
  have hmul : Filter.Tendsto
      (fun n : ℕ ↦ Real.exp 1 * (logFourthThreshold n : ℝ))
      Filter.atTop Filter.atTop :=
    Filter.Tendsto.const_mul_atTop (Real.exp_pos 1) hcast
  exact Real.tendsto_log_atTop.comp hmul

/-- The fourth-root of the cutoff is at most `log n` once the logarithm is
nonnegative. -/
theorem logFourthThreshold_rpow_le_log {n : ℕ}
    (hn : 1 ≤ n) :
    (logFourthThreshold n : ℝ) ^ (1 / 4 : ℝ) ≤ Real.log (n : ℝ) := by
  have hlog : 0 ≤ Real.log (n : ℝ) := by
    exact Real.log_nonneg (by exact_mod_cast hn)
  have hfloor : (logFourthThreshold n : ℝ) ≤ (Real.log (n : ℝ)) ^ 4 := by
    exact Nat.floor_le (pow_nonneg hlog 4)
  calc
    (logFourthThreshold n : ℝ) ^ (1 / 4 : ℝ) ≤
        ((Real.log (n : ℝ)) ^ 4) ^ (1 / 4 : ℝ) :=
      Real.rpow_le_rpow (by positivity) hfloor (by norm_num)
    _ = Real.log (n : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hlog]
      norm_num

/-- Uniform `n^(1/16)` bound for the Rankin Euler product throughout the
small range `X ≤ (log n)^4`. -/
theorem eventually_rankinMoment_le_sixteenth :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ X : ℕ,
      0 < X → X ≤ logFourthThreshold n →
        rankinMoment X ≤ (n : ℝ) ^ (1 / 16 : ℝ) := by
  obtain ⟨C, hC⟩ := primeThreeQuarterSum_isBigO_scale.bound
  let D : ℝ := max 1 C
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_left 1 C)
  have hdouble : Filter.Tendsto (fun n : ℕ ↦ 2 * logFourthThreshold n)
      Filter.atTop Filter.atTop := by
    refine Filter.tendsto_atTop.2 fun B ↦ ?_
    filter_upwards [logFourthThreshold_tendsto_atTop.eventually_ge_atTop B]
      with n hn
    omega
  have hbound := hdouble.eventually hC
  have hlamLarge := lambda_logFourthThreshold_tendsto_atTop.eventually_ge_atTop (32 * D)
  have hthresholdPos := logFourthThreshold_tendsto_atTop.eventually_gt_atTop 0
  have hlogPos := (Real.tendsto_log_atTop.comp
    tendsto_natCast_atTop_atTop).eventually_gt_atTop 0
  filter_upwards [hbound, hlamLarge, hthresholdPos, hlogPos,
    Filter.eventually_ge_atTop 1] with n hbound hlamLarge hLpos hlogPos hn X hX hXL
  let L := logFourthThreshold n
  have hXL' : X ≤ L := by simpa [L] using hXL
  have hL : 0 < L := hLpos
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have h2L : 0 < 2 * L := by positivity
  have hlamL : 0 < lambda (L : ℝ) := lambda_pos (by exact_mod_cast hL)
  have hlam2L : 0 < lambda ((2 * L : ℕ) : ℝ) :=
    lambda_pos (by exact_mod_cast h2L)
  have hsumNonneg : 0 ≤ primeThreeQuarterSum (2 * L) := by
    unfold primeThreeQuarterSum
    positivity
  have hscaleNonneg :
      0 ≤ ((2 * L : ℕ) : ℝ) ^ (1 / 4 : ℝ) /
        lambda ((2 * L : ℕ) : ℝ) := by positivity
  have hQbound :
      primeThreeQuarterSum (2 * L) ≤
        D * (((2 * L : ℕ) : ℝ) ^ (1 / 4 : ℝ) /
          lambda ((2 * L : ℕ) : ℝ)) := by
    have hb : ‖primeThreeQuarterSum (2 * L)‖ ≤
        C * ‖((2 * L : ℕ) : ℝ) ^ (1 / 4 : ℝ) /
          lambda ((2 * L : ℕ) : ℝ)‖ := by
      simpa [L] using hbound
    rw [Real.norm_of_nonneg hsumNonneg, Real.norm_of_nonneg hscaleNonneg] at hb
    exact hb.trans <| mul_le_mul_of_nonneg_right (le_max_right 1 C) hscaleNonneg
  have hlamMono : lambda (L : ℝ) ≤ lambda ((2 * L : ℕ) : ℝ) := by
    apply lambda_mono hLr
    exact_mod_cast (show L ≤ 2 * L by omega)
  have hroot : ((2 * L : ℕ) : ℝ) ^ (1 / 4 : ℝ) ≤
      2 * Real.log (n : ℝ) := by
    have hfloor : (L : ℝ) ≤ (Real.log (n : ℝ)) ^ 4 := by
      exact Nat.floor_le (pow_nonneg hlogPos.le 4)
    have hbase : ((2 * L : ℕ) : ℝ) ≤
        (2 * Real.log (n : ℝ)) ^ 4 := by
      norm_num at ⊢
      nlinarith [sq_nonneg (Real.log (n : ℝ)),
        mul_nonneg (sq_nonneg (Real.log (n : ℝ)))
          (sq_nonneg (Real.log (n : ℝ)))]
    calc
      ((2 * L : ℕ) : ℝ) ^ (1 / 4 : ℝ) ≤
          ((2 * Real.log (n : ℝ)) ^ 4) ^ (1 / 4 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hbase (by norm_num)
      _ = 2 * Real.log (n : ℝ) := by
        have hnonneg : 0 ≤ 2 * Real.log (n : ℝ) := by positivity
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnonneg]
        norm_num
  have hscale :
      ((2 * L : ℕ) : ℝ) ^ (1 / 4 : ℝ) /
          lambda ((2 * L : ℕ) : ℝ) ≤
        (2 * Real.log (n : ℝ)) / lambda (L : ℝ) := by
    exact div_le_div₀ (by positivity) hroot hlamL hlamMono
  have hcoef : 2 * D / lambda (L : ℝ) ≤ 1 / 16 := by
    rw [div_le_iff₀ hlamL]
    linarith
  have hQlog : primeThreeQuarterSum (2 * L) ≤
      Real.log (n : ℝ) / 16 := by
    calc
      primeThreeQuarterSum (2 * L) ≤
          D * (((2 * L : ℕ) : ℝ) ^ (1 / 4 : ℝ) /
            lambda ((2 * L : ℕ) : ℝ)) := hQbound
      _ ≤ D * ((2 * Real.log (n : ℝ)) / lambda (L : ℝ)) :=
        mul_le_mul_of_nonneg_left hscale hDpos.le
      _ = (2 * D / lambda (L : ℝ)) * Real.log (n : ℝ) := by ring
      _ ≤ (1 / 16 : ℝ) * Real.log (n : ℝ) :=
        mul_le_mul_of_nonneg_right hcoef hlogPos.le
      _ = Real.log (n : ℝ) / 16 := by ring
  have hSlog : rankinPrimeSum X ≤ Real.log (n : ℝ) / 16 :=
    (rankinPrimeSum_le_primeThreeQuarterSum X).trans <|
      (primeThreeQuarterSum_mono (Nat.mul_le_mul_left 2 hXL')).trans hQlog
  calc
    rankinMoment X ≤ Real.exp (rankinPrimeSum X) := rankinMoment_le_exp_primeSum X
    _ ≤ Real.exp (Real.log (n : ℝ) / 16) := Real.exp_monotone hSlog
    _ = (n : ℝ) ^ (1 / 16 : ℝ) := by
      rw [Real.rpow_def_of_pos (by exact_mod_cast (show 0 < n by omega))]
      congr 1 <;> ring

private theorem cast_prod_rpow (s : Finset ℕ) (a : ℝ) :
    ((∏ p ∈ s, p : ℕ) : ℝ) ^ a = ∏ p ∈ s, (p : ℝ) ^ a := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert p s hp ih =>
      calc
        ((∏ q ∈ insert p s, q : ℕ) : ℝ) ^ a =
            ((p : ℝ) * ((∏ q ∈ s, q : ℕ) : ℝ)) ^ a := by
              rw [Finset.prod_insert hp, Nat.cast_mul]
        _ = (p : ℝ) ^ a * ((∏ q ∈ s, q : ℕ) : ℝ) ^ a :=
          Real.mul_rpow (by positivity) (by positivity)
        _ = (p : ℝ) ^ a * ∏ q ∈ s, (q : ℝ) ^ a := by rw [ih]
        _ = ∏ q ∈ insert p s, (q : ℝ) ^ a := by
          rw [Finset.prod_insert hp]

private theorem primeFactors_injective_on_smoothCoreSet (n X : ℕ) :
    Set.InjOn Nat.primeFactors (smoothCoreSet n X : Set ℕ) := by
  intro c hc d hd hcd
  rw [← Nat.prod_primeFactors_of_squarefree (smoothCoreSet_squarefree hc),
    ← Nat.prod_primeFactors_of_squarefree (smoothCoreSet_squarefree hd), hcd]

/-- The weighted sum over smooth squarefree cores is at most the complete
Euler product over the allowed primes. -/
theorem weighted_smoothCoreSum_le_rankinMoment (n X : ℕ) :
    (∑ c ∈ smoothCoreSet n X, (c : ℝ) ^ (-(3 / 4 : ℝ))) ≤
      rankinMoment X := by
  classical
  let P : Finset ℕ := (2 * X).primesBelow
  have hinj : Set.InjOn Nat.primeFactors (smoothCoreSet n X : Set ℕ) :=
    primeFactors_injective_on_smoothCoreSet n X
  have hsub : (smoothCoreSet n X).image Nat.primeFactors ⊆ P.powerset := by
    intro s hs
    rcases Finset.mem_image.mp hs with ⟨c, hc, rfl⟩
    rw [Finset.mem_powerset]
    intro p hp
    rw [Nat.mem_primesBelow]
    exact ⟨smoothCoreSet_primeFactor_lt hc hp,
      Nat.prime_of_mem_primeFactors hp⟩
  calc
    (∑ c ∈ smoothCoreSet n X, (c : ℝ) ^ (-(3 / 4 : ℝ))) =
        ∑ c ∈ smoothCoreSet n X,
          ∏ p ∈ c.primeFactors, (p : ℝ) ^ (-(3 / 4 : ℝ)) := by
            apply Finset.sum_congr rfl
            intro c hc
            rw [← cast_prod_rpow]
            congr 1
            exact_mod_cast (Nat.prod_primeFactors_of_squarefree
              (smoothCoreSet_squarefree hc)).symm
    _ = ∑ s ∈ (smoothCoreSet n X).image Nat.primeFactors,
          ∏ p ∈ s, (p : ℝ) ^ (-(3 / 4 : ℝ)) := by
            symm
            exact Finset.sum_image hinj
    _ ≤ ∑ s ∈ P.powerset,
          ∏ p ∈ s, (p : ℝ) ^ (-(3 / 4 : ℝ)) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hsub
            intro s hs hnot
            positivity
    _ = rankinMoment X := by
      rw [← Finset.prod_one_add]
      rfl

private theorem one_le_rankin_term {n X c : ℕ} (hX : 0 < X)
    (hc : c ∈ smoothCoreSet n X) :
    1 ≤ rankinScale n X * (c : ℝ) ^ (-(3 / 4 : ℝ)) := by
  have hcpos : (0 : ℝ) < c := by exact_mod_cast smoothCoreSet_pos hc
  have hXpos : (0 : ℝ) < X := by exact_mod_cast hX
  have hsize : (c : ℝ) * (X : ℝ) ^ 2 ≤ n := by
    exact_mod_cast smoothCoreSet_size hc
  have hbase : 1 ≤ (n : ℝ) / ((X : ℝ) ^ 2 * c) := by
    rw [one_le_div₀]
    · nlinarith
    · positivity
  have hrpow :
      1 ≤ ((n : ℝ) / ((X : ℝ) ^ 2 * c)) ^ (3 / 4 : ℝ) :=
    Real.one_le_rpow hbase (by norm_num)
  calc
    1 ≤ ((n : ℝ) / ((X : ℝ) ^ 2 * c)) ^ (3 / 4 : ℝ) := hrpow
    _ = rankinScale n X * (c : ℝ) ^ (-(3 / 4 : ℝ)) := by
      rw [rankinScale, Real.div_rpow (by positivity) (by positivity),
        Real.div_rpow (by positivity) (by positivity),
        Real.mul_rpow (show 0 ≤ (X : ℝ) ^ 2 by positivity)
          (show 0 ≤ (c : ℝ) by positivity),
        Real.rpow_neg (le_of_lt hcpos)]
      ring

/-- Rankin's trick with exponent `3/4`, in the exact finite form used in the
smooth-core estimate. -/
theorem T0_rankin {n X : ℕ} (hX : 0 < X) :
    (T0 n X : ℝ) ≤ rankinScale n X * rankinMoment X := by
  classical
  calc
    (T0 n X : ℝ) = ∑ c ∈ smoothCoreSet n X, (1 : ℝ) := by
      simp [T0]
    _ ≤ ∑ c ∈ smoothCoreSet n X,
        rankinScale n X * (c : ℝ) ^ (-(3 / 4 : ℝ)) := by
      exact Finset.sum_le_sum fun c hc ↦ one_le_rankin_term hX hc
    _ = rankinScale n X *
        ∑ c ∈ smoothCoreSet n X, (c : ℝ) ^ (-(3 / 4 : ℝ)) := by
      rw [Finset.mul_sum]
    _ ≤ rankinScale n X * rankinMoment X := by
      have hscale : 0 ≤ rankinScale n X := by
        apply Real.rpow_nonneg
        positivity
      exact mul_le_mul_of_nonneg_left
        (weighted_smoothCoreSum_le_rankinMoment n X)
        hscale

/-- Rankin's inequality with the Euler product already replaced by an
exponential prime-sum estimate. -/
theorem T0_rankin_exp {n X : ℕ} (hX : 0 < X) :
    (T0 n X : ℝ) ≤ rankinScale n X * Real.exp (rankinPrimeSum X) :=
  (T0_rankin hX).trans <| mul_le_mul_of_nonneg_left
    (rankinMoment_le_exp_primeSum X) (by
      apply Real.rpow_nonneg
      positivity)

/-- The concrete `13/16` consequence used in the small-scale range: a
`n^(1/16)` bound for the Euler product combines with Rankin's exponent
`3/4` to give `n^(13/16) X^(-3/2)`. -/
theorem T0_le_thirteenSixteenths {n X : ℕ} (hX : 0 < X)
    (hmoment : rankinMoment X ≤ (n : ℝ) ^ (1 / 16 : ℝ)) :
    (T0 n X : ℝ) ≤
      (n : ℝ) ^ (13 / 16 : ℝ) * (X : ℝ) ^ (-(3 / 2 : ℝ)) := by
  by_cases hn0 : n = 0
  · subst n
    have hempty : smoothCoreSet 0 X = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro c hc
      have hcpos := smoothCoreSet_pos hc
      have hsize := smoothCoreSet_size hc
      nlinarith [pow_pos hX 2]
    simp [T0, hempty]
  have hn : 0 < n := Nat.pos_of_ne_zero hn0
  have hnonneg : 0 ≤ rankinScale n X := by
    apply Real.rpow_nonneg
    positivity
  refine (T0_rankin hX).trans <| (mul_le_mul_of_nonneg_left hmoment hnonneg).trans ?_
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  rw [rankinScale, Real.div_rpow (by positivity) (by positivity),
    show (13 / 16 : ℝ) = 3 / 4 + 1 / 16 by norm_num,
    Real.rpow_add (show (0 : ℝ) < n by exact_mod_cast hn) (3 / 4) (1 / 16)]
  have hpow : ((X : ℝ) ^ 2) ^ (3 / 4 : ℝ) =
      (X : ℝ) ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hXr)]
    norm_num
  rw [hpow, Real.rpow_neg (le_of_lt hXr)]
  simp only [div_eq_mul_inv]
  ring_nf
  exact le_rfl

/-- The trivial counting bound, useful in the large-`X` range. -/
theorem T0_le_div (n X : ℕ) (hX : 0 < X) : T0 n X ≤ n / X ^ 2 := by
  classical
  rw [T0]
  calc
    (smoothCoreSet n X).card ≤ (Finset.Icc 1 (n / X ^ 2)).card := by
      apply Finset.card_le_card
      intro c hc
      rw [Finset.mem_Icc]
      refine ⟨(mem_smoothCoreSet.mp hc).1, ?_⟩
      exact Nat.le_div_iff_mul_le (pow_pos hX 2) |>.2 <| by
        simpa [mul_comm] using smoothCoreSet_size hc
    _ ≤ n / X ^ 2 := by simp

/-! ## Bounds for the reduced `S₃` summand -/

/-- The contribution remaining after summing the `Y` variable, before the
outer sum over dyadic `X`. -/
noncomputable def smoothCoreTerm (n X : ℕ) : ℝ :=
  Real.sqrt (n : ℝ) *
    (Real.sqrt ((X : ℝ) * (T0 n X : ℝ)) / lambda (X : ℝ))

/-- Trivial large-scale estimate for one dyadic summand. -/
theorem smoothCoreTerm_le_large {n X : ℕ} (hX : 0 < X) :
    smoothCoreTerm n X ≤ (n : ℝ) / Real.sqrt (X : ℝ) := by
  have hTnat := T0_le_div n X hX
  have hTcast : (T0 n X : ℝ) ≤ (n : ℝ) / (X : ℝ) ^ 2 := by
    calc
      (T0 n X : ℝ) ≤ ((n / X ^ 2 : ℕ) : ℝ) := by exact_mod_cast hTnat
      _ ≤ (n : ℝ) / ((X ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
      _ = (n : ℝ) / (X : ℝ) ^ 2 := by norm_num
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hlam : 1 ≤ lambda (X : ℝ) := by
    rw [lambda_eq_one_add_log hXr.ne']
    have : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
    linarith
  have hsqrt :
      Real.sqrt ((X : ℝ) * (T0 n X : ℝ)) ≤
        Real.sqrt ((n : ℝ) / (X : ℝ)) := by
    apply Real.sqrt_le_sqrt
    calc
      (X : ℝ) * (T0 n X : ℝ) ≤
          (X : ℝ) * ((n : ℝ) / (X : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hTcast hXr.le
      _ = (n : ℝ) / (X : ℝ) := by field_simp
  unfold smoothCoreTerm
  calc
    Real.sqrt (n : ℝ) *
        (Real.sqrt ((X : ℝ) * (T0 n X : ℝ)) / lambda (X : ℝ)) ≤
      Real.sqrt (n : ℝ) * Real.sqrt ((X : ℝ) * (T0 n X : ℝ)) := by
        gcongr
        exact (div_le_iff₀ (lambda_pos (by exact_mod_cast hX))).2 <| by
          nlinarith [Real.sqrt_nonneg ((X : ℝ) * (T0 n X : ℝ))]
    _ ≤ Real.sqrt (n : ℝ) * Real.sqrt ((n : ℝ) / (X : ℝ)) := by
      gcongr
    _ = (n : ℝ) / Real.sqrt (X : ℝ) := by
      rw [Real.sqrt_div (by positivity)]
      calc
        Real.sqrt (n : ℝ) * (Real.sqrt (n : ℝ) / Real.sqrt (X : ℝ)) =
            (Real.sqrt (n : ℝ) * Real.sqrt (n : ℝ)) /
              Real.sqrt (X : ℝ) := by ring
        _ = (n : ℝ) / Real.sqrt (X : ℝ) := by
          rw [Real.mul_self_sqrt (by positivity)]

/-- Small-scale estimate for one dyadic summand, conditional only on the
uniform Euler-product bound supplied by the Rankin argument. -/
theorem smoothCoreTerm_le_small {n X : ℕ} (hn : 0 < n) (hX : 0 < X)
    (hmoment : rankinMoment X ≤ (n : ℝ) ^ (1 / 16 : ℝ)) :
    smoothCoreTerm n X ≤ (n : ℝ) ^ (29 / 32 : ℝ) := by
  have hT := T0_le_thirteenSixteenths hX hmoment
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hXr : (0 : ℝ) < X := by exact_mod_cast hX
  have hlam : 1 ≤ lambda (X : ℝ) := by
    rw [lambda_eq_one_add_log hXr.ne']
    have : 0 ≤ Real.log (X : ℝ) := Real.log_nonneg (by exact_mod_cast hX)
    linarith
  have hinside :
      (X : ℝ) * (T0 n X : ℝ) ≤
        (n : ℝ) ^ (13 / 16 : ℝ) * (X : ℝ) ^ (-(1 / 2 : ℝ)) := by
    calc
      (X : ℝ) * (T0 n X : ℝ) ≤
          (X : ℝ) * ((n : ℝ) ^ (13 / 16 : ℝ) *
            (X : ℝ) ^ (-(3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hT hXr.le
      _ = (n : ℝ) ^ (13 / 16 : ℝ) * (X : ℝ) ^ (-(1 / 2 : ℝ)) := by
        calc
          (X : ℝ) * ((n : ℝ) ^ (13 / 16 : ℝ) *
              (X : ℝ) ^ (-(3 / 2 : ℝ))) =
              (n : ℝ) ^ (13 / 16 : ℝ) *
                ((X : ℝ) ^ (1 : ℝ) * (X : ℝ) ^ (-(3 / 2 : ℝ))) := by
            norm_num [Real.rpow_one]
            ring
          _ = (n : ℝ) ^ (13 / 16 : ℝ) *
              (X : ℝ) ^ (1 + (-(3 / 2 : ℝ))) := by
            rw [Real.rpow_add hXr]
          _ = _ := by norm_num
  unfold smoothCoreTerm
  calc
    Real.sqrt (n : ℝ) *
        (Real.sqrt ((X : ℝ) * (T0 n X : ℝ)) / lambda (X : ℝ)) ≤
      Real.sqrt (n : ℝ) * Real.sqrt ((X : ℝ) * (T0 n X : ℝ)) := by
        gcongr
        exact (div_le_iff₀ (lambda_pos (by exact_mod_cast hX))).2 <| by
          nlinarith [Real.sqrt_nonneg ((X : ℝ) * (T0 n X : ℝ))]
    _ ≤ Real.sqrt (n : ℝ) *
        Real.sqrt ((n : ℝ) ^ (13 / 16 : ℝ) *
          (X : ℝ) ^ (-(1 / 2 : ℝ))) := by
      gcongr
    _ = (n : ℝ) ^ (29 / 32 : ℝ) * (X : ℝ) ^ (-(1 / 4 : ℝ)) := by
      simp only [Real.sqrt_eq_rpow]
      rw [Real.mul_rpow (by positivity) (by positivity),
        ← Real.rpow_mul (le_of_lt hXr),
        ← Real.rpow_mul (le_of_lt hnr)]
      norm_num
      calc
        (n : ℝ) ^ (1 / 2 : ℝ) *
            ((n : ℝ) ^ (13 / 32 : ℝ) * (X : ℝ) ^ (-(1 / 4 : ℝ))) =
            ((n : ℝ) ^ (1 / 2 : ℝ) * (n : ℝ) ^ (13 / 32 : ℝ)) *
              (X : ℝ) ^ (-(1 / 4 : ℝ)) := by ring
        _ = (n : ℝ) ^ ((1 / 2 : ℝ) + 13 / 32) *
              (X : ℝ) ^ (-(1 / 4 : ℝ)) := by rw [Real.rpow_add hnr]
        _ = _ := by norm_num
    _ ≤ (n : ℝ) ^ (29 / 32 : ℝ) := by
      have hXinvrpow : (X : ℝ) ^ (-(1 / 4 : ℝ)) ≤ 1 := by
        simpa only [Real.rpow_zero] using
          Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hX) (by norm_num : (-(1 / 4 : ℝ)) ≤ 0)
      exact mul_le_of_le_one_right (Real.rpow_nonneg (by positivity) _) hXinvrpow

theorem smoothCoreTerm_nonneg (n X : ℕ) : 0 ≤ smoothCoreTerm n X := by
  by_cases hX : X = 0
  · subst X
    simp [smoothCoreTerm, lambda]
  · unfold smoothCoreTerm
    exact mul_nonneg (Real.sqrt_nonneg _) <|
      div_nonneg (Real.sqrt_nonneg _) (lambda_pos (by exact_mod_cast (Nat.pos_of_ne_zero hX))).le

private theorem index_le_two_pow (i : ℕ) : i ≤ 2 ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
      cases i with
      | zero => norm_num
      | succ i =>
          rw [pow_succ]
          omega

private theorem sqrt_two_pow (i : ℕ) :
    Real.sqrt ((2 : ℝ) ^ i) = (Real.sqrt 2) ^ i := by
  induction i with
  | zero => simp
  | succ i ih =>
      rw [pow_succ, Real.sqrt_mul (by positivity), ih, pow_succ]

/-- A finite tail of inverse square roots of dyadic powers is controlled by
its first term.  The deliberately round constant `4` avoids carrying the
exact factor `(1 - 2⁻¹ᐟ²)⁻¹`. -/
private theorem invSqrtDyadicTail_le (k m : ℕ) :
    (∑ j ∈ Finset.range m,
      1 / Real.sqrt ((2 : ℝ) ^ (k + j))) ≤
      4 / Real.sqrt ((2 : ℝ) ^ k) := by
  let q : ℝ := (Real.sqrt 2)⁻¹
  have hsqrtPos : 0 < Real.sqrt (2 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hsqrtOne : 1 < Real.sqrt (2 : ℝ) := by
    have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
    nlinarith [Real.sqrt_nonneg (2 : ℝ)]
  have hq0 : 0 ≤ q := inv_nonneg.mpr hsqrtPos.le
  have hq1 : q < 1 := by
    dsimp [q]
    exact inv_lt_one_of_one_lt₀ hsqrtOne
  have hgeom : (∑ j ∈ Finset.range m, q ^ j) ≤ 4 := by
    have hlt := geom_sum_Ico_le_of_lt_one (m := 0) (n := m) hq0 hq1
    have hdenom : (1 - q)⁻¹ ≤ 4 := by
      rw [inv_le_iff_one_le_mul₀' (sub_pos.mpr hq1)]
      dsimp [q]
      have hsqrtLower : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
        have hsquare := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
        nlinarith [Real.sqrt_nonneg (2 : ℝ)]
      have hinv : (Real.sqrt 2)⁻¹ ≤ 3 / 4 := by
        rw [inv_le_iff_one_le_mul₀' hsqrtPos]
        nlinarith
      linarith
    have hdenom' : q ^ 0 / (1 - q) ≤ 4 := by
      simpa [div_eq_mul_inv] using hdenom
    simpa using hlt.trans hdenom'
  calc
    (∑ j ∈ Finset.range m,
        1 / Real.sqrt ((2 : ℝ) ^ (k + j))) =
        q ^ k * ∑ j ∈ Finset.range m, q ^ j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      rw [sqrt_two_pow, pow_add]
      dsimp [q]
      rw [inv_pow, inv_pow]
      field_simp
    _ ≤ q ^ k * 4 :=
      mul_le_mul_of_nonneg_left hgeom (pow_nonneg hq0 k)
    _ = 4 / Real.sqrt ((2 : ℝ) ^ k) := by
      rw [sqrt_two_pow]
      dsimp [q]
      rw [inv_pow]
      field_simp

/-- The reduced `S₃` contribution at the canonical base-two scales. -/
noncomputable def smoothCoreS3 (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (Nat.log 2 n + 1), smoothCoreTerm n (2 ^ i)

private theorem smoothCoreS3_small_le {n L : ℕ} (hn : 0 < n)
    (hmoment : ∀ X : ℕ, 0 < X → X ≤ L →
      rankinMoment X ≤ (n : ℝ) ^ (1 / 16 : ℝ)) :
    (∑ i ∈ (Finset.range (Nat.log 2 n + 1)).filter (fun i ↦ 2 ^ i ≤ L),
        smoothCoreTerm n (2 ^ i)) ≤
      (L + 1 : ℕ) * (n : ℝ) ^ (29 / 32 : ℝ) := by
  classical
  let s := (Finset.range (Nat.log 2 n + 1)).filter (fun i ↦ 2 ^ i ≤ L)
  have hsCard : s.card ≤ L + 1 := by
    have hsub : s ⊆ Finset.range (L + 1) := by
      intro i hi
      rw [Finset.mem_range]
      have hiL : 2 ^ i ≤ L := (Finset.mem_filter.mp hi).2
      exact (index_le_two_pow i).trans hiL |>.trans_lt (Nat.lt_succ_self L)
    simpa using Finset.card_le_card hsub
  have hterm : ∀ i ∈ s,
      smoothCoreTerm n (2 ^ i) ≤ (n : ℝ) ^ (29 / 32 : ℝ) := by
    intro i hi
    apply smoothCoreTerm_le_small hn (pow_pos (by norm_num) i)
    apply hmoment (2 ^ i) (pow_pos (by norm_num) i)
    exact (Finset.mem_filter.mp hi).2
  have hsum := Finset.sum_le_card_nsmul s
    (fun i ↦ smoothCoreTerm n (2 ^ i))
    ((n : ℝ) ^ (29 / 32 : ℝ)) hterm
  change (∑ i ∈ s, smoothCoreTerm n (2 ^ i)) ≤ _
  calc
    (∑ i ∈ s, smoothCoreTerm n (2 ^ i)) ≤
        (s.card : ℝ) * (n : ℝ) ^ (29 / 32 : ℝ) := by
      simpa [nsmul_eq_mul] using hsum
    _ ≤ (L + 1 : ℕ) * (n : ℝ) ^ (29 / 32 : ℝ) := by
      gcongr

private theorem smoothCoreS3_large_le {n L : ℕ} (hL : 0 < L) :
    (∑ i ∈ (Finset.range (Nat.log 2 n + 1)).filter (fun i ↦ ¬ 2 ^ i ≤ L),
        smoothCoreTerm n (2 ^ i)) ≤
      4 * (n : ℝ) / Real.sqrt (L : ℝ) := by
  classical
  let R := Nat.log 2 n + 1
  let k := Nat.log 2 L + 1
  let s := (Finset.range R).filter (fun i ↦ ¬ 2 ^ i ≤ L)
  have hsIco : s ⊆ Finset.Ico k R := by
    intro i hi
    have hiR : i < R := Finset.mem_range.mp (Finset.mem_filter.mp hi).1
    have hLi : L < 2 ^ i := Nat.lt_of_not_ge (Finset.mem_filter.mp hi).2
    have hi0 : i ≠ 0 := by
      intro hiZero
      subst i
      norm_num at hLi
      omega
    have hlogi : Nat.log 2 L < i := Nat.log_lt_of_lt_pow' hi0 hLi
    exact Finset.mem_Ico.mpr ⟨by simpa [k] using hlogi, hiR⟩
  have hlargeTerm : ∀ i ∈ s,
      smoothCoreTerm n (2 ^ i) ≤
        (n : ℝ) / Real.sqrt ((2 : ℕ) ^ i : ℝ) := by
    intro i hi
    simpa using smoothCoreTerm_le_large (n := n)
      (X := 2 ^ i) (pow_pos (by norm_num) i)
  have hnonneg : ∀ i ∈ Finset.Ico k R,
      i ∉ s → 0 ≤ (n : ℝ) / Real.sqrt ((2 : ℕ) ^ i : ℝ) := by
    intro i hi hnot
    positivity
  calc
    (∑ i ∈ (Finset.range (Nat.log 2 n + 1)).filter
        (fun i ↦ ¬ 2 ^ i ≤ L), smoothCoreTerm n (2 ^ i)) =
        ∑ i ∈ s, smoothCoreTerm n (2 ^ i) := by rfl
    _ ≤ ∑ i ∈ s, (n : ℝ) / Real.sqrt ((2 : ℕ) ^ i : ℝ) := by
      exact Finset.sum_le_sum hlargeTerm
    _ ≤ ∑ i ∈ Finset.Ico k R,
        (n : ℝ) / Real.sqrt ((2 : ℕ) ^ i : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsIco hnonneg
    _ = (n : ℝ) * ∑ j ∈ Finset.range (R - k),
        1 / Real.sqrt ((2 : ℝ) ^ (k + j)) := by
      rw [Finset.sum_Ico_eq_sum_range, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      norm_num [div_eq_mul_inv]
    _ ≤ (n : ℝ) * (4 / Real.sqrt ((2 : ℝ) ^ k)) := by
      exact mul_le_mul_of_nonneg_left (invSqrtDyadicTail_le k (R - k)) (by positivity)
    _ ≤ 4 * (n : ℝ) / Real.sqrt (L : ℝ) := by
      have hLpow : L < 2 ^ k := by
        simpa [k] using Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) L
      have hsqrt : Real.sqrt (L : ℝ) ≤ Real.sqrt ((2 : ℝ) ^ k) := by
        apply Real.sqrt_le_sqrt
        exact_mod_cast hLpow.le
      have hsqrtL : 0 < Real.sqrt (L : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hL)
      have hsqrtPow : 0 < Real.sqrt ((2 : ℝ) ^ k) := by positivity
      have hinv : 1 / Real.sqrt ((2 : ℝ) ^ k) ≤
          1 / Real.sqrt (L : ℝ) := by
        exact one_div_le_one_div_of_le hsqrtL hsqrt
      calc
        (n : ℝ) * (4 / Real.sqrt ((2 : ℝ) ^ k)) =
            (4 * (n : ℝ)) * (1 / Real.sqrt ((2 : ℝ) ^ k)) := by ring
        _ ≤ (4 * (n : ℝ)) * (1 / Real.sqrt (L : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hinv (by positivity)
        _ = 4 * (n : ℝ) / Real.sqrt (L : ℝ) := by ring

theorem smoothCoreS3_nonneg (n : ℕ) : 0 ≤ smoothCoreS3 n := by
  unfold smoothCoreS3
  exact Finset.sum_nonneg fun i hi ↦ smoothCoreTerm_nonneg n (2 ^ i)

/-- The exact finite cutoff estimate behind the asymptotic `S₃` bound. -/
theorem smoothCoreS3_le_cutoff {n L : ℕ} (hn : 0 < n) (hL : 0 < L)
    (hmoment : ∀ X : ℕ, 0 < X → X ≤ L →
      rankinMoment X ≤ (n : ℝ) ^ (1 / 16 : ℝ)) :
    smoothCoreS3 n ≤
      (L + 1 : ℕ) * (n : ℝ) ^ (29 / 32 : ℝ) +
        4 * (n : ℝ) / Real.sqrt (L : ℝ) := by
  classical
  rw [smoothCoreS3, ← Finset.sum_filter_add_sum_filter_not
    (Finset.range (Nat.log 2 n + 1)) (fun i ↦ 2 ^ i ≤ L)
    (fun i ↦ smoothCoreTerm n (2 ^ i))]
  exact add_le_add (smoothCoreS3_small_le hn hmoment)
    (smoothCoreS3_large_le hL)

private theorem eventually_log_fifth_le_threeThirtySeconds :
    ∀ᶠ n : ℕ in Filter.atTop,
      (Real.log (n : ℝ)) ^ (5 : ℝ) ≤
        (n : ℝ) ^ (3 / 32 : ℝ) := by
  have h := (isLittleO_log_rpow_rpow_atTop (5 : ℝ)
    (by norm_num : (0 : ℝ) < 3 / 32)).comp_tendsto
      (tendsto_natCast_atTop_atTop :
        Filter.Tendsto (fun n : ℕ ↦ (n : ℝ)) Filter.atTop Filter.atTop)
  filter_upwards [h.eventuallyLE, Filter.eventually_ge_atTop 1] with n hn hn1
  have hlog : 0 ≤ Real.log (n : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hn1)
  change ‖Real.log (n : ℝ) ^ (5 : ℝ)‖ ≤
    ‖(n : ℝ) ^ (3 / 32 : ℝ)‖ at hn
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hlog _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by positivity) _)] at hn
  exact hn

/-- Explicit eventual form of the reduced smooth-core estimate. -/
theorem eventually_smoothCoreS3_le :
    ∀ᶠ n : ℕ in Filter.atTop,
      smoothCoreS3 n ≤ 6 * ((n : ℝ) / Real.log (n : ℝ)) := by
  have hlogLarge := (Real.tendsto_log_atTop.comp
    tendsto_natCast_atTop_atTop).eventually_ge_atTop 2
  have hLpos := logFourthThreshold_tendsto_atTop.eventually_gt_atTop 0
  filter_upwards [eventually_rankinMoment_le_sixteenth,
    eventually_log_fifth_le_threeThirtySeconds, hlogLarge, hLpos,
    Filter.eventually_ge_atTop 1] with n hmoment hlogFifth hlogLarge hLpos hn1
  let t : ℝ := Real.log (n : ℝ)
  let L : ℕ := logFourthThreshold n
  have hn : 0 < n := by omega
  have ht : 0 < t := lt_of_lt_of_le (by norm_num) hlogLarge
  have htTwo : 2 ≤ t := by simpa [t] using hlogLarge
  have hL : 0 < L := by simpa [L] using hLpos
  have hLupper : (L : ℝ) ≤ t ^ 4 := by
    simpa [L, t, logFourthThreshold] using
      (Nat.floor_le (show 0 ≤ (Real.log (n : ℝ)) ^ 4 by positivity))
  have hLplus : (L + 1 : ℕ) ≤ (2 : ℝ) * t ^ 4 := by
    norm_num at ⊢
    have ht4one : 1 ≤ t ^ 4 := one_le_pow₀ (by linarith [htTwo])
    linarith
  have hfloorLow : t ^ 4 - 1 < (L : ℝ) := by
    simpa [L, t, logFourthThreshold] using
      (Nat.sub_one_lt_floor ((Real.log (n : ℝ)) ^ 4))
  have ht2Lower : t ^ 2 ≤ (L : ℝ) := by
    have hgap : 1 ≤ t ^ 4 - t ^ 2 := by
      nlinarith [sq_nonneg (t ^ 2 - 1), sq_nonneg (t - 2)]
    linarith
  have hsqrtLower : t ≤ Real.sqrt (L : ℝ) := by
    calc
      t = Real.sqrt (t ^ 2) := by
        rw [Real.sqrt_sq_eq_abs, abs_of_pos ht]
      _ ≤ Real.sqrt (L : ℝ) := Real.sqrt_le_sqrt ht2Lower
  have hlogPow : t ^ (5 : ℕ) ≤ (n : ℝ) ^ (3 / 32 : ℝ) := by
    simpa [t, Real.rpow_natCast] using hlogFifth
  have hsmall :
      (L + 1 : ℕ) * (n : ℝ) ^ (29 / 32 : ℝ) ≤
        2 * ((n : ℝ) / t) := by
    rw [show 2 * ((n : ℝ) / t) = (2 * (n : ℝ)) / t by ring,
      le_div_iff₀ ht]
    calc
      ((L + 1 : ℕ) : ℝ) * (n : ℝ) ^ (29 / 32 : ℝ) * t ≤
          (2 * t ^ 4) * (n : ℝ) ^ (29 / 32 : ℝ) * t := by
        gcongr
      _ = 2 * t ^ 5 * (n : ℝ) ^ (29 / 32 : ℝ) := by ring
      _ ≤ 2 * (n : ℝ) ^ (3 / 32 : ℝ) *
          (n : ℝ) ^ (29 / 32 : ℝ) := by
        gcongr
      _ = 2 * (n : ℝ) := by
        calc
          2 * (n : ℝ) ^ (3 / 32 : ℝ) * (n : ℝ) ^ (29 / 32 : ℝ) =
              2 * ((n : ℝ) ^ (3 / 32 : ℝ) *
                (n : ℝ) ^ (29 / 32 : ℝ)) := by ring
          _ = 2 * (n : ℝ) ^ ((3 / 32 : ℝ) + 29 / 32) := by
            rw [Real.rpow_add (by exact_mod_cast hn)]
          _ = 2 * (n : ℝ) := by norm_num [Real.rpow_one]
  have hlarge : 4 * (n : ℝ) / Real.sqrt (L : ℝ) ≤
      4 * ((n : ℝ) / t) := by
    have hinv : 1 / Real.sqrt (L : ℝ) ≤ 1 / t :=
      one_div_le_one_div_of_le ht hsqrtLower
    calc
      4 * (n : ℝ) / Real.sqrt (L : ℝ) =
          (4 * (n : ℝ)) * (1 / Real.sqrt (L : ℝ)) := by ring
      _ ≤ (4 * (n : ℝ)) * (1 / t) := by
        exact mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = 4 * ((n : ℝ) / t) := by ring
  calc
    smoothCoreS3 n ≤
        (L + 1 : ℕ) * (n : ℝ) ^ (29 / 32 : ℝ) +
          4 * (n : ℝ) / Real.sqrt (L : ℝ) :=
      smoothCoreS3_le_cutoff hn hL (by
        intro X hX hXL
        exact hmoment X hX (by simpa [L] using hXL))
    _ ≤ 2 * ((n : ℝ) / t) + 4 * ((n : ℝ) / t) := add_le_add hsmall hlarge
    _ = 6 * ((n : ℝ) / Real.log (n : ℝ)) := by simp [t]; ring

/-- The complete reduced `S₃` estimate in the asymptotic form consumed by
the upper-bound assembly. -/
theorem smoothCoreS3_isBigO :
    smoothCoreS3 =O[Filter.atTop]
      (fun n : ℕ ↦ (n : ℝ) / Real.log (n : ℝ)) := by
  apply Asymptotics.IsBigO.of_bound 6
  have hlogPos := (Real.tendsto_log_atTop.comp
    tendsto_natCast_atTop_atTop).eventually_gt_atTop 0
  filter_upwards [eventually_smoothCoreS3_le, hlogPos] with n hn hlog
  rw [Real.norm_of_nonneg (smoothCoreS3_nonneg n)]
  have hscale : 0 ≤ (n : ℝ) / Real.log (n : ℝ) :=
    div_nonneg (by positivity) (by simpa using hlog.le)
  rw [Real.norm_of_nonneg hscale]
  exact hn

end Erdos888
