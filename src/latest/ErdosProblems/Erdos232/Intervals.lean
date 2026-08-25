import ErdosProblems.Erdos232.GridLookup

open LeanCert.Core
open Filter MeasureTheory Metric intervalIntegral
open scoped ENNReal Topology Interval

namespace Erdos232

def intervalSub (I J : IntervalRat) : IntervalRat :=
  IntervalRat.add I (IntervalRat.scale (-1) J)

theorem IntervalRat.mem_sub {x y : ℝ} {I J : IntervalRat}
    (hx : x ∈ I) (hy : y ∈ J) : x - y ∈ intervalSub I J := by
  have h := IntervalRat.mem_add hx (IntervalRat.mem_scale (-1 : ℚ) hy)
  simpa only [intervalSub, Rat.cast_neg, Rat.cast_one, neg_one_mul, sub_eq_add_neg] using h

def intervalPow (I : IntervalRat) : ℕ → IntervalRat
  | 0 => IntervalRat.singleton 1
  | n + 1 => IntervalRat.mul (intervalPow I n) I

theorem IntervalRat.mem_pow {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    ∀ n : ℕ, x ^ n ∈ intervalPow I n
  | 0 => by simpa [intervalPow] using IntervalRat.mem_singleton 1
  | n + 1 => by
      rw [pow_succ]
      exact IntervalRat.mem_mul (IntervalRat.mem_pow hx n) hx

def intervalTaylorSum (C : ℕ → IntervalRat) (H : IntervalRat) : ℕ → IntervalRat
  | 0 => IntervalRat.singleton 0
  | n + 1 => IntervalRat.add (intervalTaylorSum C H n)
      (IntervalRat.scale (1 / n.factorial) (IntervalRat.mul (C n) (intervalPow H n)))

theorem mem_intervalTaylorSum {c : ℕ → ℝ} {h : ℝ}
    {C : ℕ → IntervalRat} {H : IntervalRat}
    (hc : ∀ k, c k ∈ C k) (hh : h ∈ H) : ∀ n : ℕ,
    (∑ k ∈ Finset.range n, c k * h ^ k / k.factorial) ∈ intervalTaylorSum C H n
  | 0 => by simpa [intervalTaylorSum] using IntervalRat.mem_singleton 0
  | n + 1 => by
      rw [Finset.sum_range_succ, intervalTaylorSum]
      have hterm := IntervalRat.mem_scale (1 / n.factorial : ℚ)
        (IntervalRat.mem_mul (hc n) (IntervalRat.mem_pow hh n))
      convert IntervalRat.mem_add (mem_intervalTaylorSum hc hh n) hterm using 1 <;> push_cast <;> ring

def intervalMaxAbs (I : IntervalRat) : ℚ := max |I.lo| |I.hi|

theorem abs_le_intervalMaxAbs {x : ℝ} {I : IntervalRat} (hx : x ∈ I) :
    |x| ≤ (intervalMaxAbs I : ℝ) := by
  rw [abs_le]
  simp only [intervalMaxAbs, Rat.cast_max, Rat.cast_abs]
  constructor
  · have h := neg_abs_le (I.lo : ℝ)
    have hm : (|I.lo| : ℝ) ≤ max (|I.lo| : ℝ) |(I.hi : ℝ)| := le_max_left _ _
    linarith [hx.1]
  · have h := le_abs_self (I.hi : ℝ)
    have hm : |(I.hi : ℝ)| ≤ max (|I.lo| : ℝ) |I.hi| := le_max_right _ _
    linarith [hx.2]

def besselGridDerivativeInterval (i : Fin 367) (r : ℕ) : IntervalRat :=
  if i.val = 0 then IntervalRat.singleton (besselInitial r)
  else linearInterval (besselCoefficients (i.val * 157 / 50) r).1
    (besselCoefficients (i.val * 157 / 50) r).2 (besselGridStateAt i)

theorem mem_besselGridDerivativeInterval (i : Fin 367) (r : ℕ) :
    besselDerivative r (((i.val : ℚ) * 157 / 50 : ℚ) : ℝ) ∈
      besselGridDerivativeInterval i r := by
  by_cases hi : i.val = 0
  · have hieq : i = 0 := Fin.ext hi
    subst i
    simpa [besselGridDerivativeInterval, besselDerivative_zero_eq_initial] using
      IntervalRat.mem_singleton (besselInitial r)
  · have hq : ((i.val : ℚ) * 157 / 50 : ℚ) ≠ 0 := by
      positivity
    rw [besselDerivative_eq_coefficients _ hq]
    simpa [besselGridDerivativeInterval, hi] using
      mem_linearInterval (besselGridStateAt_valid i).1 (besselGridStateAt_valid i).2

def besselOnInterval (i : Fin 367) (r n : ℕ) (Y : IntervalRat) : IntervalRat :=
  let q : ℚ := i.val * 157 / 50
  let H := intervalSub Y (IntervalRat.singleton q)
  let P := intervalTaylorSum (fun k => besselGridDerivativeInterval i (r + k)) H (n + 1)
  widenInterval (intervalMaxAbs H ^ (n + 1) / (n + 1).factorial) P

theorem mem_besselOnInterval (i : Fin 367) (r n : ℕ) (Y : IntervalRat)
    {y : ℝ} (hy : y ∈ Y) : besselDerivative r y ∈ besselOnInterval i r n Y := by
  let q : ℚ := i.val * 157 / 50
  let H := intervalSub Y (IntervalRat.singleton q)
  have hq : ((q : ℚ) : ℝ) ∈ IntervalRat.singleton q := IntervalRat.mem_singleton q
  have hh : y - (q : ℝ) ∈ H := IntervalRat.mem_sub hy hq
  have hp : besselTaylor r n (q : ℝ) y ∈
      intervalTaylorSum (fun k => besselGridDerivativeInterval i (r + k)) H (n + 1) := by
    unfold besselTaylor
    exact mem_intervalTaylorSum (fun k => mem_besselGridDerivativeInterval i (r + k)) hh (n + 1)
  apply mem_widenInterval hp
  have hb := besselTaylor_bound r n (q : ℝ) y
  have hm := abs_le_intervalMaxAbs hh
  have hnonnegQ : 0 ≤ intervalMaxAbs H :=
    (abs_nonneg H.lo).trans (le_max_left _ _)
  have hnonneg : 0 ≤ (intervalMaxAbs H : ℝ) := Rat.cast_nonneg.mpr hnonnegQ
  have hpow : |y - (q : ℝ)| ^ (n + 1) ≤ (intervalMaxAbs H : ℝ) ^ (n + 1) :=
    (pow_le_pow_left₀ (abs_nonneg _) hm) (n + 1)
  have he : |besselDerivative r y - besselTaylor r n (q : ℝ) y| ≤
      ((intervalMaxAbs H ^ (n + 1) / (n + 1).factorial : ℚ) : ℝ) := by
    push_cast
    exact hb.trans (div_le_div_of_nonneg_right hpow (Nat.cast_nonneg _))
  change |besselDerivative r y - besselTaylor r n (q : ℝ) y| ≤
    |((intervalMaxAbs H ^ (n + 1) / (n + 1).factorial : ℚ) : ℝ)|
  have herrQ : 0 ≤ intervalMaxAbs H ^ (n + 1) / ((n + 1).factorial : ℚ) :=
    div_nonneg (pow_nonneg hnonnegQ _) (by positivity)
  have herrAbs : |((intervalMaxAbs H ^ (n + 1) / (n + 1).factorial : ℚ) : ℝ)| =
      ((intervalMaxAbs H ^ (n + 1) / (n + 1).factorial : ℚ) : ℝ) :=
    abs_of_nonneg (Rat.cast_nonneg.mpr herrQ)
  rw [herrAbs]
  exact he

def intervalFinSum : (n : ℕ) → (Fin n → IntervalRat) → IntervalRat
  | 0, _ => IntervalRat.singleton 0
  | n + 1, F => IntervalRat.add
      (intervalFinSum n (fun i => F i.castSucc)) (F (Fin.last n))

theorem mem_intervalFinSum {n : ℕ} {x : Fin n → ℝ} {F : Fin n → IntervalRat}
    (hx : ∀ i, x i ∈ F i) : (∑ i, x i) ∈ intervalFinSum n F := by
  induction n with
  | zero => simpa [intervalFinSum] using IntervalRat.mem_singleton 0
  | succ n ih =>
      rw [Fin.sum_univ_castSucc]
      exact IntervalRat.mem_add (ih (fun i => hx i.castSucc)) (hx (Fin.last n))

def combinedDerivativeInterval {n : ℕ}
    (weight : Fin n → ℚ) (distance : Fin n → IntervalRat)
    (grid : Fin n → Fin 367) (m : ℚ) (r evalDegree : ℕ) : IntervalRat :=
  intervalFinSum n fun j =>
    IntervalRat.scale (weight j) <| IntervalRat.mul (intervalPow (distance j) r) <|
      besselOnInterval (grid j) r evalDegree (IntervalRat.scale m (distance j))

theorem mem_combinedDerivativeInterval {n : ℕ}
    (weight : Fin n → ℚ) (distance : Fin n → IntervalRat)
    (grid : Fin n → Fin 367) (m : ℚ) (r evalDegree : ℕ)
    (d : Fin n → ℝ) (hd : ∀ j, d j ∈ distance j) :
    (∑ j, (weight j : ℝ) * d j ^ r * besselDerivative r ((m : ℝ) * d j)) ∈
      combinedDerivativeInterval weight distance grid m r evalDegree := by
  apply mem_intervalFinSum
  intro j
  have hpow := IntervalRat.mem_pow (hd j) r
  have harg := IntervalRat.mem_scale m (hd j)
  have hb := mem_besselOnInterval (grid j) r evalDegree _ harg
  convert IntervalRat.mem_scale (weight j) (IntervalRat.mem_mul hpow hb) using 1 <;> ring

noncomputable def spectralSum {n : ℕ} (weight : Fin n → ℚ) (d : Fin n → ℝ)
    (t : ℝ) : ℝ :=
  ∑ j, (weight j : ℝ) * besselJ0 (t * d j)

noncomputable def spectralTaylorValue {n : ℕ} (weight : Fin n → ℚ)
    (d : Fin n → ℝ) (m : ℝ) (degree : ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (degree + 1),
    (∑ j, (weight j : ℝ) * d j ^ k * besselDerivative k (m * d j)) *
      (t - m) ^ k / k.factorial

def combinedRemainderConstant {n : ℕ} (weight : Fin n → ℚ)
    (distance : Fin n → IntervalRat) (degree : ℕ) : ℚ :=
  ∑ j, |weight j| * intervalMaxAbs (distance j) ^ (degree + 1)

theorem spectralTaylor_bound {n : ℕ} (weight : Fin n → ℚ)
    (distance : Fin n → IntervalRat) (d : Fin n → ℝ)
    (hd : ∀ j, d j ∈ distance j) (m t : ℝ) (degree : ℕ) :
    |spectralSum weight d t - spectralTaylorValue weight d m degree t| ≤
      (combinedRemainderConstant weight distance degree : ℝ) *
        |t - m| ^ (degree + 1) / (degree + 1).factorial := by
  have hrewrite : spectralTaylorValue weight d m degree t =
      ∑ j, (weight j : ℝ) * besselTaylor 0 degree (m * d j) (t * d j) := by
    rw [spectralTaylorValue]
    simp_rw [Finset.sum_mul, Finset.sum_div]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [besselTaylor, Finset.mul_sum]
    simp only [zero_add]
    apply Finset.sum_congr rfl
    intro k _
    rw [show t * d j - m * d j = d j * (t - m) by ring, mul_pow]
    ring
  rw [spectralSum, hrewrite]
  have hsum := Finset.abs_sum_le_sum_abs
    (fun j : Fin n => (weight j : ℝ) *
      (besselJ0 (t * d j) - besselTaylor 0 degree (m * d j) (t * d j))) Finset.univ
  have heq :
      (∑ j, (weight j : ℝ) * besselJ0 (t * d j)) -
        ∑ j, (weight j : ℝ) * besselTaylor 0 degree (m * d j) (t * d j) =
      ∑ j, (weight j : ℝ) *
        (besselJ0 (t * d j) - besselTaylor 0 degree (m * d j) (t * d j)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [heq]
  have hterms (j : Fin n) :
      |(weight j : ℝ) *
        (besselJ0 (t * d j) - besselTaylor 0 degree (m * d j) (t * d j))| ≤
        ((|weight j| * intervalMaxAbs (distance j) ^ (degree + 1) : ℚ) : ℝ) *
          |t - m| ^ (degree + 1) / (degree + 1).factorial := by
    rw [abs_mul, besselJ0]
    have hb := besselTaylor_bound 0 degree (m * d j) (t * d j)
    have hdabs := abs_le_intervalMaxAbs (hd j)
    have hpowd := (pow_le_pow_left₀ (abs_nonneg _) hdabs) (degree + 1)
    have hoff : |t * d j - m * d j| = |d j| * |t - m| := by
      rw [show t * d j - m * d j = d j * (t - m) by ring, abs_mul, mul_comm]
    rw [hoff, mul_pow] at hb
    have hfac : 0 ≤ ((degree + 1).factorial : ℝ) := Nat.cast_nonneg _
    calc
      |(weight j : ℝ)| *
          |besselDerivative 0 (t * d j) - besselTaylor 0 degree (m * d j) (t * d j)|
          ≤ |(weight j : ℝ)| *
              ((|d j| ^ (degree + 1) * |t - m| ^ (degree + 1)) /
                (degree + 1).factorial) := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ ≤ |(weight j : ℝ)| *
              (((intervalMaxAbs (distance j) : ℝ) ^ (degree + 1) *
                |t - m| ^ (degree + 1)) / (degree + 1).factorial) := by
            gcongr
      _ = ((|weight j| * intervalMaxAbs (distance j) ^ (degree + 1) : ℚ) : ℝ) *
            |t - m| ^ (degree + 1) / (degree + 1).factorial := by push_cast; ring
  calc
    |∑ j, (weight j : ℝ) *
        (besselJ0 (t * d j) - besselTaylor 0 degree (m * d j) (t * d j))|
        ≤ ∑ j, |(weight j : ℝ) *
          (besselJ0 (t * d j) - besselTaylor 0 degree (m * d j) (t * d j))| := hsum
    _ ≤ ∑ j, ((|weight j| * intervalMaxAbs (distance j) ^ (degree + 1) : ℚ) : ℝ) *
          |t - m| ^ (degree + 1) / (degree + 1).factorial :=
      Finset.sum_le_sum fun j _ => hterms j
    _ = (combinedRemainderConstant weight distance degree : ℝ) *
          |t - m| ^ (degree + 1) / (degree + 1).factorial := by
      rw [combinedRemainderConstant]
      push_cast
      rw [Finset.sum_mul, Finset.sum_div]

theorem combinedRemainderConstant_nonneg {n : ℕ} (weight : Fin n → ℚ)
    (distance : Fin n → IntervalRat) (degree : ℕ) :
    0 ≤ combinedRemainderConstant weight distance degree := by
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (abs_nonneg _) (pow_nonneg
    ((abs_nonneg (distance j).lo).trans (le_max_left _ _)) _)

def dualOnInterval {n : ℕ} (constant : ℚ) (weight : Fin n → ℚ)
    (distance : Fin n → IntervalRat) (grid : Fin n → Fin 367)
    (m : ℚ) (degree evalDegree : ℕ) (T : IntervalRat) : IntervalRat :=
  let H := intervalSub T (IntervalRat.singleton m)
  let P := IntervalRat.add (IntervalRat.singleton constant) <|
    intervalTaylorSum
      (fun k => combinedDerivativeInterval weight distance grid m k evalDegree) H (degree + 1)
  widenInterval
    (combinedRemainderConstant weight distance degree *
      intervalMaxAbs H ^ (degree + 1) / (degree + 1).factorial) P

theorem mem_dualOnInterval {n : ℕ} (constant : ℚ) (weight : Fin n → ℚ)
    (distance : Fin n → IntervalRat) (grid : Fin n → Fin 367)
    (m : ℚ) (degree evalDegree : ℕ) (T : IntervalRat)
    (d : Fin n → ℝ) (hd : ∀ j, d j ∈ distance j)
    {t : ℝ} (ht : t ∈ T) :
    (constant : ℝ) + spectralSum weight d t ∈
      dualOnInterval constant weight distance grid m degree evalDegree T := by
  let H := intervalSub T (IntervalRat.singleton m)
  have hm : (m : ℝ) ∈ IntervalRat.singleton m := IntervalRat.mem_singleton m
  have hh : t - (m : ℝ) ∈ H := IntervalRat.mem_sub ht hm
  have hcoeff (k : ℕ) := mem_combinedDerivativeInterval weight distance grid m k evalDegree d hd
  have hpoly0 := mem_intervalTaylorSum hcoeff hh (degree + 1)
  have hpoly : (constant : ℝ) + spectralTaylorValue weight d m degree t ∈
      IntervalRat.add (IntervalRat.singleton constant)
        (intervalTaylorSum
          (fun k => combinedDerivativeInterval weight distance grid m k evalDegree) H
          (degree + 1)) := by
    apply IntervalRat.mem_add (IntervalRat.mem_singleton constant)
    simpa [spectralTaylorValue] using hpoly0
  apply mem_widenInterval hpoly
  have hb := spectralTaylor_bound weight distance d hd (m : ℝ) t degree
  have hmabs := abs_le_intervalMaxAbs hh
  have hpow := (pow_le_pow_left₀ (abs_nonneg _) hmabs) (degree + 1)
  have hC : 0 ≤ (combinedRemainderConstant weight distance degree : ℝ) := by
    exact Rat.cast_nonneg.mpr (combinedRemainderConstant_nonneg weight distance degree)
  have hfac : 0 ≤ ((degree + 1).factorial : ℝ) := Nat.cast_nonneg _
  have he : |((constant : ℝ) + spectralSum weight d t) -
      ((constant : ℝ) + spectralTaylorValue weight d m degree t)| ≤
      ((combinedRemainderConstant weight distance degree *
        intervalMaxAbs H ^ (degree + 1) / (degree + 1).factorial : ℚ) : ℝ) := by
    rw [add_sub_add_left_eq_sub]
    push_cast
    exact hb.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow hC) hfac)
  change |((constant : ℝ) + spectralSum weight d t) -
      ((constant : ℝ) + spectralTaylorValue weight d m degree t)| ≤
    |((combinedRemainderConstant weight distance degree *
      intervalMaxAbs H ^ (degree + 1) / (degree + 1).factorial : ℚ) : ℝ)|
  have herrQ : 0 ≤ combinedRemainderConstant weight distance degree *
      intervalMaxAbs H ^ (degree + 1) / ((degree + 1).factorial : ℚ) := by
    unfold combinedRemainderConstant intervalMaxAbs
    positivity
  have herrAbs : |((combinedRemainderConstant weight distance degree *
      intervalMaxAbs H ^ (degree + 1) / (degree + 1).factorial : ℚ) : ℝ)| =
      ((combinedRemainderConstant weight distance degree *
        intervalMaxAbs H ^ (degree + 1) / (degree + 1).factorial : ℚ) : ℝ) :=
    abs_of_nonneg (Rat.cast_nonneg.mpr herrQ)
  rw [herrAbs]
  exact he

end Erdos232
